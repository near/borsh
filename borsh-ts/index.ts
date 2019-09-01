import BN from 'bn.js';

const INITIAL_LENGTH = 1024;

export type Schema = Map<Function, any>;

/// Binary encoder.
export class BinaryWriter {
    buf: Buffer;
    length: number;

    public constructor() {
        this.buf = Buffer.alloc(INITIAL_LENGTH);
        this.length = 0;
    }

    maybe_resize() {
        if (this.buf.length < 16 + this.length) {
            this.buf = Buffer.concat([this.buf, Buffer.alloc(INITIAL_LENGTH)]);
        }
    }

    public write_u8(value: number) {
        this.maybe_resize();
        this.buf.writeUInt8(value, this.length);
        this.length += 1;
    }

    public write_u32(value: number) {
        this.maybe_resize();
        this.buf.writeUInt32LE(value, this.length);
        this.length += 4;
    }

    public write_u64(value: BN) {
        this.maybe_resize();
        this.write_buffer(Buffer.from(new BN(value).toArray('le', 8)));
    }

    public write_u128(value: BN) {
        this.maybe_resize();
        this.write_buffer(Buffer.from(new BN(value).toArray('le', 16)));
    }

    private write_buffer(buffer: Buffer) {
        // Buffer.from is needed as this.buf.subarray can return plain Uint8Array in browser
        this.buf = Buffer.concat([Buffer.from(this.buf.subarray(0, this.length)), buffer, Buffer.alloc(INITIAL_LENGTH)]);
        this.length += buffer.length;
    }

    public write_string(str: string) {
        this.maybe_resize();
        const b = Buffer.from(str, 'utf8');
        this.write_u32(b.length);
        this.write_buffer(b);
    }

    public write_fixed_array(array: Uint8Array) {
        this.write_buffer(Buffer.from(array));
    }

    public write_array(array: any[], fn: any) {
        this.maybe_resize();
        this.write_u32(array.length);
        for (const elem of array) {
            this.maybe_resize();
            fn(elem);
        }
    }

    public toArray(): Uint8Array {
        return this.buf.subarray(0, this.length);
    }
}

export class BinaryReader {
    buf: Buffer;
    offset: number;

    public constructor(buf: Buffer) {
        this.buf = buf;
        this.offset = 0;
    }

    read_u8(): number {
        const value = this.buf.readUInt8(this.offset);
        this.offset += 1;
        return value;
    }

    read_u32(): number {
        const value = this.buf.readUInt32LE(this.offset);
        this.offset += 4;
        return value;
    }

    read_u64(): BN {
        const buf = this.read_buffer(8);
        buf.reverse();
        return new BN(`${buf.toString('hex')}`, 16);
    }

    read_u128(): BN {
        const buf = this.read_buffer(16);
        return new BN(buf);
    }

    private read_buffer(len: number): Buffer {
        const result = this.buf.slice(this.offset, this.offset + len);
        this.offset += len;
        return result;
    }

    read_string(): string {
        const len = this.read_u32();
        return this.read_buffer(len).toString('utf8');
    }

    read_fixed_array(len: number): Uint8Array {
        return new Uint8Array(this.read_buffer(len));
    }

    read_array(fn: any): any[] {
        const len = this.read_u32();
        const result = Array<any>();
        for (let i = 0; i < len; ++i) {
            result.push(fn());
        }
        return result;
    }
}

function serializeField(schema: Schema, value: any, fieldType: any, writer: any) {
    if (typeof fieldType === 'string') {
        writer[`write_${fieldType}`](value);
    } else if (fieldType instanceof Array) {
        if (typeof fieldType[0] === 'number') {
            writer.write_fixed_array(value);
        } else {
            writer.write_array(value, (item: any) => { serializeField(schema, item, fieldType[0], writer); });
        }
    } else if (fieldType.kind !== undefined) {
        switch (fieldType.kind) {
            case 'option': {
                if (value === null) {
                    writer.write_u8(0);
                } else {
                    writer.write_u8(1);
                    serializeField(schema, value, fieldType.type, writer);
                }
                break;
            }
            default: throw new Error(`FieldType ${fieldType} unrecognized`);
        }
    } else {
        serializeStruct(schema, value, writer);
    }
}

function serializeStruct(schema: Schema, obj: any, writer: any) {
    const structSchema = schema.get(obj.constructor);
    if (!structSchema) {
        throw new Error(`Class ${obj.constructor.name} is missing in schema`);
    }
    if (structSchema.kind === 'struct') {
        structSchema.fields.map(([fieldName, fieldType]: [any, any]) => {
            serializeField(schema, obj[fieldName], fieldType, writer);
        });
    } else if (structSchema.kind === 'enum') {
        const name = obj[structSchema.field];
        for (let idx = 0; idx < structSchema.values.length; ++idx) {
            const [fieldName, fieldType]: [any, any] = structSchema.values[idx];
            if (fieldName === name) {
                writer.write_u8(idx);
                serializeField(schema, obj[fieldName], fieldType, writer);
                break;
            }
        }
    } else {
        throw new Error(`Unexpected schema kind: ${structSchema.kind} for ${obj.constructor.name}`);
    }
}

/// Serialize given object using schema of the form:
/// { class_name -> [ [field_name, field_type], .. ], .. }
export function serialize(schema: Schema, obj: any): Uint8Array {
    const writer = new BinaryWriter();
    serializeStruct(schema, obj, writer);
    return writer.toArray();
}

function deserializeField(schema: Schema, fieldType: any, reader: any): any {
    if (typeof fieldType === 'string') {
        return reader[`read_${fieldType}`]();
    } else if (fieldType instanceof Array) {
        if (typeof fieldType[0] === 'number') {
            return reader.read_fixed_array(fieldType[0]);
        } else {
            return reader.read_array(() => deserializeField(schema, fieldType[0], reader));
        }
    } else {
        return deserializeStruct(schema, fieldType, reader);
    }
}

function deserializeStruct(schema: Schema, classType: any, reader: any) {
    const fields = schema.get(classType).fields.map(([fieldName, fieldType]: [any, any]) => {
        return deserializeField(schema, fieldType, reader);
    });
    return new classType(...fields);
}

/// Deserializes object from bytes using schema.
export function deserialize(schema: Schema, classType: any, buffer: Buffer): any {
    const reader = new BinaryReader(buffer);
    return deserializeStruct(schema, classType, reader);
}
