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

    maybeResize() {
        if (this.buf.length < 16 + this.length) {
            this.buf = Buffer.concat([this.buf, Buffer.alloc(INITIAL_LENGTH)]);
        }
    }

    public writeU8(value: number) {
        this.maybeResize();
        this.buf.writeUInt8(value, this.length);
        this.length += 1;
    }

    public writeU32(value: number) {
        this.maybeResize();
        this.buf.writeUInt32LE(value, this.length);
        this.length += 4;
    }

    public writeU64(value: BN) {
        this.maybeResize();
        this.writeBuffer(Buffer.from(new BN(value).toArray('le', 8)));
    }

    public writeU128(value: BN) {
        this.maybeResize();
        this.writeBuffer(Buffer.from(new BN(value).toArray('le', 16)));
    }

    private writeBuffer(buffer: Buffer) {
        // Buffer.from is needed as this.buf.subarray can return plain Uint8Array in browser
        this.buf = Buffer.concat([Buffer.from(this.buf.subarray(0, this.length)), buffer, Buffer.alloc(INITIAL_LENGTH)]);
        this.length += buffer.length;
    }

    public writeString(str: string) {
        this.maybeResize();
        const b = Buffer.from(str, 'utf8');
        this.writeU32(b.length);
        this.writeBuffer(b);
    }

    public writeFixedArray(array: Uint8Array) {
        this.writeBuffer(Buffer.from(array));
    }

    public writeArray(array: any[], fn: any) {
        this.maybeResize();
        this.writeU32(array.length);
        for (const elem of array) {
            this.maybeResize();
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

    readU8(): number {
        const value = this.buf.readUInt8(this.offset);
        this.offset += 1;
        return value;
    }

    readU32(): number {
        const value = this.buf.readUInt32LE(this.offset);
        this.offset += 4;
        return value;
    }

    readU64(): BN {
        const buf = this.readBuffer(8);
        buf.reverse();
        return new BN(`${buf.toString('hex')}`, 16);
    }

    readU128(): BN {
        const buf = this.readBuffer(16);
        return new BN(buf);
    }

    private readBuffer(len: number): Buffer {
        const result = this.buf.slice(this.offset, this.offset + len);
        this.offset += len;
        return result;
    }

    readString(): string {
        const len = this.readU32();
        return this.readBuffer(len).toString('utf8');
    }

    readFixedArray(len: number): Uint8Array {
        return new Uint8Array(this.readBuffer(len));
    }

    readArray(fn: any): any[] {
        const len = this.readU32();
        const result = Array<any>();
        for (let i = 0; i < len; ++i) {
            result.push(fn());
        }
        return result;
    }
}

function serializeField(schema: Schema, value: any, fieldType: any, writer: any) {
    if (typeof fieldType === 'string') {
        writer[`write${fieldType}`](value);
    } else if (fieldType instanceof Array) {
        if (typeof fieldType[0] === 'number') {
            writer.writeFixedArray(value);
        } else {
            writer.writeArray(value, (item: any) => { serializeField(schema, item, fieldType[0], writer); });
        }
    } else if (fieldType.kind !== undefined) {
        switch (fieldType.kind) {
            case 'option': {
                if (value === null) {
                    writer.writeU8(0);
                } else {
                    writer.writeU8(1);
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
                writer.writeU8(idx);
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
        return reader[`read${fieldType}`]();
    } else if (fieldType instanceof Array) {
        if (typeof fieldType[0] === 'number') {
            return reader.readFixedArray(fieldType[0]);
        } else {
            return reader.readArray(() => deserializeField(schema, fieldType[0], reader));
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
