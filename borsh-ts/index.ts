import BN from 'bn.js';

// TODO: Make sure this polyfill not included when not required
import * as encoding from 'text-encoding-utf-8';
const TextDecoder = (typeof (global as any).TextDecoder !== 'function') ? encoding.TextDecoder : (global as any).TextDecoder;
const textDecoder = new TextDecoder('utf-8', { fatal: true });

const INITIAL_LENGTH = 1024;

export type Schema = Map<Function, any>;

export class BorshError extends Error {
    originalMessage: string;
    fieldPath: string[] = [];

    constructor(message: string) {
        super(message);
        this.originalMessage = message;
    }

    addToFieldPath(fieldName: string) {
        this.fieldPath.splice(0, 0, fieldName);
        // NOTE: Modifying message directly as jest doesn't use .toString()
        this.message = this.originalMessage + ': ' + this.fieldPath.join('.');
    }
}

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

function handlingRangeError(target: any, propertyKey: string, propertyDescriptor: PropertyDescriptor) {
    const originalMethod = propertyDescriptor.value;
    propertyDescriptor.value = function (...args: any[]) {
        try {
            return originalMethod.apply(this, args);
        } catch (e) {
            if (e instanceof RangeError) {
                const code = (e as any).code;
                if (['ERR_BUFFER_OUT_OF_BOUNDS', 'ERR_OUT_OF_RANGE'].indexOf(code) >= 0) {
                    throw new BorshError('Reached the end of buffer when deserializing');
                }
            }
            throw e;
        }
    };
}

export class BinaryReader {
    buf: Buffer;
    offset: number;

    public constructor(buf: Buffer) {
        this.buf = buf;
        this.offset = 0;
    }

    @handlingRangeError
    readU8(): number {
        const value = this.buf.readUInt8(this.offset);
        this.offset += 1;
        return value;
    }

    @handlingRangeError
    readU32(): number {
        const value = this.buf.readUInt32LE(this.offset);
        this.offset += 4;
        return value;
    }

    @handlingRangeError
    readU64(): BN {
        const buf = this.readBuffer(8);
        return new BN(buf, 'le');
    }

    @handlingRangeError
    readU128(): BN {
        const buf = this.readBuffer(16);
        return new BN(buf, 'le');
    }

    private readBuffer(len: number): Buffer {
        if ((this.offset + len) > this.buf.length) {
            throw new BorshError(`Expected buffer length ${len} isn't within bounds`);
        }
        const result = this.buf.slice(this.offset, this.offset + len);
        this.offset += len;
        return result;
    }

    @handlingRangeError
    readString(): string {
        const len = this.readU32();
        const buf = this.readBuffer(len);
        try {
            // NOTE: Using TextDecoder to fail on invalid UTF-8
            return textDecoder.decode(buf);
        } catch (e) {
            throw new BorshError(`Error decoding UTF-8 string: ${e}`);
        }
    }

    @handlingRangeError
    readFixedArray(len: number): Uint8Array {
        return new Uint8Array(this.readBuffer(len));
    }

    @handlingRangeError
    readArray(fn: any): any[] {
        const len = this.readU32();
        const result = Array<any>();
        for (let i = 0; i < len; ++i) {
            result.push(fn());
        }
        return result;
    }
}

function capitalizeFirstLetter(string) {
    return string.charAt(0).toUpperCase() + string.slice(1);
}

function serializeField(schema: Schema, fieldName: string, value: any, fieldType: any, writer: any) {
    try {
        // TODO: Handle missing values properly (make sure they never result in just skipped write)
        if (typeof fieldType === 'string') {
            writer[`write${capitalizeFirstLetter(fieldType)}`](value);

        } else if (fieldType instanceof Array) {
            if (typeof fieldType[0] === 'number') {
                if (value.length !== fieldType[0]) {
                    throw new BorshError(`Expecting byte array of length ${fieldType[0]}, but got ${value.length} bytes`);
                }
                writer.writeFixedArray(value);
            } else {
                writer.writeArray(value, (item: any) => { serializeField(schema, fieldName, item, fieldType[0], writer); });
            }
        } else if (fieldType.kind !== undefined) {
            switch (fieldType.kind) {
                case 'option': {
                    if (value === null) {
                        writer.writeU8(0);
                    } else {
                        writer.writeU8(1);
                        serializeField(schema, fieldName, value, fieldType.type, writer);
                    }
                    break;
                }
                default: throw new BorshError(`FieldType ${fieldType} unrecognized`);
            }
        } else {
            serializeStruct(schema, value, writer);
        }
    } catch (error) {
        if (error instanceof BorshError) {
            error.addToFieldPath(fieldName);
        }
        throw error;
    }
}

function serializeStruct(schema: Schema, obj: any, writer: any) {
    const structSchema = schema.get(obj.constructor);
    if (!structSchema) {
        throw new BorshError(`Class ${obj.constructor.name} is missing in schema`);
    }
    if (structSchema.kind === 'struct') {
        structSchema.fields.map(([fieldName, fieldType]: [any, any]) => {
            serializeField(schema, fieldName, obj[fieldName], fieldType, writer);
        });
    } else if (structSchema.kind === 'enum') {
        const name = obj[structSchema.field];
        for (let idx = 0; idx < structSchema.values.length; ++idx) {
            const [fieldName, fieldType]: [any, any] = structSchema.values[idx];
            if (fieldName === name) {
                writer.writeU8(idx);
                serializeField(schema, fieldName, obj[fieldName], fieldType, writer);
                break;
            }
        }
    } else {
        throw new BorshError(`Unexpected schema kind: ${structSchema.kind} for ${obj.constructor.name}`);
    }
}

/// Serialize given object using schema of the form:
/// { class_name -> [ [field_name, field_type], .. ], .. }
export function serialize(schema: Schema, obj: any): Uint8Array {
    const writer = new BinaryWriter();
    serializeStruct(schema, obj, writer);
    return writer.toArray();
}

function deserializeField(schema: Schema, fieldName: string, fieldType: any, reader: BinaryReader): any {
    try {
        if (typeof fieldType === 'string') {
            return reader[`read${capitalizeFirstLetter(fieldType)}`]();
        }

        if (fieldType instanceof Array) {
            if (typeof fieldType[0] === 'number') {
                return reader.readFixedArray(fieldType[0]);
            }

            return reader.readArray(() => deserializeField(schema, fieldName, fieldType[0], reader));
        }

        return deserializeStruct(schema, fieldType, reader);
    } catch (error) {
        if (error instanceof BorshError) {
            error.addToFieldPath(fieldName);
        }
        throw error;
    }
}

function deserializeStruct(schema: Schema, classType: any, reader: BinaryReader) {
    const structSchema = schema.get(classType);
    if (!structSchema) {
        throw new BorshError(`Class ${classType.name} is missing in schema`);
    }

    if (structSchema.kind === 'struct') {
        const result = {};
        for (const [fieldName, fieldType] of schema.get(classType).fields) {
            result[fieldName] = deserializeField(schema, fieldName, fieldType, reader);
        }
        return new classType(result);
    }

    if (structSchema.kind === 'enum') {
        const idx = reader.readU8();
        if (idx >= structSchema.values.length) {
            throw new BorshError(`Enum index: ${idx} is out of range`);
        }
        const [fieldName, fieldType] = structSchema.values[idx];
        const fieldValue = deserializeField(schema, fieldName, fieldType, reader);
        return new classType({ [fieldName]: fieldValue });
    }

    throw new BorshError(`Unexpected schema kind: ${structSchema.kind} for ${classType.constructor.name}`);
}

/// Deserializes object from bytes using schema.
export function deserialize(schema: Schema, classType: any, buffer: Buffer): any {
    const reader = new BinaryReader(buffer);
    const result = deserializeStruct(schema, classType, reader);
    if (reader.offset < buffer.length) {
        throw new BorshError(`Unexpected ${buffer.length - reader.offset} bytes after deserialized data`);
    }
    return result;
}