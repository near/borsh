"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const bn_js_1 = __importDefault(require("bn.js"));
const INITIAL_LENGTH = 1024;
/// Binary encoder.
class BinaryWriter {
    constructor() {
        this.buf = Buffer.alloc(INITIAL_LENGTH);
        this.length = 0;
    }
    maybeResize() {
        if (this.buf.length < 16 + this.length) {
            this.buf = Buffer.concat([this.buf, Buffer.alloc(INITIAL_LENGTH)]);
        }
    }
    writeU8(value) {
        this.maybeResize();
        this.buf.writeUInt8(value, this.length);
        this.length += 1;
    }
    writeU32(value) {
        this.maybeResize();
        this.buf.writeUInt32LE(value, this.length);
        this.length += 4;
    }
    writeU64(value) {
        this.maybeResize();
        this.writeBuffer(Buffer.from(new bn_js_1.default(value).toArray('le', 8)));
    }
    writeU128(value) {
        this.maybeResize();
        this.writeBuffer(Buffer.from(new bn_js_1.default(value).toArray('le', 16)));
    }
    writeBuffer(buffer) {
        // Buffer.from is needed as this.buf.subarray can return plain Uint8Array in browser
        this.buf = Buffer.concat([Buffer.from(this.buf.subarray(0, this.length)), buffer, Buffer.alloc(INITIAL_LENGTH)]);
        this.length += buffer.length;
    }
    writeString(str) {
        this.maybeResize();
        const b = Buffer.from(str, 'utf8');
        this.writeU32(b.length);
        this.writeBuffer(b);
    }
    writeFixedArray(array) {
        this.writeBuffer(Buffer.from(array));
    }
    writeArray(array, fn) {
        this.maybeResize();
        this.writeU32(array.length);
        for (const elem of array) {
            this.maybeResize();
            fn(elem);
        }
    }
    toArray() {
        return this.buf.subarray(0, this.length);
    }
}
exports.BinaryWriter = BinaryWriter;
class BinaryReader {
    constructor(buf) {
        this.buf = buf;
        this.offset = 0;
    }
    readU8() {
        const value = this.buf.readUInt8(this.offset);
        this.offset += 1;
        return value;
    }
    readU32() {
        const value = this.buf.readUInt32LE(this.offset);
        this.offset += 4;
        return value;
    }
    readU64() {
        const buf = this.readBuffer(8);
        buf.reverse();
        return new bn_js_1.default(`${buf.toString('hex')}`, 16);
    }
    readU128() {
        const buf = this.readBuffer(16);
        return new bn_js_1.default(buf);
    }
    readBuffer(len) {
        const result = this.buf.slice(this.offset, this.offset + len);
        this.offset += len;
        return result;
    }
    readString() {
        const len = this.readU32();
        return this.readBuffer(len).toString('utf8');
    }
    readFixedArray(len) {
        return new Uint8Array(this.readBuffer(len));
    }
    readArray(fn) {
        const len = this.readU32();
        const result = Array();
        for (let i = 0; i < len; ++i) {
            result.push(fn());
        }
        return result;
    }
}
exports.BinaryReader = BinaryReader;
function serializeField(schema, value, fieldType, writer) {
    if (typeof fieldType === 'string') {
        writer[`write${fieldType}`](value);
    }
    else if (fieldType instanceof Array) {
        if (typeof fieldType[0] === 'number') {
            writer.writeFixedArray(value);
        }
        else {
            writer.writeArray(value, (item) => { serializeField(schema, item, fieldType[0], writer); });
        }
    }
    else if (fieldType.kind !== undefined) {
        switch (fieldType.kind) {
            case 'option': {
                if (value === null) {
                    writer.writeU8(0);
                }
                else {
                    writer.writeU8(1);
                    serializeField(schema, value, fieldType.type, writer);
                }
                break;
            }
            default: throw new Error(`FieldType ${fieldType} unrecognized`);
        }
    }
    else {
        serializeStruct(schema, value, writer);
    }
}
function serializeStruct(schema, obj, writer) {
    const structSchema = schema.get(obj.constructor);
    if (!structSchema) {
        throw new Error(`Class ${obj.constructor.name} is missing in schema`);
    }
    if (structSchema.kind === 'struct') {
        structSchema.fields.map(([fieldName, fieldType]) => {
            serializeField(schema, obj[fieldName], fieldType, writer);
        });
    }
    else if (structSchema.kind === 'enum') {
        const name = obj[structSchema.field];
        for (let idx = 0; idx < structSchema.values.length; ++idx) {
            const [fieldName, fieldType] = structSchema.values[idx];
            if (fieldName === name) {
                writer.writeU8(idx);
                serializeField(schema, obj[fieldName], fieldType, writer);
                break;
            }
        }
    }
    else {
        throw new Error(`Unexpected schema kind: ${structSchema.kind} for ${obj.constructor.name}`);
    }
}
/// Serialize given object using schema of the form:
/// { class_name -> [ [field_name, field_type], .. ], .. }
function serialize(schema, obj) {
    const writer = new BinaryWriter();
    serializeStruct(schema, obj, writer);
    return writer.toArray();
}
exports.serialize = serialize;
function deserializeField(schema, fieldType, reader) {
    if (typeof fieldType === 'string') {
        return reader[`read${fieldType}`]();
    }
    else if (fieldType instanceof Array) {
        if (typeof fieldType[0] === 'number') {
            return reader.readFixedArray(fieldType[0]);
        }
        else {
            return reader.readArray(() => deserializeField(schema, fieldType[0], reader));
        }
    }
    else {
        return deserializeStruct(schema, fieldType, reader);
    }
}
function deserializeStruct(schema, classType, reader) {
    const fields = schema.get(classType).fields.map(([fieldName, fieldType]) => {
        return deserializeField(schema, fieldType, reader);
    });
    return new classType(...fields);
}
/// Deserializes object from bytes using schema.
function deserialize(schema, classType, buffer) {
    const reader = new BinaryReader(buffer);
    return deserializeStruct(schema, classType, reader);
}
exports.deserialize = deserialize;
