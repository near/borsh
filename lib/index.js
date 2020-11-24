"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    Object.defineProperty(o, k2, { enumerable: true, get: function() { return m[k]; } });
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __decorate = (this && this.__decorate) || function (decorators, target, key, desc) {
    var c = arguments.length, r = c < 3 ? target : desc === null ? desc = Object.getOwnPropertyDescriptor(target, key) : desc, d;
    if (typeof Reflect === "object" && typeof Reflect.decorate === "function") r = Reflect.decorate(decorators, target, key, desc);
    else for (var i = decorators.length - 1; i >= 0; i--) if (d = decorators[i]) r = (c < 3 ? d(r) : c > 3 ? d(target, key, r) : d(target, key)) || r;
    return c > 3 && r && Object.defineProperty(target, key, r), r;
};
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.deserialize = exports.serialize = exports.BinaryReader = exports.BinaryWriter = exports.BorshError = void 0;
const bn_js_1 = __importDefault(require("bn.js"));
// TODO: Make sure this polyfill not included when not required
const encoding = __importStar(require("text-encoding-utf-8"));
const TextDecoder = (typeof global.TextDecoder !== 'function') ? encoding.TextDecoder : global.TextDecoder;
const textDecoder = new TextDecoder('utf-8', { fatal: true });
const INITIAL_LENGTH = 1024;
class BorshError extends Error {
    constructor(message) {
        super(message);
        this.fieldPath = [];
        this.originalMessage = message;
    }
    addToFieldPath(fieldName) {
        this.fieldPath.splice(0, 0, fieldName);
        // NOTE: Modifying message directly as jest doesn't use .toString()
        this.message = this.originalMessage + ': ' + this.fieldPath.join('.');
    }
}
exports.BorshError = BorshError;
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
function handlingRangeError(target, propertyKey, propertyDescriptor) {
    const originalMethod = propertyDescriptor.value;
    propertyDescriptor.value = function (...args) {
        try {
            return originalMethod.apply(this, args);
        }
        catch (e) {
            if (e instanceof RangeError) {
                const code = e.code;
                if (['ERR_BUFFER_OUT_OF_BOUNDS', 'ERR_OUT_OF_RANGE'].indexOf(code) >= 0) {
                    throw new BorshError('Reached the end of buffer when deserializing');
                }
            }
            throw e;
        }
    };
}
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
        return new bn_js_1.default(buf, 'le');
    }
    readU128() {
        const buf = this.readBuffer(16);
        return new bn_js_1.default(buf, 'le');
    }
    readBuffer(len) {
        if ((this.offset + len) > this.buf.length) {
            throw new BorshError(`Expected buffer length ${len} isn't within bounds`);
        }
        const result = this.buf.slice(this.offset, this.offset + len);
        this.offset += len;
        return result;
    }
    readString() {
        const len = this.readU32();
        const buf = this.readBuffer(len);
        try {
            // NOTE: Using TextDecoder to fail on invalid UTF-8
            return textDecoder.decode(buf);
        }
        catch (e) {
            throw new BorshError(`Error decoding UTF-8 string: ${e}`);
        }
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
__decorate([
    handlingRangeError
], BinaryReader.prototype, "readU8", null);
__decorate([
    handlingRangeError
], BinaryReader.prototype, "readU32", null);
__decorate([
    handlingRangeError
], BinaryReader.prototype, "readU64", null);
__decorate([
    handlingRangeError
], BinaryReader.prototype, "readU128", null);
__decorate([
    handlingRangeError
], BinaryReader.prototype, "readString", null);
__decorate([
    handlingRangeError
], BinaryReader.prototype, "readFixedArray", null);
__decorate([
    handlingRangeError
], BinaryReader.prototype, "readArray", null);
exports.BinaryReader = BinaryReader;
function capitalizeFirstLetter(string) {
    return string.charAt(0).toUpperCase() + string.slice(1);
}
function serializeField(schema, fieldName, value, fieldType, writer) {
    try {
        // TODO: Handle missing values properly (make sure they never result in just skipped write)
        if (typeof fieldType === 'string') {
            writer[`write${capitalizeFirstLetter(fieldType)}`](value);
        }
        else if (fieldType instanceof Array) {
            if (typeof fieldType[0] === 'number') {
                if (value.length !== fieldType[0]) {
                    throw new BorshError(`Expecting byte array of length ${fieldType[0]}, but got ${value.length} bytes`);
                }
                writer.writeFixedArray(value);
            }
            else {
                writer.writeArray(value, (item) => { serializeField(schema, fieldName, item, fieldType[0], writer); });
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
                        serializeField(schema, fieldName, value, fieldType.type, writer);
                    }
                    break;
                }
                default: throw new BorshError(`FieldType ${fieldType} unrecognized`);
            }
        }
        else {
            serializeStruct(schema, value, writer);
        }
    }
    catch (error) {
        if (error instanceof BorshError) {
            error.addToFieldPath(fieldName);
        }
        throw error;
    }
}
function serializeStruct(schema, obj, writer) {
    const structSchema = schema.get(obj.constructor);
    if (!structSchema) {
        throw new BorshError(`Class ${obj.constructor.name} is missing in schema`);
    }
    if (structSchema.kind === 'struct') {
        structSchema.fields.map(([fieldName, fieldType]) => {
            serializeField(schema, fieldName, obj[fieldName], fieldType, writer);
        });
    }
    else if (structSchema.kind === 'enum') {
        const name = obj[structSchema.field];
        for (let idx = 0; idx < structSchema.values.length; ++idx) {
            const [fieldName, fieldType] = structSchema.values[idx];
            if (fieldName === name) {
                writer.writeU8(idx);
                serializeField(schema, fieldName, obj[fieldName], fieldType, writer);
                break;
            }
        }
    }
    else {
        throw new BorshError(`Unexpected schema kind: ${structSchema.kind} for ${obj.constructor.name}`);
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
function deserializeField(schema, fieldName, fieldType, reader) {
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
    }
    catch (error) {
        if (error instanceof BorshError) {
            error.addToFieldPath(fieldName);
        }
        throw error;
    }
}
function deserializeStruct(schema, classType, reader) {
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
function deserialize(schema, classType, buffer) {
    const reader = new BinaryReader(buffer);
    const result = deserializeStruct(schema, classType, reader);
    if (reader.offset < buffer.length) {
        throw new BorshError(`Unexpected ${buffer.length - reader.offset} bytes after deserialized data`);
    }
    return result;
}
exports.deserialize = deserialize;
