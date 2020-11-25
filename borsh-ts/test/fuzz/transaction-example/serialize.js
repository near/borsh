"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
const bs58_1 = __importDefault(require("bs58"));
function base_encode(value) {
    if (typeof (value) === 'string') {
        value = Buffer.from(value, 'utf8');
    }
    return bs58_1.default.encode(Buffer.from(value));
}
exports.base_encode = base_encode;
function base_decode(value) {
    return Buffer.from(bs58_1.default.decode(value));
}
exports.base_decode = base_decode;
