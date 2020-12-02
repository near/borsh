/// <reference types="node" />
import BN from 'bn.js';
export declare function base_encode(value: Uint8Array | string): string;
export declare function base_decode(value: string): Uint8Array;
export declare type Schema = Map<Function, any>;
export declare class BorshError extends Error {
    originalMessage: string;
    fieldPath: string[];
    constructor(message: string);
    addToFieldPath(fieldName: string): void;
}
export declare class BinaryWriter {
    buf: Buffer;
    length: number;
    constructor();
    maybe_resize(): void;
    write_u8(value: number): void;
    write_u32(value: number): void;
    write_u64(value: BN): void;
    write_u128(value: BN): void;
    private write_buffer;
    write_string(str: string): void;
    write_fixed_array(array: Uint8Array): void;
    write_array(array: any[], fn: any): void;
    toArray(): Uint8Array;
}
export declare class BinaryReader {
    buf: Buffer;
    offset: number;
    constructor(buf: Buffer);
    read_u8(): number;
    read_u32(): number;
    read_u64(): BN;
    read_u128(): BN;
    private read_buffer;
    read_string(): string;
    read_fixed_array(len: number): Uint8Array;
    read_array(fn: any): any[];
}
export declare function serialize(schema: Schema, obj: any): Uint8Array;
export declare function deserialize(schema: Schema, classType: any, buffer: Buffer): any;
