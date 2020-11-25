/// <reference types="node" />
import BN from 'bn.js';
import { Enum, Assignable } from './enums';
import { KeyType, PublicKey } from './key_pair';
import { Signer } from './signer';
export declare class FunctionCallPermission extends Assignable {
    allowance?: BN;
    receiverId: string;
    methodNames: string[];
}
export declare class FullAccessPermission extends Assignable {
}
export declare class AccessKeyPermission extends Enum {
    functionCall: FunctionCallPermission;
    fullAccess: FullAccessPermission;
}
export declare class AccessKey extends Assignable {
    nonce: number;
    permission: AccessKeyPermission;
}
export declare function fullAccessKey(): AccessKey;
export declare function functionCallAccessKey(receiverId: string, methodNames: string[], allowance?: BN): AccessKey;
export declare class IAction extends Assignable {
}
export declare class CreateAccount extends IAction {
}
export declare class DeployContract extends IAction {
    code: Uint8Array;
}
export declare class FunctionCall extends IAction {
    methodName: string;
    args: Uint8Array;
    gas: BN;
    deposit: BN;
}
export declare class Transfer extends IAction {
    deposit: BN;
}
export declare class Stake extends IAction {
    stake: BN;
    publicKey: PublicKey;
}
export declare class AddKey extends IAction {
    publicKey: PublicKey;
    accessKey: AccessKey;
}
export declare class DeleteKey extends IAction {
    publicKey: PublicKey;
}
export declare class DeleteAccount extends IAction {
    beneficiaryId: string;
}
export declare function createAccount(): Action;
export declare function deployContract(code: Uint8Array): Action;
/**
 * Constructs {@link Action} instance representing contract method call.
 *
 * @param methodName the name of the method to call
 * @param args arguments to pass to method. Can be either plain JS object which gets serialized as JSON automatically
 *  or `Uint8Array` instance which represents bytes passed as is.
 * @param gas max amount of gas that method call can use
 * @param deposit amount of NEAR (in yoctoNEAR) to send together with the call
 */
export declare function functionCall(methodName: string, args: Uint8Array | object, gas: BN, deposit: BN): Action;
export declare function transfer(deposit: BN): Action;
export declare function stake(stake: BN, publicKey: PublicKey): Action;
export declare function addKey(publicKey: PublicKey, accessKey: AccessKey): Action;
export declare function deleteKey(publicKey: PublicKey): Action;
export declare function deleteAccount(beneficiaryId: string): Action;
export declare class Signature extends Assignable {
    keyType: KeyType;
    data: Uint8Array;
}
export declare class Transaction extends Assignable {
    signerId: string;
    publicKey: PublicKey;
    nonce: number;
    receiverId: string;
    actions: Action[];
    blockHash: Uint8Array;
    encode(): Uint8Array;
    static decode(bytes: Buffer): Transaction;
}
export declare class SignedTransaction extends Assignable {
    transaction: Transaction;
    signature: Signature;
    encode(): Uint8Array;
    static decode(bytes: Buffer): SignedTransaction;
}
/**
 * Contains a list of the valid transaction Actions available with this API
 */
export declare class Action extends Enum {
    createAccount: CreateAccount;
    deployContract: DeployContract;
    functionCall: FunctionCall;
    transfer: Transfer;
    stake: Stake;
    addKey: AddKey;
    deleteKey: DeleteKey;
    deleteAccount: DeleteAccount;
}
export declare const SCHEMA: Map<Function, any>;
export declare function createTransaction(signerId: string, publicKey: PublicKey, receiverId: string, nonce: number, actions: Action[], blockHash: Uint8Array): Transaction;
export declare function signTransaction(transaction: Transaction, signer: Signer, accountId?: string, networkId?: string): Promise<[Uint8Array, SignedTransaction]>;
export declare function signTransaction(receiverId: string, nonce: number, actions: Action[], blockHash: Uint8Array, signer: Signer, accountId?: string, networkId?: string): Promise<[Uint8Array, SignedTransaction]>;
