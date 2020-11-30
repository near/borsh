const borsh = require('../../../lib/index.js');
const transaction = require('./transaction-example/transaction');

exports.fuzz = input => {
    try {
        const deserialized = borsh.deserialize(transaction.SCHEMA, transaction.Transaction, input);
        const serialized = borsh.serialize(transaction.SCHEMA, deserialized);
        if (!serialized.equals(input)) {
            console.log(`Mismatching output:\n${serialized.toString('hex')}\nand input:\n${input.toString('hex')}`);
            throw new Error('Mismatching input and output');
        }
    } catch (e) {
        if (e instanceof borsh.BorshError) {
            // Do nothing
        } else {
            throw e;
        }
    }
};