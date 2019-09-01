
const borsh = require('../../borsh-js/index.js');

class Test {
    constructor(x, y, z, q) {
        this.x = x;
        this.y = y;
        this.z = z;
        this.q = q;
    }
}

test('serialize object', async () => {
    const value = new Test(255, 20, '123', [1, 2, 3]);
    const schema = new Map([[Test, {kind: 'struct', fields: [['x', 'u8'], ['y', 'u64'], ['z', 'string'], ['q', [3]]] }]]);
    let buf = borsh.serialize(schema, value);
    let new_value = borsh.deserialize(schema, Test, buf);
    expect(new_value.x).toEqual(255);
    expect(new_value.y.toString()).toEqual('20');
    expect(new_value.z).toEqual('123');
    expect(new_value.q).toEqual(new Uint8Array([1, 2, 3]));
});

