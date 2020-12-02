const borsh = require('../../lib/index');

class Assignable {
    constructor(properties) {
        Object.keys(properties).map((key) => {
            this[key] = properties[key];
        });
    }
}

class Test extends Assignable { }

test('serialize object', async () => {
    const value = new Test({ x: 255, y: 20, z: '123', q: [1, 2, 3] });
    const schema = new Map([[Test, { kind: 'struct', fields: [['x', 'u8'], ['y', 'u64'], ['z', 'string'], ['q', [3]]] }]]);
    const buf = borsh.serialize(schema, value);
    const newValue = borsh.deserialize(schema, Test, buf);
    expect(newValue.x).toEqual(255);
    expect(newValue.y.toString()).toEqual('20');
    expect(newValue.z).toEqual('123');
    expect(newValue.q).toEqual(new Uint8Array([1, 2, 3]));
});