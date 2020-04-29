
const borsh = require('../../borsh-js/index.js');

class Assignable {
    constructor(properties) {
        Object.keys(properties).map((key) => {
            this[key] = properties[key];
        });
    }
}

class Test extends Assignable {
}

test('serialize object', async () => {
    const value = new Test({ x: 255, y: 20, z: '123', q: [1, 2, 3] });
    const schema = new Map([[Test, { kind: 'struct', fields: [['x', 'u8'], ['y', 'u64'], ['z', 'string'], ['q', [3]]] }]]);
    let buf = borsh.serialize(schema, value);
    let new_value = borsh.deserialize(schema, Test, buf);
    expect(new_value.x).toEqual(255);
    expect(new_value.y.toString()).toEqual('20');
    expect(new_value.z).toEqual('123');
    expect(new_value.q).toEqual(new Uint8Array([1, 2, 3]));
});
