<div align="center">

  <h1><code>borsh</code></h1>

  <p>
    <strong>Binary Object Representation Serializer for Hashing</strong>
  </p>
  
  <p>
    <a href="https://crates.io/crates/borsh"><img src="https://img.shields.io/crates/v/borsh.svg?style=flat-square" alt="Crates.io version" /></a>
    <a href="https://crates.io/crates/borsh"><img src="https://img.shields.io/crates/d/borsh.svg?style=flat-square" alt="Download" /></a>
    <a href="https://discord.gg/gBtUFKR"><img src="https://img.shields.io/discord/490367152054992913.svg" alt="Join the community on Discord" /></a>
    <a href="https://opensource.org/licenses/Apache-2.0"> <img src="https://img.shields.io/badge/license-Apache2.0-blue.svg" alt="Apache 2.0 License" /></a>
  </p>
  
  <h3>
        <a href="http://borsh.io">Website</a>
        <span> | </span>
        <a href="https://github.com/nearprotocol/borsh#example">Example</a>
        <span> | </span>
        <a href="https://github.com/nearprotocol/borsh#features">Features</a>
        <span> | </span>
        <a href="https://github.com/nearprotocol/borsh#benchmarks">Benchmarks</a>
        <span> | </span>
        <a href="https://github.com/nearprotocol/borsh#specification">Specification</a>
      </h3>
</div>

Why do we need yet another serialization format? Borsh is the first serializer that prioritizes the following qualities that are crucial for security-critical projects:
* Consistent and specified binary representation:
   * Consistent means there is a bijective mapping between objects and their binary representations. There is no two binary representations that deserialize
   into the same object. This is extremely useful for applications that use binary representation to compute hash;
   * Borsh comes with a full specification that can be used for implementations in other languages;
* Safe. Borsh implementations use safe coding practices. In Rust, Borsh uses only safe code;
* Speed. In Rust, Borsh achieves high performance by opting out from [Serde](https://serde.rs) which makes it faster
  than [bincode](https://github.com/servo/bincode); which also reduces the code size.
  
## Example

```rust
use borsh::{BorshSerialize, BorshDeserialize};

#[derive(BorshSerialize, BorshDeserialize, PartialEq, Debug)]
struct A {
    x: u64,
    y: String,
}

#[test]
fn test_simple_struct() {
    let a = A {
        x: 3301,
        y: "liber primus".to_string(),
    };
    let encoded_a = a.try_to_vec().unwrap();
    let decoded_a = A::try_from_slice(&encoded_a).unwrap();
    assert_eq!(a, decoded_a);
}
```

## Features

Opting out from Serde allows borsh to have some features that currently are not available for serde-compatible serializers.
Currently we support two features: `borsh_init` and `borsh_skip` (the former one not available in Serde).

`borsh_init` allows to automatically run an initialization function right after deserialization. This adds a lot of convenience for objects that are architectured to be used as strictly immutable. Usage example:
```rust
#[derive(BorshSerialize, BorshDeserialize)]
#[borsh_init(init)]
struct Message {
    message: String,
    timestamp: u64,
    public_key: CryptoKey,
    signature: CryptoSignature
    hash: CryptoHash
}

impl Message {
    pub fn init(&mut self) {
        self.hash = CryptoHash::new().write_string(self.message).write_u64(self.timestamp);
        self.signature.verify(self.hash, self.public_key);
    }
}
```

`borsh_skip` allows to skip serializing/deserializing fields, assuming they implement `Default` trait, similary to `#[serde(skip)]`.
```rust
#[derive(BorshSerialize, BorshDeserialize)]
struct A {
    x: u64,
    #[borsh_skip]
    y: f32,
}
```

## Benchmarks

We measured the following benchmarks on objects that blockchain projects care about the most: blocks, block headers,
transactions, accounts. We took object structure from the [nearprotocol](https://nearprotocol.com) blockchain.
We used [Criterion](https://bheisler.github.io/criterion.rs/book/index.html) for building the following graphs.

The benchmarks were run on Google Cloud [n1-standard-2 (2 vCPUs, 7.5 GB memory)](https://cloud.google.com/compute/docs/machine-types).

Block header serialization speed vs block header size in bytes (size only roughly corresponds to the serialization complexity which causes non-smoothness of the graph):

![ser_header](http://borsh.io/criterion/ser_header/report/lines.svg)

Block header de-serialization speed vs block header size in bytes:

![ser_header](http://borsh.io/criterion/de_header/report/lines.svg)

Block serialization speed vs block size in bytes:

![ser_header](http://borsh.io/criterion/ser_block/report/lines.svg)

Block de-serialization speed vs block size in bytes:

![ser_header](http://borsh.io/criterion/de_block/report/lines.svg)

See complete report [here](http://borsh.io/criterion/report/index.html).

## Specification
In short, Borsh is a non self-describing binary serialization format. It is designed to serialize any objects to canonical and deterministic set of bytes.</p>

General principles:
* integers are little endian;
* sizes of dynamic containers are written before values as `u32`;
* all unordered containers (hashmap/hashset) are ordered in lexicographic order by key (in tie breaker case on value);
* structs are serialized in the order of fields in the struct;
* enums are serialized with using `u8` for the enum ordinal and then storing data inside the enum value (if present).
    
Formal specification:
<div>
    <table>
        <tr><td>Informal type</td><td><a href="https://doc.rust-lang.org/grammar.html">Rust EBNF </a> * </td><td>Pseudocode</td></tr>
        <tr>
            <td>Integers</td>
            <td>integer_type: ["u8" | "u16" | "u32" | "u64" | "u128" | "i8" | "i16" | "i32" | "i64" | "i128" ]</td>
            <td>little_endian(x)</td>
        </tr>
        <tr>
            <td>Floats</td>
            <td>float_type: ["f32" | "f64" ]</td>
            <td>err_if_nan(x)<br/>little_endian(x as integer_type)</td>
        </tr>
        <tr>
            <td>Unit</td>
            <td>unit_type: "()"</td><td>We do not write anything</td>
        </tr>
        <tr>
            <td>Fixed sized arrays</td>
            <td>array_type: '[' ident ';' literal ']'</td>
            <td>for el in x <br/>&nbsp; repr(el as ident)</td>
        </tr>
        <tr>
            <td>Dynamic sized array</td>
            <td>vec_type: "Vec&lt;" ident '&gt;'</td>
            <td>repr(len() as u32)<br/>
                for el in x <br/>
                &nbsp; repr(el as ident)
            </td>
        </tr>
        <tr>
            <td>Struct</td>
            <td>struct_type: "struct" ident fields </td><td>repr(fields)</td>
        </tr>
        <tr>
            <td>Fields</td>
            <td>fields: [named_fields | unnamed_fields] </td>
            <td></td>
        </tr>
        <tr>
            <td>Named fields</td>
            <td>named_fields: '{' ident_field0 ':' ident_type0 ',' ident_field1 ':' ident_type1 ',' ... '}'</td>
            <td>repr(ident_field0 as ident_type0)<br/>
                repr(ident_field1 as ident_type1)<br/>
                ...
            </td>
        </tr>
        <tr>
            <td>Unnamed fields</td>
            <td>unnamed_fields: '(' ident_type0 ',' ident_type1 ',' ... ')'</td><td>repr(x.0 as type0)<br/>repr(x.1 as type1)<br/>...</td>
        </tr>
        <tr>
            <td>Enum</td>
            <td>enum: 'enum' ident '{' variant0 ',' variant1 ',' ... '}'<br/>
                variant: ident [ fields ] ?
            </td>
            <td>Suppose X is the number of the variant that the enum takes.<br/>
                repr(X as u8)<br/>
                repr(x.X as fieldsX)
            </td>
        </tr>
        <tr><td>HashMap</td><td>hashmap: "HashMap&lt;" ident0, ident1 "&gt;"</td><td>
            repr(x.len() as u32)<br/>
            for (k, v) in x.sorted_by_key() {<br/>
            &nbsp; repr(k as ident0) <br/>
            &nbsp; repr(v as ident1) <br/>
            } </td></tr>
        <tr><td>HashSet</td><td>hashset: "HashSet&lt;" ident "&gt;"</td><td>
            repr(x.len() as u32)<br/>
            for el in x.sorted() {<br/>
            &nbsp;repr(el as ident) <br/>
            } </td></tr>
        <tr>
            <td>Option</td>
            <td>option_type: "Option&lt;" ident '&gt;'</td>
            <td> if x.is_some() { <br/>
                &nbsp; repr(1 as u8) <br/>
                &nbsp; repr(x.unwrap() as ident) <br/>
                } else { <br/>
                &nbsp; repr(0 as u8) <br/>
                }
            </td>
        </tr>
        <tr>
            <td>String</td>
            <td>string_type: "String"</td>
            <td> encoded = utf8_encoding(x) as Vec&lt;u8&gt; <br/>
                repr(encoded.len() as u32) <br/>
                repr(encoded as Vec&lt;u8&gt;) </td>
        </tr>
    </table>
</div>

Note: 
* Some parts of Rust grammar are not yet formalized, like enums and variants. We backwards derive EBNF forms of Rust grammar from [syn types](https://github.com/dtolnay/syn);
* We had to extend repetitions of EBNF and instead of defining them as `[ ident_field ':' ident_type ',' ] *` we define them as `ident_field0 ':' ident_type0 ',' ident_field1 ':' ident_type1 ',' ...` so that we can refer to individual elements in the pseudocode;
* We use `repr()` function to denote that we are writing the representation of the given element into an imaginary buffer.
