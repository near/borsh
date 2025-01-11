<div align="center">

  <h1><code>borsh</code></h1>

  <p>
    <strong>Binary Object Representation Serializer for Hashing</strong>
  </p>
  
  <h3>
    <a href="https://borsh.io">Website</a>
    <span> | </span>
    <a href="https://near.chat">Join Community</a>
    <span> | </span>
    <a href="https://github.com/nearprotocol/borsh#implementations">Implementations</a>
    <span> | </span>
    <a href="https://github.com/nearprotocol/borsh#benchmarks">Benchmarks</a>
    <span> | </span>
    <a href="https://github.com/nearprotocol/borsh#specification">Specification</a>
  </h3>
</div>

Why do we need yet another serialization format? Borsh is the first serializer that prioritizes the following qualities that are crucial for security-critical projects:

- Consistent and specified binary representation:
  - Consistent means there is a bijective mapping between objects and their binary representations. There is no two binary representations that deserialize
    into the same object. This is extremely useful for applications that use binary representation to compute hash;
  - Borsh comes with a full specification that can be used for implementations in other languages;
- Safe. Borsh implementations use safe coding practices. In Rust, Borsh uses almost only safe code, with one exception usage of `unsafe` to avoid an exhaustion attack;
- Speed. In Rust, Borsh achieves high performance by opting out from [Serde](https://serde.rs) which makes it faster
  than [bincode](https://github.com/servo/bincode) in some cases; which also reduces the code size.

## Implementations

| Platform                          | Repository                                   | Latest Release                                                                                                                                 |
| --------------------------------- | -------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| Rust                              | [borsh-rs](https://github.com/near/borsh-rs) | <a href="https://crates.io/crates/borsh"><img src="https://img.shields.io/crates/v/borsh.svg?style=flat-square" alt="Latest released version" /></a> |
| TypeScript, JavaScript            | [borsh-js](https://github.com/near/borsh-js) | <a href="https://npmjs.com/borsh"><img src="https://img.shields.io/npm/v/borsh.svg?style=flat-square" alt="Latest released version"></a>                           |
| TypeScript | [borsh-ts](https://github.com/dao-xyz/borsh-ts) | <a href="https://npmjs.com/package/@dao-xyz/borsh"><img src="https://img.shields.io/npm/v/@dao-xyz/borsh.svg?style=flat-square" alt="Latest released version"></a> |
| Java, Kotlin, Scala, Clojure, etc | [borshj](https://github.com/near/borshj)     |                                                                                                                                                |
| Go                                | [borsh-go](https://github.com/near/borsh-go) | <a href="https://github.com/near/borsh-go"><img src="https://img.shields.io/github/v/release/near/borsh-go?sort=semver&style=flat-square" alt="Latest released version" /></a> |
| Python                            | [borsh-construct-py](https://github.com/near/borsh-construct-py) | <a href="https://pypi.org/project/borsh-construct/"><img src="https://img.shields.io/pypi/v/borsh-construct.svg?style=flat-square" alt="Latest released version" /></a>                                                                                                                               |
| Assemblyscript                    | [borsh-as](https://github.com/gagdiez/serial-as/tree/main/borsh) | <a href="https://www.npmjs.com/package/@serial-as/borsh"><img src="https://img.shields.io/npm/v/@serial-as/borsh?style=flat-square" alt="Latest released version" /></a> |
| C#                                | [Hexarc.Borsh](https://github.com/hexarc-software/hexarc-borsh) | <a href="https://www.nuget.org/packages/Hexarc.Borsh"><img src="https://img.shields.io/nuget/v/Hexarc.Borsh.svg?style=flat-square" alt="Latest released version" /></a> |
| C++                    | [borsh-cpp](https://github.com/Stolkerve/borsh-cpp) | *(work-in-progress)* |
| C++20                    | [borsh-cpp20](https://github.com/israelidanny/borsh-cpp20) | *(work-in-progress)* |
| Elixir                    | [borsh-ex](https://github.com/alexfilatov/borsh) | <a href="https://hex.pm/packages/borsh"><img src="https://img.shields.io/hexpm/v/borsh.svg?style=flat-square" alt="Latest released version" /></a> |
| Ruby | [borsh.rb](https://github.com/dryruby/borsh.rb) | <a href="https://rubygems.org/gems/borsh"><img src="https://img.shields.io/gem/v/borsh?style=flat-square" alt="Latest released version" /></a> |

## Benchmarks

We measured the following benchmarks on objects that blockchain projects care about the most: blocks, block headers,
transactions, accounts. We took object structure from the [NEAR Protocol](https://near.org) blockchain.
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

In short, Borsh is a non self-describing binary serialization format. It is designed to serialize any objects to canonical and deterministic set of bytes.

General principles:

- integers are little endian;
- sizes of dynamic containers are written before values as `u32`;
- all unordered containers (hashmap/hashset) are ordered in lexicographic order by key (in tie breaker case on value);
- structs are serialized in the order of fields in the struct;
- enums are serialized with using `u8` for the enum ordinal and then storing data inside the enum value (if present).

Formal specification:

<div>
  <table>
    <tr>
      <td>Informal type</td>
      <td><a href="https://doc.rust-lang.org/grammar.html">Rust EBNF </a> * </td>
      <td>Pseudocode</td>
    </tr>
    <tr>
      <td>Integers</td>
      <td>integer_type: ["u8" | "u16" | "u32" | "u64" | "u128" | "i8" | "i16" | "i32" | "i64" | "i128" ]</td>
      <td>little_endian(x)</td>
    </tr>
    <tr>
      <td>Floats</td>
      <td>float_type: ["f32" | "f64" ]</td>
      <td>
        err_if_nan(x)<br/>
        little_endian(x as integer_type)
      </td>
    </tr>
    <tr>
      <td>Unit</td>
      <td>unit_type: "()"</td>
      <td>We do not write anything</td>
    </tr>
    <tr>
      <td>Bool</td>
      <td>boolean_type: "bool"</td>
      <td>
        if x {<br/>
        &nbsp; repr(1 as u8)<br/>
        } else {<br/>
        &nbsp; repr(0 as u8)<br/>
        }
      </td>
    </tr>
    <tr>
      <td>Fixed sized arrays</td>
      <td>array_type: '[' ident ';' literal ']'</td>
      <td>
        for el in x {<br/>
        &nbsp; repr(el as ident)<br/>
        }
      </td>
    </tr>
    <tr>
      <td>Dynamic sized array</td>
      <td>vec_type: "Vec&lt;" ident '&gt;'</td>
      <td>
        repr(len() as u32)<br/>
        for el in x {<br/>
        &nbsp; repr(el as ident)<br/>
        }
      </td>
    </tr>
    <tr>
      <td>Struct</td>
      <td>struct_type: "struct" ident fields</td>
      <td>repr(fields)</td>
    </tr>
    <tr>
      <td>Fields</td>
      <td>fields: [named_fields | unnamed_fields]</td>
      <td></td>
    </tr>
    <tr>
      <td>Named fields</td>
      <td>named_fields: '{' ident_field0 ':' ident_type0 ',' ident_field1 ':' ident_type1 ',' ... '}'</td>
      <td>
        repr(ident_field0 as ident_type0)<br/>
        repr(ident_field1 as ident_type1)<br/>
        ...
      </td>
    </tr>
    <tr>
      <td>Unnamed fields</td>
      <td>unnamed_fields: '(' ident_type0 ',' ident_type1 ',' ... ')'</td>
      <td>
        repr(x.0 as type0)<br/>
        repr(x.1 as type1)<br/>
        ...
      </td>
    </tr>
    <tr>
      <td>Enum</td>
      <td>
        enum: 'enum' ident '{' variant0 ',' variant1 ',' ... '}'<br/>
        variant: ident [ fields ] ?
      </td>
      <td>
        Suppose X is the number of the variant that the enum takes.<br/>
        repr(X as u8)<br/>
        repr(x.X as fieldsX)
      </td>
    </tr>
    <tr>
      <td>HashMap</td>
      <td>hashmap: "HashMap&lt;" ident0, ident1 "&gt;"</td>
      <td>
        repr(x.len() as u32)<br/>
        for (k, v) in x.sorted_by_key() {<br/>
        &nbsp; repr(k as ident0)<br/>
        &nbsp; repr(v as ident1)<br/>
        }
      </td>
    </tr>
    <tr>
      <td>HashSet</td>
      <td>hashset: "HashSet&lt;" ident "&gt;"</td>
      <td>
        repr(x.len() as u32)<br/>
        for el in x.sorted() {<br/>
        &nbsp; repr(el as ident)<br/>
        }
      </td>
    </tr>
    <tr>
      <td>Option</td>
      <td>option_type: "Option&lt;" ident '&gt;'</td>
      <td>
        if x.is_some() {<br/>
        &nbsp; repr(1 as u8)<br/>
        &nbsp; repr(x.unwrap() as ident <br/>
        } else {<br/>
        &nbsp; repr(0 as u8)<br/>
        }
      </td>
    </tr>
    <tr>
      <td>String</td>
      <td>string_type: "String"</td>
      <td>
        encoded = utf8_encoding(x) as Vec&lt;u8&gt;<br/>
        repr(encoded.len() as u32)<br/>
        repr(encoded as Vec&lt;u8&gt;)
      </td>
    </tr>
  </table>
</div>

Note:

- Some parts of Rust grammar are not yet formalized, like enums and variants. We backwards derive EBNF forms of Rust grammar from [syn types](https://github.com/dtolnay/syn);
- We had to extend repetitions of EBNF and instead of defining them as `[ ident_field ':' ident_type ',' ] *` we define them as `ident_field0 ':' ident_type0 ',' ident_field1 ':' ident_type1 ',' ...` so that we can refer to individual elements in the pseudocode;
- We use `repr()` function to denote that we are writing the representation of the given element into an imaginary buffer.
