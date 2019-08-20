<div align="center">

  <h1><code>borsh</code></h1>

  <p>
    <strong>Binary Object Representation Serializer for Hashing</strong>
  </p>
  
  <p>
    <a href="https://crates.io/crates/borsh"><img src="https://img.shields.io/crates/v/borsh.svg?style=flat-square" alt="Crates.io version" /></a>
    <a href="https://crates.io/crates/borsh"><img src="https://img.shields.io/crates/d/borsh.svg?style=flat-square" alt="Download" /></a>
    <a href="https://discord.gg/gBtUFKR"><img src="https://img.shields.io/discord/490367152054992913.svg" alt="Join the community on Discord" /></a>
  </p>
</div>

## Specification
In short, Borsh is a non self-describing binary serialization format. It is designed to serialize any objects to canonical and deterministic set of bytes.</p>

General principles:
* integers are little endian;
* sizes of dynamic containers are written before values as `u32`;
* all unordered containers (hashmap/hashset) are ordered in lexicographic order by key (in tie breaker case on value);
* structs are serialized in the order of fields in the struct;
* enums are serialized with using `u8` for the enum ordinal and then storing data inside the enum value (if present).
    
More formal specification:
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
            <td>for el in x <br/>&nbsp; write_representation(el as ident)</td>
        </tr>
        <tr>
            <td>Dynamic sized array</td>
            <td>vec_type: "Vec&lt;" ident '&gt;'</td>
            <td>write_representation(len() as u32)<br/>
                for el in x <br/>
                &nbsp; write_representation(el as ident)
            </td>
        </tr>
        <tr>
            <td>Struct</td>
            <td>struct_type: "struct" ident fields </td><td>write_representation(fields)</td>
        </tr>
        <tr>
            <td>Fields</td>
            <td>fields: [named_fields | unnamed_fields] </td>
            <td></td>
        </tr>
        <tr>
            <td>Named fields</td>
            <td>named_fields: '{' ident_field0 ':' ident_type0 ',' ident_field1 ':' ident_type1 ',' ... '}'</td>
            <td>write_representation(ident_field0 as ident_type0)<br/>
                write_representation(ident_field1 as ident_type1)<br/>
                ...
            </td>
        </tr>
        <tr>
            <td>Unnamed fields</td>
            <td>unnamed_fields: '(' ident_type0 ',' ident_type1 ',' ... ')'</td><td>write_representation(x.0 as type0)<br/>write_representation(x.1 as type1)<br/>...</td>
        </tr>
        <tr>
            <td>Enum</td>
            <td>enum: 'enum' ident '{' variant0 ',' variant1 ',' ... '}'<br/>
                variant: ident [ fields ] ?
            </td>
            <td>Suppose X is the number of the variant that the enum takes.<br/>
                write_representation(X as u8)<br/>
                write_representation(x.X as fieldsX)
            </td>
        </tr>
        <tr><td>HashMap</td><td>hashmap: "HashMap&lt;" ident0, ident1 "&gt;"</td><td>
            write_representation(x.len() as u32)<br/>
            for (k, v) in x.sorted_by_key() {<br/>
            &nbsp; write_representation(k as ident0) <br/>
            &nbsp; write_representation(v as ident1) <br/>
            } </td></tr>
        <tr><td>HashSet</td><td>hashset: "HashSet&lt;" ident "&gt;"</td><td>
            write_representation(x.len() as u32)<br/>
            for el in x.sorted() {<br/>
            &nbsp;write_representation(el as ident) <br/>
            } </td></tr>
        <tr>
            <td>Option</td>
            <td>option_type: "Option&lt;" ident '&gt;'</td>
            <td> if x.is_some() { <br/>
                &nbsp; write_representation(1 as u8) <br/>
                &nbsp; write_representation(x.unwrap() as ident) <br/>
                } else { <br/>
                &nbsp; write_representation(0 as u8) <br/>
                }
            </td>
        </tr>
        <tr>
            <td>String</td>
            <td>string_type: "String"</td>
            <td> encoded = utf8_encoding(x) as Vec&lt;u8&gt; <br/>
                write_representation(encoded.len() as u32) <br/>
                write_representation(encoded as Vec&lt;u8&gt;) </td>
        </tr>
    </table>
</div>

* Note, some parts of Rust grammar are not yet formalized, like enums and variants. We backwards derive EBNF forms of Rust grammar from [syn types](https://github.com/dtolnay/syn);
* Note, we had to extend repeatitions of EBNF and instead of defining them as [ ident_field ':' ident_type ',' ] * we define them as ident_field0 ':' ident_type0 ',' ident_field1 ':' ident_type1 ',' ... so that we can refer to individual elements in the pseudocode.
