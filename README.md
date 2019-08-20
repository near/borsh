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
<div>
  <h2>Specification</h2>
  <p>In short, BORsh is a non self-describing binary serialization format. It is designed to serialize to canonical and determenistic set of bytes any objects.</p>
  <p>General principles:</p>
  <ul>
    <li>integers are little endian;</li>
    <li>sizes of dynamic containers are written before values as <code>u32</code></li>
    <li>all unordered containers (hashmap/hashset) are first ordered in lexicographic order by key (in tie breaker case on value).</li>
    <li>structs are serialized in the order of fields in the struct.</li>
    <li>enums are serialized with using <code>u8</code> for the enum ordinal and then storing data inside the enum value (if present)</li>
  </ul>
  <p>More formal specification:</p>
  <table>
   <tr><td>Type</td><td>Type spec</td><td>Representation format</td></tr>
   <tr><td>Integers</td><td>u8 | u16 | u32 | u64 | u128</td><td>write little endian</td></tr>
   <tr><td>Fixed sized arrays</td><td>[u8; T]</td><td>for _ in 0..size write T</td></tr>
   <tr><td>Dynamic sized array</td><td>Vec&lt;T&gt;</td><td>len() as u32 || for _ in 0..len() write T</td></tr>
   <tr><td>Struct</td><td>struct { ..feilds }</td><td>for field in fields -> write field</td></tr>
  <tr><td>Enum</td><td>enum {</br>&nbsp;&nbsp;a {field: T},</br>&nbsp;&nbsp;b,</br>&nbsp;&nbsp;c(x, y)</br>}</td><td>enum ordinal as u8 || write value of enum if present</td></tr>
   <tr><td>HashMap</td><td>hashmap&lt;K, V&gt;</td><td>len() as u32 || for (k, v) in hashmap.sorted_by_key() { write k || write v } </td></tr>
   <tr><td>HashSet</td><td>hashset&lt;V&gt;</td><td>len() as u32 || for v in hashset.sorted_by_value() { write v } </td></tr>
  </table>
  </code>
</div>
