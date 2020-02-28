//! Generate `BorshSchemaCointainer` for `BorshSchemaContainer` and save it into a file.
use borsh::schema::BorshSchema;
use borsh::BorshSerialize;
use std::fs::File;
use std::io::Write;

fn main() {
    let container = borsh::schema::BorshSchemaContainer::schema_container();
    println!("{:?}", container);
    let data = container
        .try_to_vec()
        .expect("Failed to serialize BorshSchemaContainer");
    let mut file = File::create("schema_schema.dat").expect("Failed to create file");
    file.write_all(&data).expect("Failed to write file");
}
