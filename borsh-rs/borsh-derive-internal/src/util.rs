use syn::{Generics, parse_quote};

pub fn add_ser_constraints(mut generics: Generics) -> Generics {
    for type_param in generics.type_params_mut() {
        type_param.bounds.push(parse_quote!(borsh::ser::BorshSerialize));
    }
    generics
}

pub fn add_de_constraints(mut generics: Generics) -> Generics {
    for type_param in generics.type_params_mut() {
        type_param.bounds.push(parse_quote!(borsh::de::BorshDeserialize));
    }
    generics
}
