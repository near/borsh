// Package borsh implements encoding and decoding of objects using borsh as the
// wire format. The borsh serialization/deserialization protocol is defined below:
//
// https://github.com/oasislabs/borsh#specification
//
// Specific mappings between Go values and their corresponding borsh encodings
// are described in the documentation for the Marshal and Unmarshal functions.
package borsh

import (
	"reflect"
)

// Marshal returns the borsh encoding of v.
//
// Marshal traverses the value v recursively, borsh encoding encountered values
// as it progresses. Invalid values that violate the borsh specification will
// cause a panic.
//
// Notably, the following borsh spec types are not yet supported:
// 	U128
// 	I128
// 	Fields
// 	Named fields
// 	Unnamed fields
//	Result
//
// Additionally, the following types require special handling:
// 	HashSet - A HashSet<T> must be decoded into a map[T]bool
//	Option - A Option<T> must be decoded into a *T, where a nil pointer indicates
// 	         the option is None, while a valid pointer indicates the option is Some.
func Marshal(v interface{}) ([]byte, error) {
	e := NewEncoder()
	if err := e.marshal(v); err != nil {
		return nil, err
	}
	return e.Finish(), nil
}

// Unmarshal parses the borsh-encoded data and stores the result in the value pointed to by v.
//
// Unmarshal uses the inverse of the encodings that Marshal uses. The caller is (for now)
// responsible for ensuring that maps, slices, and pointers are allocated as necessary.
func Unmarshal(data []byte, v interface{}) error {
	d := NewDecoder(data)
	return d.unmarshal(reflect.ValueOf(v))
}
