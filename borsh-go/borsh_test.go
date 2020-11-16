package borsh_test

import (
	"testing"

	"github.com/stretchr/testify/assert"

	"github.com/oasislabs/borsh"
)

func TestRoundtripBoolean(t *testing.T) {
	var src, dst bool

	src = true
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x01}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripU8(t *testing.T) {
	var src, dst uint8

	src = 1
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x01}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripI8(t *testing.T) {
	var src, dst int8

	src = -1
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0xFF}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripU16(t *testing.T) {
	var src, dst uint16

	src = 257
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x01, 0x01}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripI16(t *testing.T) {
	var src, dst int16

	src = -1
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0xFF, 0xFF}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripU32(t *testing.T) {
	var src, dst uint32

	src = 16843009
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x01, 0x01, 0x01, 0x01}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripI32(t *testing.T) {
	var src, dst int32

	src = -1
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0xFF, 0xFF, 0xFF, 0xFF}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripU64(t *testing.T) {
	var src, dst uint64

	src = 72340172838076673
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripI64(t *testing.T) {
	var src, dst int64

	src = -1
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripF32(t *testing.T) {
	var src, dst float32

	src = 3.141592
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0xD8, 0x0F, 0x49, 0x40}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripF64(t *testing.T) {
	var src, dst float64

	src = 3.141592
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x7A, 0x00, 0x8B, 0xFC, 0xFA, 0x21, 0x09, 0x40}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripArray(t *testing.T) {
	var src, dst [5]uint8

	src = [5]uint8{1, 2, 3, 4, 5}
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x01, 0x02, 0x03, 0x04, 0x05}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripSlice(t *testing.T) {
	var src, dst []uint8

	src = []uint8{1, 2, 3, 4, 5}
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{
		0x05, 0x00, 0x00, 0x00, // Length: 5
		0x01, 0x02, 0x03, 0x04, 0x05, // [1 2 3 4 5]
	}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripStruct(t *testing.T) {
	type Event struct {
		Name string
		ID   uint16
	}

	var src, dst Event

	src = Event{
		Name: "my event",
		ID:   3,
	}
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{
		0x08, 0x00, 0x00, 0x00, // Length (Name): 8
		0x6d, 0x79, 0x20, 0x65, 0x76, 0x65, 0x6e, 0x74, // Name: "my event"
		0x03, 0x00, // ID: 3
	}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripMap(t *testing.T) {
	var src, dst map[string]uint8

	src = make(map[string]uint8)
	src["element with id 0"] = 0
	src["element with id 1"] = 1
	src["element with id 2"] = 2
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripSet(t *testing.T) {
	var src, dst map[string]bool

	src = make(map[string]bool)
	src["element which exists 0"] = true
	src["element which exists 1"] = true
	src["element which exists 2"] = true
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripOptionSome(t *testing.T) {
	var src, dst *uint32

	val := uint32(16843009)
	src = &val
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x01, 0x01, 0x01, 0x01, 0x01}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripOptionNone(t *testing.T) {
	var src, dst *uint32

	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{0x00}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Nil(t, src)
	assert.Nil(t, dst)
}

func TestRoundtripString(t *testing.T) {
	var src, dst string

	src = "i am a string"
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{
		0x0D, 0x00, 0x00, 0x00, // Length: 13
		0x69, 0x20, 0x61, 0x6d, 0x20, 0x61, 0x20, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67, // "i am a string"
	}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripEmptyStruct(t *testing.T) {
	type Void struct{}

	var src, dst Void
	src = Void{}
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripStructWithOptional(t *testing.T) {
	type StructWithOptional struct {
		OptionalString *string
	}
	optionalString := "hello, world"

	var src, dst StructWithOptional
	src = StructWithOptional{
		OptionalString: &optionalString,
	}
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)
	assert.Equal(t, []byte{
		0x1,                // Value exists
		0xc, 0x0, 0x0, 0x0, // Length: 12
		0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, // "hello, world"
	}, encoding)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}

func TestRoundtripNestedComplexTypes(t *testing.T) {
	type FoodItem struct {
		Name   string
		Rating uint32
	}

	type Person struct {
		Name       string
		Dependents []string
		Favorites  []FoodItem
	}

	var src, dst []Person
	daughter := Person{
		Name:       "daughter",
		Dependents: []string{},
		Favorites: []FoodItem{
			{
				Name:   "pizza",
				Rating: 10,
			},
		},
	}

	son := Person{
		Name:       "son",
		Dependents: []string{},
		Favorites: []FoodItem{
			{
				Name:   "ice cream",
				Rating: 9,
			},
		},
	}

	mom := Person{
		Name:       "mom",
		Dependents: []string{"son", "daughter"},
		Favorites: []FoodItem{
			{
				Name:   "salad",
				Rating: 7,
			},
			{
				Name:   "paneer tikka masala",
				Rating: 100,
			},
		},
	}

	dad := Person{
		Name:       "dad",
		Dependents: []string{"son", "daughter"},
		Favorites: []FoodItem{
			{
				Name:   "beer",
				Rating: 8,
			},
			{
				Name:   "wings",
				Rating: 9,
			},
		},
	}

	src = []Person{
		son,
		daughter,
		mom,
		dad,
	}
	encoding, err := borsh.Marshal(src)
	assert.Nil(t, err)

	err = borsh.Unmarshal(encoding, &dst)
	assert.Nil(t, err)
	assert.Equal(t, src, dst)
}
