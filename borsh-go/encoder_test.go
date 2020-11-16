package borsh_test

import (
	"testing"

	"github.com/stretchr/testify/assert"

	"github.com/oasislabs/borsh"
)

func TestEncodeBoolean(t *testing.T) {
	enc := borsh.NewEncoder()
	val := true
	enc.WriteBoolean(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0x01}, bytes)
}

func TestEncodeU8(t *testing.T) {
	enc := borsh.NewEncoder()
	val := uint8(1)
	enc.WriteU8(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0x01}, bytes)
}

func TestEncodeI8(t *testing.T) {
	enc := borsh.NewEncoder()
	val := int8(-1)
	enc.WriteI8(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0xFF}, bytes)
}

func TestEncodeU16(t *testing.T) {
	enc := borsh.NewEncoder()
	val := uint16(257)
	enc.WriteU16(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0x01, 0x01}, bytes)
}

func TestEncodeI16(t *testing.T) {
	enc := borsh.NewEncoder()
	val := int16(-1)
	enc.WriteI16(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0xFF, 0xFF}, bytes)
}

func TestEncodeU32(t *testing.T) {
	enc := borsh.NewEncoder()
	val := uint32(16843009)
	enc.WriteU32(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0x01, 0x01, 0x01, 0x01}, bytes)
}

func TestEncodeI32(t *testing.T) {
	enc := borsh.NewEncoder()
	val := int32(-1)
	enc.WriteI32(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0xFF, 0xFF, 0xFF, 0xFF}, bytes)
}

func TestEncodeU64(t *testing.T) {
	enc := borsh.NewEncoder()
	val := uint64(72340172838076673)
	enc.WriteU64(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01}, bytes)
}

func TestEncodeI64(t *testing.T) {
	enc := borsh.NewEncoder()
	val := int64(-1)
	enc.WriteI64(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF}, bytes)
}

func TestEncodeF32(t *testing.T) {
	enc := borsh.NewEncoder()
	val := float32(3.141592)
	enc.WriteF32(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0xD8, 0x0F, 0x49, 0x40}, bytes)
}

func TestEncodeF64(t *testing.T) {
	enc := borsh.NewEncoder()
	val := float64(3.141592)
	enc.WriteF64(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{0x7A, 0x00, 0x8B, 0xFC, 0xFA, 0x21, 0x09, 0x40}, bytes)
}

func TestEncodeString(t *testing.T) {
	enc := borsh.NewEncoder()
	val := "i am a string"
	enc.WriteString(val)

	bytes := enc.Finish()
	assert.Equal(t, []byte{
		0x0D, 0x00, 0x00, 0x00, // Length: 13
		0x69, 0x20, 0x61, 0x6d, 0x20, 0x61, 0x20, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67, // "i am a string"
	}, bytes)
}
