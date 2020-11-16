package borsh_test

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/oasislabs/borsh"
)

func TestDecodeBoolean(t *testing.T) {
	// True value 1.
	bytes := []byte{0x01}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadBoolean()

	require.Nil(t, err)
	assert.Equal(t, true, val)

	// False value.
	bytes = []byte{0x0}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadBoolean()

	require.Nil(t, err)
	assert.Equal(t, false, val)

	// Multi-byte test.
	bytes = []byte{0x00, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadBoolean()

	require.Nil(t, err)
	assert.Equal(t, false, val)

	// Empty input.
	bytes = []byte{}
	dec = borsh.NewDecoder(bytes)
	_, err = dec.ReadBoolean()

	require.NotNil(t, err)
}

func TestDecodeU8(t *testing.T) {
	// Single-byte input.
	bytes := []byte{0x01}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadU8()

	require.Nil(t, err)
	assert.Equal(t, uint8(1), val)

	// Multi-byte test.
	bytes = []byte{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadU8()

	require.Nil(t, err)
	assert.Equal(t, uint8(1), val)

	// Empty input.
	bytes = []byte{}
	dec = borsh.NewDecoder(bytes)
	_, err = dec.ReadU8()

	require.NotNil(t, err)
}

func TestDecodeI8(t *testing.T) {
	// Single-byte input.
	bytes := []byte{0xFF}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadI8()

	require.Nil(t, err)
	assert.Equal(t, int8(-1), val)

	// Multi-byte input.
	bytes = []byte{0xFF, 0xFE, 0xFD, 0xFC, 0xFB, 0xFA, 0xF9, 0xF8, 0xF7}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadI8()

	require.Nil(t, err)
	assert.Equal(t, int8(-1), val)

	// Empty input.
	bytes = []byte{}
	dec = borsh.NewDecoder(bytes)
	_, err = dec.ReadI8()

	require.NotNil(t, err)
}

func TestDecodeU16(t *testing.T) {
	// Two-byte input.
	bytes := []byte{0x02, 0x01}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadU16()

	require.Nil(t, err)
	assert.Equal(t, uint16(258), val)

	// Multiple-byte input.
	bytes = []byte{0x02, 0x01, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadU16()

	require.Nil(t, err)
	assert.Equal(t, uint16(258), val)

	// One byte and empty input.
	bytes = []byte{0xFF}
	for i := 0; i < 2; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadU16()
		require.NotNil(t, err)
	}
}

func TestDecodeI16(t *testing.T) {
	// Two-byte input.
	bytes := []byte{0xFE, 0xFF}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadI16()

	require.Nil(t, err)
	assert.Equal(t, int16(-2), val)

	// Multiple-byte input.
	bytes = []byte{0xFE, 0xFF, 0xFD, 0xFC, 0xFB, 0xFA, 0xF9, 0xF8, 0xF7}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadI16()

	require.Nil(t, err)
	assert.Equal(t, int16(-2), val)

	// One byte and empty input.
	bytes = []byte{0xFF}
	for i := 0; i < 2; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadI16()
		require.NotNil(t, err)
	}
}

func TestDecodeU32(t *testing.T) {
	// Four-byte input.
	bytes := []byte{0x04, 0x03, 0x02, 0x01}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadU32()

	require.Nil(t, err)
	assert.Equal(t, uint32(16909060), val)

	// Multiple-byte input.
	bytes = []byte{0x04, 0x03, 0x02, 0x01, 0x05, 0x06, 0x07, 0x08, 0x09}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadU32()

	require.Nil(t, err)
	assert.Equal(t, uint32(16909060), val)

	// Three-, two-, one-byte and empty input.
	bytes = []byte{0x03, 0x02, 0x01}
	for i := 0; i < 4; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadU32()
		require.NotNil(t, err)
	}
}

func TestDecodeI32(t *testing.T) {
	// Four-byte input.
	bytes := []byte{0xFC, 0xFD, 0xFE, 0xFF}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadI32()

	require.Nil(t, err)
	assert.Equal(t, int32(-66052), val)

	// Multiple-byte input.
	bytes = []byte{0xFC, 0xFD, 0xFE, 0xFF, 0xFB, 0xFA, 0xF9, 0xF8, 0xF7}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadI32()

	require.Nil(t, err)
	assert.Equal(t, int32(-66052), val)

	// Three-, two-, one-byte and empty input.
	bytes = []byte{0xFD, 0xFE, 0xFF}
	for i := 0; i < 4; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadI32()
		require.NotNil(t, err)
	}
}

func TestDecodeU64(t *testing.T) {
	// Eight-byte input.
	bytes := []byte{0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadU64()

	require.Nil(t, err)
	assert.Equal(t, uint64(72623859790382856), val)

	// Multi-byte input.
	bytes = []byte{0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x09}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadU64()

	require.Nil(t, err)
	assert.Equal(t, uint64(72623859790382856), val)

	// Seven-, six-, ..., one-byte and empty input.
	bytes = []byte{0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01}
	for i := 0; i < 8; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadU64()
		require.NotNil(t, err)
	}
}

func TestDecodeI64(t *testing.T) {
	// Eight-byte input.
	bytes := []byte{0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadI64()

	require.Nil(t, err)
	assert.Equal(t, int64(-283686952306184), val)

	// Multi-byte input.
	bytes = []byte{0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF, 0xF7}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadI64()

	require.Nil(t, err)
	assert.Equal(t, int64(-283686952306184), val)

	// Seven-, six-, ..., one-byte and empty input.
	bytes = []byte{0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF}
	for i := 0; i < 8; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadI64()
		require.NotNil(t, err)
	}
}

func TestDecodeF32(t *testing.T) {
	// Four-byte input
	bytes := []byte{0xD8, 0x0F, 0x49, 0x40}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadF32()

	require.Nil(t, err)
	assert.Equal(t, float32(3.141592), val)

	// Multi-byte input
	bytes = []byte{0xD8, 0x0F, 0x49, 0x40, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadF32()

	require.Nil(t, err)
	assert.Equal(t, float32(3.141592), val)

	// Three-, two-, one-byte and empty input.
	bytes = []byte{0x0F, 0x49, 0x40}
	for i := 0; i < 4; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadF32()
		require.NotNil(t, err)
	}
}

func TestDecodeF64(t *testing.T) {
	// Eight-byte input
	bytes := []byte{0x7A, 0x00, 0x8B, 0xFC, 0xFA, 0x21, 0x09, 0x40}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadF64()

	require.Nil(t, err)
	assert.Equal(t, float64(3.141592), val)

	// Multi-byte input
	bytes = []byte{0x7A, 0x00, 0x8B, 0xFC, 0xFA, 0x21, 0x09, 0x40, 0xFF}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadF64()

	require.Nil(t, err)
	assert.Equal(t, float64(3.141592), val)

	// Seven-, six-, ..., one-byte and empty input.
	bytes = []byte{0x00, 0x8B, 0xFC, 0xFA, 0x21, 0x09, 0x40}
	for i := 0; i < 8; i++ {
		dec = borsh.NewDecoder(bytes[i:])
		_, err = dec.ReadF64()
		require.NotNil(t, err)
	}
}

func TestDecodeString(t *testing.T) {
	// "i am a string" with some extra characters
	bytes := []byte{
		0x0D, 0x00, 0x00, 0x00, // Length: 13
		0x69, 0x20, 0x61, 0x6d, 0x20, 0x61, 0x20, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67,
		0x01, 0x02, 0x02,
	}
	dec := borsh.NewDecoder(bytes)
	val, err := dec.ReadString()

	require.Nil(t, err)
	assert.Equal(t, "i am a string", val)

	// Empty string.
	bytes = []byte{
		0x00, 0x00, 0x00, 0x00, // Length: 0
	}
	dec = borsh.NewDecoder(bytes)
	val, err = dec.ReadString()

	require.Nil(t, err)
	assert.Equal(t, "", val)
}
