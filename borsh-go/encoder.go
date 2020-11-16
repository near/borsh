package borsh

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"math"
	"reflect"
)

const (
	// The initial buffer size an encoder will maintain.
	INITIAL_BUFFER_SIZE = 256

	// The growth factor for buffer reallocations.
	GROWTH_FACTOR = 1.5
)

// An Encoder encodes primitive values according to the borsh specification.
type Encoder struct {
	Buffer *bytes.Buffer
}

// NewEncoder creates a new encoder.
func NewEncoder() *Encoder {
	buffer := new(bytes.Buffer)
	buffer.Grow(INITIAL_BUFFER_SIZE)
	return &Encoder{
		Buffer: buffer,
	}
}

// WriteBoolean encodes a boolean into the encoded buffer.
func (e *Encoder) WriteBoolean(b bool) {
	e.reserveCapacity(1)
	u8 := uint8(0)
	if b {
		u8 = 1
	}
	e.WriteU8(u8)
}

// WriteU8 encodes an unsigned 8-bit integer into the encoded buffer.
func (e *Encoder) WriteU8(u8 uint8) {
	e.reserveCapacity(1)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &u8)
}

// WriteI8 encodes a signed 8-bit integer into the encoded buffer.
func (e *Encoder) WriteI8(i8 int8) {
	e.reserveCapacity(1)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &i8)
}

// WriteU16 encodes an unsigned 16-bit integer into the encoded buffer.
func (e *Encoder) WriteU16(u16 uint16) {
	e.reserveCapacity(2)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &u16)
}

// WriteI16 encodes a signed 16-bit integer into the encoded buffer.
func (e *Encoder) WriteI16(i16 int16) {
	e.reserveCapacity(2)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &i16)
}

// WriteU32 encodes an unsigned 32-bit integer into the encoded buffer.
func (e *Encoder) WriteU32(u32 uint32) {
	e.reserveCapacity(4)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &u32)
}

// WriteI32 encodes a signed 32-bit integer into the encoded buffer.
func (e *Encoder) WriteI32(i32 int32) {
	e.reserveCapacity(4)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &i32)
}

// WriteU64 encodes an unsigned 64-bit integer into the encoded buffer.
func (e *Encoder) WriteU64(u64 uint64) {
	e.reserveCapacity(8)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &u64)
}

// WriteI64 encodes a signed 64-bit integer into the encoded buffer.
func (e *Encoder) WriteI64(i64 int64) {
	e.reserveCapacity(8)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &i64)
}

// WriteF32 encodes a 32-bit float into the encoded buffer.
func (e *Encoder) WriteF32(f32 float32) {
	e.reserveCapacity(4)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &f32)
}

// WriteF64 encodes a 32-bit float into the encoded buffer.
func (e *Encoder) WriteF64(f64 float64) {
	e.reserveCapacity(8)
	_ = binary.Write(e.Buffer, binary.LittleEndian, &f64)
}

// WriteString encodes a string into the encoded buffer.
func (e *Encoder) WriteString(str string) {
	encodedStr := bytes.NewBufferString(str)
	length := encodedStr.Len()
	e.WriteU32(uint32(length))

	e.reserveCapacity(length)
	_ = binary.Write(e.Buffer, binary.LittleEndian, encodedStr.Bytes())
}

// Finish retrieves all bytes that have been encoded by the encoder.
func (e *Encoder) Finish() []byte {
	return e.Buffer.Bytes()
}

// reserveCapacity grows the allocated buffer for the encoder to meet
// the quota defined by neededCapacity.
func (e *Encoder) reserveCapacity(neededCapacity int) {
	currentCapacity := e.Buffer.Cap() - e.Buffer.Len()
	if currentCapacity < neededCapacity {
		e.Buffer.Grow(
			max(
				int(math.Ceil(float64(e.Buffer.Cap())*GROWTH_FACTOR)),
				currentCapacity+neededCapacity,
			),
		)
	}
}

// Computes the max of x and y.
func max(x, y int) int {
	if x > y {
		return x
	}
	return y
}

func (e *Encoder) marshal(v interface{}) error {
	e.reflectValue(reflect.ValueOf(v))
	return nil
}

func (e *Encoder) reflectValue(v reflect.Value) {
	newTypeEncoder(v.Type())(e, v)
}

type encoderFunc func(e *Encoder, v reflect.Value)

func newTypeEncoder(t reflect.Type) encoderFunc {
	switch t.Kind() {
	case reflect.Bool:
		return boolEncoder
	case reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return uintEncoder
	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return intEncoder
	case reflect.Float32, reflect.Float64:
		return floatEncoder
	case reflect.Array:
		return newArrayEncoder(t)
	case reflect.Slice:
		return newSliceEncoder(t)
	case reflect.Struct:
		return newStructEncoder(t)
	case reflect.Map:
		switch t.Elem().Kind() {
		case reflect.Bool:
			// A value type of `bool` indicates this map is a set.
			return newSetEncoder(t)
		default:
			// Any other value type indicates a map as usual.
			return newMapEncoder(t)
		}
	case reflect.Ptr:
		// A pointer represents an `Option`. If the pointer is nil, the object is `None`.
		return newOptionEncoder(t)
	case reflect.String:
		return stringEncoder
	default:
		return unsupportedTypeEncoder
	}
}

func boolEncoder(e *Encoder, v reflect.Value) {
	e.WriteBoolean(v.Bool())
}

func uintEncoder(e *Encoder, v reflect.Value) {
	switch v.Kind() {
	case reflect.Uint8:
		e.WriteU8(uint8(v.Uint()))
	case reflect.Uint16:
		e.WriteU16(uint16(v.Uint()))
	case reflect.Uint32:
		e.WriteU32(uint32(v.Uint()))
	case reflect.Uint64:
		e.WriteU64(v.Uint())
	default:
		panic(fmt.Sprintf("borsh: unexpected uint type: %v", v.Kind()))
	}
}

func intEncoder(e *Encoder, v reflect.Value) {
	switch v.Kind() {
	case reflect.Int8:
		e.WriteI8(int8(v.Int()))
	case reflect.Int16:
		e.WriteI16(int16(v.Int()))
	case reflect.Int32:
		e.WriteI32(int32(v.Int()))
	case reflect.Int64:
		e.WriteI64(v.Int())
	default:
		panic(fmt.Sprintf("borsh: unexpected int type: %v", v.Kind()))
	}
}

func floatEncoder(e *Encoder, v reflect.Value) {
	switch v.Kind() {
	case reflect.Float32:
		e.WriteF32(float32(v.Float()))
	case reflect.Float64:
		e.WriteF64(v.Float())
	default:
		panic(fmt.Sprintf("borsh: unexpected float type: %v", v.Kind()))
	}
}

type arrayEncoder struct {
	elemEncoder encoderFunc
}

func (ad arrayEncoder) encode(e *Encoder, v reflect.Value) {
	for i := 0; i < v.Len(); i++ {
		ad.elemEncoder(e, v.Index(i))
	}
}

func newArrayEncoder(t reflect.Type) encoderFunc {
	enc := arrayEncoder{newTypeEncoder(t.Elem())}
	return enc.encode
}

type sliceEncoder struct {
	elemEncoder encoderFunc
}

func (sd sliceEncoder) encode(e *Encoder, v reflect.Value) {
	e.WriteU32(uint32(v.Len()))
	for i := 0; i < v.Len(); i++ {
		sd.elemEncoder(e, v.Index(i))
	}
}

func newSliceEncoder(t reflect.Type) encoderFunc {
	enc := sliceEncoder{newTypeEncoder(t.Elem())}
	return enc.encode
}

type structEncoder struct {
	elemEncoders []encoderFunc
}

func (sd structEncoder) encode(e *Encoder, v reflect.Value) {
	for i := 0; i < v.NumField(); i++ {
		sd.elemEncoders[i](e, v.Field(i))
	}
}

func newStructEncoder(t reflect.Type) encoderFunc {
	elemEncoders := make([]encoderFunc, t.NumField())
	for i := 0; i < t.NumField(); i++ {
		elemEncoders[i] = newTypeEncoder(t.Field(i).Type)
	}
	enc := structEncoder{elemEncoders}
	return enc.encode
}

type setEncoder struct {
	elemEncoder encoderFunc
}

func (sd setEncoder) encode(e *Encoder, v reflect.Value) {
	e.WriteU32(uint32(v.Len()))

	iter := v.MapRange()
	for iter.Next() { // TODO: Sort by key to match Borsh spec exactly.
		sd.elemEncoder(e, iter.Key())
	}
}

func newSetEncoder(t reflect.Type) encoderFunc {
	enc := setEncoder{newTypeEncoder(t.Key())}
	return enc.encode
}

type mapEncoder struct {
	keyEncoder encoderFunc
	valEncoder encoderFunc
}

func (md mapEncoder) encode(e *Encoder, v reflect.Value) {
	e.WriteU32(uint32(v.Len()))

	iter := v.MapRange()
	for iter.Next() { // TODO: Sort by key to match Borsh spec exactly.
		md.keyEncoder(e, iter.Key())
		md.valEncoder(e, iter.Value())
	}
}

func newMapEncoder(t reflect.Type) encoderFunc {
	enc := mapEncoder{
		keyEncoder: newTypeEncoder(t.Key()),
		valEncoder: newTypeEncoder(t.Elem()),
	}
	return enc.encode
}

type optionEncoder struct {
	elemEncoder encoderFunc
}

func (od optionEncoder) encode(e *Encoder, v reflect.Value) {
	if v.IsNil() {
		e.WriteBoolean(false)
	} else {
		e.WriteBoolean(true)
		od.elemEncoder(e, v.Elem())
	}
}

func newOptionEncoder(t reflect.Type) encoderFunc {
	enc := optionEncoder{newTypeEncoder(t.Elem())}
	return enc.encode
}

func stringEncoder(e *Encoder, v reflect.Value) {
	e.WriteString(v.String())
}

func unsupportedTypeEncoder(e *Encoder, v reflect.Value) {
	panic(fmt.Sprintf("borsh: unexpected type: %v", v.Kind()))
}
