package borsh

import (
	"bytes"
	"encoding/binary"
	"reflect"

	"github.com/pkg/errors"
)

// Decoder decodes primitive borsh-encoded values.
type Decoder struct {
	Buffer *bytes.Buffer
}

// NewDecoder creates a new decoder.
func NewDecoder(data []byte) *Decoder {
	return &Decoder{
		Buffer: bytes.NewBuffer(data),
	}
}

// ReadBoolean decodes a boolean from the encoded buffer.
func (d *Decoder) ReadBoolean() (bool, error) {
	u8, err := d.ReadU8()
	if err != nil {
		return false, err
	}
	return u8 != 0, nil
}

// ReadU8 decodes an unsigned 8-bit integer from the encoded buffer.
func (d *Decoder) ReadU8() (u8 uint8, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &u8)
	return
}

// ReadI8 decodes a signed 8-bit integer from the encoded buffer.
func (d *Decoder) ReadI8() (i8 int8, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &i8)
	return
}

// ReadU16 decodes an unsigned 16-bit integer from the encoded buffer.
func (d *Decoder) ReadU16() (u16 uint16, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &u16)
	return
}

// ReadI16 decodes a signed 16-bit integer from the encoded buffer.
func (d *Decoder) ReadI16() (i16 int16, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &i16)
	return
}

// ReadU32 decodes an unsigned 32-bit integer from the encoded buffer.
func (d *Decoder) ReadU32() (u32 uint32, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &u32)
	return
}

// ReadI32 decodes a signed 32-bit integer from the encoded buffer.
func (d *Decoder) ReadI32() (i32 int32, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &i32)
	return
}

// ReadU64 decodes an unsigned 64-bit integer from the encoded buffer.
func (d *Decoder) ReadU64() (u64 uint64, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &u64)
	return
}

// ReadI64 decodes a signed 64-bit integer from the encoded buffer.
func (d *Decoder) ReadI64() (i64 int64, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &i64)
	return
}

// ReadF32 decodes a 32-bit float from the encoded buffer.
func (d *Decoder) ReadF32() (f32 float32, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &f32)
	return
}

// ReadF32 decodes a 64-bit float from the encoded buffer.
func (d *Decoder) ReadF64() (f64 float64, err error) {
	err = binary.Read(d.Buffer, binary.LittleEndian, &f64)
	return
}

// ReadString decodes a string from the encoded buffer.
func (d *Decoder) ReadString() (string, error) {
	length, err := d.ReadU32()
	if err != nil {
		return "", err
	}
	return string(d.Buffer.Next(int(length))), nil
}

// Remainder retrieves all remaining bytes that have not been decoded by the decoder.
func (d *Decoder) Remainder() []byte {
	return d.Buffer.Bytes()
}

func (d *Decoder) unmarshal(v reflect.Value) error {
	return d.reflectValue(v.Elem())
}

func (d *Decoder) reflectValue(v reflect.Value) error {
	return newTypeDecoder(v.Type())(d, v)
}

type decoderFunc func(d *Decoder, v reflect.Value) error

func newTypeDecoder(t reflect.Type) decoderFunc {
	switch t.Kind() {
	case reflect.Bool:
		return boolDecoder
	case reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return uintDecoder
	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return intDecoder
	case reflect.Float32, reflect.Float64:
		return floatDecoder
	case reflect.Array:
		return newArrayDecoder(t)
	case reflect.Slice:
		return newSliceDecoder(t)
	case reflect.Struct:
		return newStructDecoder(t)
	case reflect.Map:
		switch t.Elem().Kind() {
		case reflect.Bool:
			// A value type of `bool` indicates this map is a set.
			return newSetDecoder(t)
		default:
			// Any other value type indicates a map as usual.
			return newMapDecoder(t)
		}
	case reflect.Ptr:
		// A pointer represents an `Option`. If the pointer is nil, the object is `None`.
		return newOptionDecoder(t)
	case reflect.String:
		return stringDecoder
	default:
		return unsupportedTypeDecoder
	}
}

func boolDecoder(d *Decoder, v reflect.Value) error {
	b, err := d.ReadBoolean()
	if err != nil {
		return err
	}
	v.SetBool(b)
	return nil
}

func uintDecoder(d *Decoder, v reflect.Value) (err error) {
	u8, u16, u32, u64 := uint8(0), uint16(0), uint32(0), uint64(0)

	switch v.Kind() {
	case reflect.Uint8:
		u8, err = d.ReadU8()
		u64 = uint64(u8)
	case reflect.Uint16:
		u16, err = d.ReadU16()
		u64 = uint64(u16)
	case reflect.Uint32:
		u32, err = d.ReadU32()
		u64 = uint64(u32)
	case reflect.Uint64:
		u64, err = d.ReadU64()
	default:
		err = errors.Errorf("borsh: unexpected uint type: %v", v.Kind())
	}
	if err != nil {
		return
	}
	v.SetUint(u64)
	return
}

func intDecoder(d *Decoder, v reflect.Value) (err error) {
	i8, i16, i32, i64 := int8(0), int16(0), int32(0), int64(0)

	switch v.Kind() {
	case reflect.Int8:
		i8, err = d.ReadI8()
		i64 = int64(i8)
	case reflect.Int16:
		i16, err = d.ReadI16()
		i64 = int64(i16)
	case reflect.Int32:
		i32, err = d.ReadI32()
		i64 = int64(i32)
	case reflect.Int64:
		i64, err = d.ReadI64()
	default:
		err = errors.Errorf("borsh: unexpected int type: %v", v.Kind())
	}
	if err != nil {
		return
	}
	v.SetInt(i64)
	return
}

func floatDecoder(d *Decoder, v reflect.Value) (err error) {
	f32, f64 := float32(0), float64(0)

	switch v.Kind() {
	case reflect.Float32:
		f32, err = d.ReadF32()
		f64 = float64(f32)
	case reflect.Float64:
		f64, err = d.ReadF64()
	default:
		err = errors.Errorf("borsh: unexpected float type: %v", v.Kind())
	}
	if err != nil {
		return
	}
	v.SetFloat(f64)
	return
}

type arrayDecoder struct {
	elemDecoder decoderFunc
}

func (ad arrayDecoder) decode(d *Decoder, v reflect.Value) error {
	for i := 0; i < v.Len(); i++ {
		if err := ad.elemDecoder(d, v.Index(i)); err != nil {
			return err
		}
	}
	return nil
}

func newArrayDecoder(t reflect.Type) decoderFunc {
	dec := arrayDecoder{newTypeDecoder(t.Elem())}
	return dec.decode
}

type sliceDecoder struct {
	elemDecoder decoderFunc
}

func (sd sliceDecoder) decode(d *Decoder, v reflect.Value) error {
	l, err := d.ReadU32()
	if err != nil {
		return err
	}
	length := int(l)
	v.Set(reflect.MakeSlice(v.Type(), length, length))
	for i := 0; i < length; i++ {
		if err := sd.elemDecoder(d, v.Index(i)); err != nil {
			return err
		}
	}
	return nil
}

func newSliceDecoder(t reflect.Type) decoderFunc {
	dec := sliceDecoder{newTypeDecoder(t.Elem())}
	return dec.decode
}

type structDecoder struct {
	elemDecoders []decoderFunc
}

func (sd structDecoder) decode(d *Decoder, v reflect.Value) error {
	for i := 0; i < v.NumField(); i++ {
		if err := sd.elemDecoders[i](d, v.Field(i)); err != nil {
			return err
		}
	}
	return nil
}

func newStructDecoder(t reflect.Type) decoderFunc {
	elemDecoders := make([]decoderFunc, t.NumField())
	for i := 0; i < t.NumField(); i++ {
		elemDecoders[i] = newTypeDecoder(t.Field(i).Type)
	}
	dec := structDecoder{elemDecoders}
	return dec.decode
}

type setDecoder struct {
	elemDecoder decoderFunc
}

func (sd setDecoder) decode(d *Decoder, v reflect.Value) error {
	length, err := d.ReadU32()
	if err != nil {
		return err
	}
	v.Set(reflect.MakeMap(v.Type()))
	for i := uint32(0); i < length; i++ {
		key := reflect.New(v.Type().Key()).Elem()
		if err := sd.elemDecoder(d, key); err != nil {
			return err
		}
		v.SetMapIndex(key, reflect.ValueOf(true))
	}
	return nil
}

func newSetDecoder(t reflect.Type) decoderFunc {
	dec := setDecoder{newTypeDecoder(t.Key())}
	return dec.decode
}

type mapDecoder struct {
	keyDecoder decoderFunc
	valDecoder decoderFunc
}

func (md mapDecoder) decode(d *Decoder, v reflect.Value) error {
	length, err := d.ReadU32()
	if err != nil {
		return err
	}
	v.Set(reflect.MakeMap(v.Type()))
	for i := uint32(0); i < length; i++ {
		key := reflect.New(v.Type().Key()).Elem()
		val := reflect.New(v.Type().Elem()).Elem()
		if err := md.keyDecoder(d, key); err != nil {
			return err
		}
		if err := md.valDecoder(d, val); err != nil {
			return err
		}
		v.SetMapIndex(key, val)
	}
	return nil
}

func newMapDecoder(t reflect.Type) decoderFunc {
	dec := mapDecoder{
		keyDecoder: newTypeDecoder(t.Key()),
		valDecoder: newTypeDecoder(t.Elem()),
	}
	return dec.decode
}

type optionDecoder struct {
	elemDecoder decoderFunc
}

func (od optionDecoder) decode(d *Decoder, v reflect.Value) error {
	exists, err := d.ReadBoolean()
	if err != nil {
		return err
	}
	if exists {
		// Input contains (at least) one element.
		v.Set(reflect.New(v.Type().Elem()))
		return od.elemDecoder(d, v.Elem())
	}
	// Input ends here.
	return nil
}

func newOptionDecoder(t reflect.Type) decoderFunc {
	dec := optionDecoder{newTypeDecoder(t.Elem())}
	return dec.decode
}

func stringDecoder(d *Decoder, v reflect.Value) error {
	s, err := d.ReadString()
	if err != nil {
		return err
	}
	v.SetString(s)
	return nil
}

func unsupportedTypeDecoder(d *Decoder, v reflect.Value) error {
	return errors.Errorf("borsh: unexpected type: %v", v.Kind())
}
