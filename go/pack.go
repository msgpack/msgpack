package msgpack

import (
	"io"
	"os"
	"reflect"
	"unsafe"
)

// Packs a given value and writes it into the specified writer.
func PackUint8(writer io.Writer, value uint8) (n int, err error) {
	if value < 128 {
		return writer.Write([]byte{byte(value)})
	}
	return writer.Write([]byte{0xcc, byte(value)})
}

// Packs a given value and writes it into the specified writer.
func PackUint16(writer io.Writer, value uint16) (n int, err error) {
	if value < 128 {
		return writer.Write([]byte{byte(value)})
	} else if value < 256 {
		return writer.Write([]byte{0xcc, byte(value)})
	}
	return writer.Write([]byte{0xcd, byte(value >> 8), byte(value)})
}

// Packs a given value and writes it into the specified writer.
func PackUint32(writer io.Writer, value uint32) (n int, err error) {
	if value < 128 {
		return writer.Write([]byte{byte(value)})
	} else if value < 256 {
		return writer.Write([]byte{0xcc, byte(value)})
	} else if value < 65536 {
		return writer.Write([]byte{0xcd, byte(value >> 8), byte(value)})
	}
	return writer.Write([]byte{0xce, byte(value >> 24), byte(value >> 16), byte(value >> 8), byte(value)})
}

// Packs a given value and writes it into the specified writer.
func PackUint64(writer io.Writer, value uint64) (n int, err error) {
	if value < 128 {
		return writer.Write([]byte{byte(value)})
	} else if value < 256 {
		return writer.Write([]byte{0xcc, byte(value)})
	} else if value < 65536 {
		return writer.Write([]byte{0xcd, byte(value >> 8), byte(value)})
	} else if value < 4294967296 {
		return writer.Write([]byte{0xce, byte(value >> 24), byte(value >> 16), byte(value >> 8), byte(value)})
	}
	return writer.Write([]byte{0xcf, byte(value >> 56), byte(value >> 48), byte(value >> 40), byte(value >> 32), byte(value >> 24), byte(value >> 16), byte(value >> 8), byte(value)})
}

func PackUint(writer io.Writer, value uint) (n int, err error) {
	// Packs a given value and writes it into the specified writer.
	switch unsafe.Sizeof(value) {
	case 4:
		return PackUint32(writer, *(*uint32)(unsafe.Pointer(&value)))
	case 8:
		return PackUint64(writer, *(*uint64)(unsafe.Pointer(&value)))
	}
	return 0, os.ErrNotExist // never get here
}

// Packs a given value and writes it into the specified writer.
func PackInt8(writer io.Writer, value int8) (n int, err error) {
	if value < -32 {
		return writer.Write([]byte{0xd0, byte(value)})
	}
	return writer.Write([]byte{byte(value)})
}

// Packs a given value and writes it into the specified writer.
func PackInt16(writer io.Writer, value int16) (n int, err error) {
	if value < -128 || value >= 128 {
		return writer.Write([]byte{0xd1, byte(uint16(value) >> 8), byte(value)})
	} else if value < -32 {
		return writer.Write([]byte{0xd0, byte(value)})
	}
	return writer.Write([]byte{byte(value)})
}

// Packs a given value and writes it into the specified writer.
func PackInt32(writer io.Writer, value int32) (n int, err error) {
	if value < -32768 || value >= 32768 {
		return writer.Write([]byte{0xd2, byte(uint32(value) >> 24), byte(uint32(value) >> 16), byte(uint32(value) >> 8), byte(value)})
	} else if value < -128 {
		return writer.Write([]byte{0xd1, byte(uint32(value) >> 8), byte(value)})
	} else if value < -32 {
		return writer.Write([]byte{0xd0, byte(value)})
	} else if value >= 128 {
		return writer.Write([]byte{0xd1, byte(uint32(value) >> 8), byte(value)})
	}
	return writer.Write([]byte{byte(value)})
}

// Packs a given value and writes it into the specified writer.
func PackInt64(writer io.Writer, value int64) (n int, err error) {
	if value < -2147483648 || value >= 2147483648 {
		return writer.Write([]byte{0xd3, byte(uint64(value) >> 56), byte(uint64(value) >> 48), byte(uint64(value) >> 40), byte(uint64(value) >> 32), byte(uint64(value) >> 24), byte(uint64(value) >> 16), byte(uint64(value) >> 8), byte(value)})
	} else if value < -32768 || value >= 32768 {
		return writer.Write([]byte{0xd2, byte(uint64(value) >> 24), byte(uint64(value) >> 16), byte(uint64(value) >> 8), byte(value)})
	} else if value < -128 || value >= 128 {
		return writer.Write([]byte{0xd1, byte(uint64(value) >> 8), byte(value)})
	} else if value < -32 {
		return writer.Write([]byte{0xd0, byte(value)})
	}
	return writer.Write([]byte{byte(value)})
}

// Packs a given value and writes it into the specified writer.
func PackInt(writer io.Writer, value int) (n int, err error) {
	switch unsafe.Sizeof(value) {
	case 4:
		return PackInt32(writer, *(*int32)(unsafe.Pointer(&value)))
	case 8:
		return PackInt64(writer, *(*int64)(unsafe.Pointer(&value)))
	}
	return 0, os.ErrNotExist // never get here
}

// Packs a given value and writes it into the specified writer.
func PackNil(writer io.Writer) (n int, err error) {
	return writer.Write([]byte{0xc0})
}

// Packs a given value and writes it into the specified writer.
func PackBool(writer io.Writer, value bool) (n int, err error) {
	var code byte
	if value {
		code = 0xc3
	} else {
		code = 0xc2
	}
	return writer.Write([]byte{code})
}

// Packs a given value and writes it into the specified writer.
func PackFloat32(writer io.Writer, value float32) (n int, err error) {
	return PackUint32(writer, *(*uint32)(unsafe.Pointer(&value)))
}

// Packs a given value and writes it into the specified writer.
func PackFloat64(writer io.Writer, value float64) (n int, err error) {
	return PackUint64(writer, *(*uint64)(unsafe.Pointer(&value)))
}

// Packs a given value and writes it into the specified writer.
func PackBytes(writer io.Writer, value []byte) (n int, err error) {
	if len(value) < 32 {
		n1, err := writer.Write([]byte{0xa0 | uint8(len(value))})
		if err != nil {
			return n1, err
		}
		n2, err := writer.Write(value)
		return n1 + n2, err
	} else if len(value) < 65536 {
		n1, err := writer.Write([]byte{0xda, byte(len(value) >> 16), byte(len(value))})
		if err != nil {
			return n1, err
		}
		n2, err := writer.Write(value)
		return n1 + n2, err
	}
	n1, err := writer.Write([]byte{0xdb, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
	if err != nil {
		return n1, err
	}
	n2, err := writer.Write(value)
	return n1 + n2, err
}

// Packs a given value and writes it into the specified writer.
func PackUint16Array(writer io.Writer, value []uint16) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint16(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint16(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint16(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackUint32Array(writer io.Writer, value []uint32) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackUint64Array(writer io.Writer, value []uint64) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackUint64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackUintArray(writer io.Writer, value []uint) (n int, err error) {
	switch unsafe.Sizeof(0) {
	case 4:
		return PackUint32Array(writer, *(*[]uint32)(unsafe.Pointer(&value)))
	case 8:
		return PackUint64Array(writer, *(*[]uint64)(unsafe.Pointer(&value)))
	}
	return 0, os.ErrNotExist // never get here
}

// Packs a given value and writes it into the specified writer.
func PackInt8Array(writer io.Writer, value []int8) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt8(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt8(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt8(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackInt16Array(writer io.Writer, value []int16) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt16(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt16(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt16(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackInt32Array(writer io.Writer, value []int32) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackInt64Array(writer io.Writer, value []int64) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackInt64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackIntArray(writer io.Writer, value []int) (n int, err error) {
	switch unsafe.Sizeof(0) {
	case 4:
		return PackInt32Array(writer, *(*[]int32)(unsafe.Pointer(&value)))
	case 8:
		return PackInt64Array(writer, *(*[]int64)(unsafe.Pointer(&value)))
	}
	return 0, os.ErrNotExist // never get here
}

// Packs a given value and writes it into the specified writer.
func PackFloat32Array(writer io.Writer, value []float32) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackFloat32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackFloat32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackFloat32(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackFloat64Array(writer io.Writer, value []float64) (n int, err error) {
	if len(value) < 16 {
		n, err := writer.Write([]byte{0x90 | byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackFloat64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if len(value) < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackFloat64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(len(value) >> 24), byte(len(value) >> 16), byte(len(value) >> 8), byte(len(value))})
		if err != nil {
			return n, err
		}
		for _, i := range value {
			_n, err := PackFloat64(writer, i)
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackArray(writer io.Writer, value reflect.Value) (n int, err error) {
	{
		elemType := value.Type().Elem()
		if (elemType.Kind() == reflect.Uint || elemType.Kind() == reflect.Uint8 || elemType.Kind() == reflect.Uint16 || elemType.Kind() == reflect.Uint32 || elemType.Kind() == reflect.Uint64 || elemType.Kind() == reflect.Uintptr) &&
			elemType.Kind() == reflect.Uint8 {
			return PackBytes(writer, value.Interface().([]byte))
		}
	}

	l := value.Len()
	if l < 16 {
		n, err := writer.Write([]byte{0x90 | byte(l)})
		if err != nil {
			return n, err
		}
		for i := 0; i < l; i++ {
			_n, err := PackValue(writer, value.Index(i))
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if l < 65536 {
		n, err := writer.Write([]byte{0xdc, byte(l >> 8), byte(l)})
		if err != nil {
			return n, err
		}
		for i := 0; i < l; i++ {
			_n, err := PackValue(writer, value.Index(i))
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdd, byte(l >> 24), byte(l >> 16), byte(l >> 8), byte(l)})
		if err != nil {
			return n, err
		}
		for i := 0; i < l; i++ {
			_n, err := PackValue(writer, value.Index(i))
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackMap(writer io.Writer, value reflect.Value) (n int, err error) {
	keys := value.MapKeys()
	if value.Len() < 16 {
		n, err := writer.Write([]byte{0x80 | byte(len(keys))})
		if err != nil {
			return n, err
		}
		for _, k := range keys {
			_n, err := PackValue(writer, k)
			if err != nil {
				return n, err
			}
			n += _n
			_n, err = PackValue(writer, value.MapIndex(k))
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else if value.Len() < 65536 {
		n, err := writer.Write([]byte{0xde, byte(len(keys) >> 8), byte(len(keys))})
		if err != nil {
			return n, err
		}
		for _, k := range keys {
			_n, err := PackValue(writer, k)
			if err != nil {
				return n, err
			}
			n += _n
			_n, err = PackValue(writer, value.MapIndex(k))
			if err != nil {
				return n, err
			}
			n += _n
		}
	} else {
		n, err := writer.Write([]byte{0xdf, byte(len(keys) >> 24), byte(len(keys) >> 16), byte(len(keys) >> 8), byte(len(keys))})
		if err != nil {
			return n, err
		}
		for _, k := range keys {
			_n, err := PackValue(writer, k)
			if err != nil {
				return n, err
			}
			n += _n
			_n, err = PackValue(writer, value.MapIndex(k))
			if err != nil {
				return n, err
			}
			n += _n
		}
	}
	return n, nil
}

// Packs a given value and writes it into the specified writer.
func PackValue(writer io.Writer, value reflect.Value) (n int, err error) {
	if !value.IsValid() || value.Type() == nil {
		return PackNil(writer)
	}
	switch _value := value; _value.Kind() {
	case reflect.Bool:
		return PackBool(writer, _value.Bool())
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
		return PackUint64(writer, _value.Uint())
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		return PackInt64(writer, _value.Int())
	case reflect.Float32, reflect.Float64:
		return PackFloat64(writer, _value.Float())
	case reflect.Array:
		return PackArray(writer, _value)
	case reflect.Slice:
		return PackArray(writer, _value)
	case reflect.Map:
		return PackMap(writer, _value)
	case reflect.String:
		return PackBytes(writer, []byte(_value.String()))
	case reflect.Interface:
		__value := reflect.ValueOf(_value.Interface())

		if __value.Kind() != reflect.Interface {
			return PackValue(writer, __value)
		}
	}
	panic("unsupported type: " + value.Type().String())
}

// Packs a given value and writes it into the specified writer.
func Pack(writer io.Writer, value interface{}) (n int, err error) {
	if value == nil {
		return PackNil(writer)
	}
	switch _value := value.(type) {
	case bool:
		return PackBool(writer, _value)
	case uint8:
		return PackUint8(writer, _value)
	case uint16:
		return PackUint16(writer, _value)
	case uint32:
		return PackUint32(writer, _value)
	case uint64:
		return PackUint64(writer, _value)
	case uint:
		return PackUint(writer, _value)
	case int8:
		return PackInt8(writer, _value)
	case int16:
		return PackInt16(writer, _value)
	case int32:
		return PackInt32(writer, _value)
	case int64:
		return PackInt64(writer, _value)
	case int:
		return PackInt(writer, _value)
	case float32:
		return PackFloat32(writer, _value)
	case float64:
		return PackFloat64(writer, _value)
	case []byte:
		return PackBytes(writer, _value)
	case []uint16:
		return PackUint16Array(writer, _value)
	case []uint32:
		return PackUint32Array(writer, _value)
	case []uint64:
		return PackUint64Array(writer, _value)
	case []uint:
		return PackUintArray(writer, _value)
	case []int8:
		return PackInt8Array(writer, _value)
	case []int16:
		return PackInt16Array(writer, _value)
	case []int32:
		return PackInt32Array(writer, _value)
	case []int64:
		return PackInt64Array(writer, _value)
	case []int:
		return PackIntArray(writer, _value)
	case []float32:
		return PackFloat32Array(writer, _value)
	case []float64:
		return PackFloat64Array(writer, _value)
	case string:
		return PackBytes(writer, []byte(_value))
	default:
		return PackValue(writer, reflect.ValueOf(value))
	}
	return 0, nil // never get here
}
