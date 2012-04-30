package msgpack

import (
	"io"
	"reflect"
	"strconv"
	"unsafe"
)

func readByte(reader io.Reader) (v uint8, err error) {
	data := [1]byte{}
	_, e := reader.Read(data[0:])
	if e != nil {
		return 0, e
	}
	return data[0], nil
}

func readUint16(reader io.Reader) (v uint16, n int, err error) {
	data := [2]byte{}
	n, e := reader.Read(data[0:])
	if e != nil {
		return 0, n, e
	}
	return (uint16(data[0]) << 8) | uint16(data[1]), n, nil
}

func readUint32(reader io.Reader) (v uint32, n int, err error) {
	data := [4]byte{}
	n, e := reader.Read(data[0:])
	if e != nil {
		return 0, n, e
	}
	return (uint32(data[0]) << 24) | (uint32(data[1]) << 16) | (uint32(data[2]) << 8) | uint32(data[3]), n, nil
}

func readUint64(reader io.Reader) (v uint64, n int, err error) {
	data := [8]byte{}
	n, e := reader.Read(data[0:])
	if e != nil {
		return 0, n, e
	}
	return (uint64(data[0]) << 56) | (uint64(data[1]) << 48) | (uint64(data[2]) << 40) | (uint64(data[3]) << 32) | (uint64(data[4]) << 24) | (uint64(data[5]) << 16) | (uint64(data[6]) << 8) | uint64(data[7]), n, nil
}

func readInt16(reader io.Reader) (v int16, n int, err error) {
	data := [2]byte{}
	n, e := reader.Read(data[0:])
	if e != nil {
		return 0, n, e
	}
	return (int16(data[0]) << 8) | int16(data[1]), n, nil
}

func readInt32(reader io.Reader) (v int32, n int, err error) {
	data := [4]byte{}
	n, e := reader.Read(data[0:])
	if e != nil {
		return 0, n, e
	}
	return (int32(data[0]) << 24) | (int32(data[1]) << 16) | (int32(data[2]) << 8) | int32(data[3]), n, nil
}

func readInt64(reader io.Reader) (v int64, n int, err error) {
	data := [8]byte{}
	n, e := reader.Read(data[0:])
	if e != nil {
		return 0, n, e
	}
	return (int64(data[0]) << 56) | (int64(data[1]) << 48) | (int64(data[2]) << 40) | (int64(data[3]) << 32) | (int64(data[4]) << 24) | (int64(data[5]) << 16) | (int64(data[6]) << 8) | int64(data[7]), n, nil
}

func unpackArray(reader io.Reader, nelems uint) (v reflect.Value, n int, err error) {
	retval := make([]interface{}, nelems)
	nbytesread := 0
	var i uint
	for i = 0; i < nelems; i++ {
		v, n, e := Unpack(reader)
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		retval[i] = v.Interface()
	}
	return reflect.ValueOf(retval), nbytesread, nil
}

func unpackArrayReflected(reader io.Reader, nelems uint) (v reflect.Value, n int, err error) {
	retval := make([]reflect.Value, nelems)
	nbytesread := 0
	var i uint
	for i = 0; i < nelems; i++ {
		v, n, e := UnpackReflected(reader)
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		retval[i] = v
	}
	return reflect.ValueOf(retval), nbytesread, nil
}

func unpackMap(reader io.Reader, nelems uint) (v reflect.Value, n int, err error) {
	retval := make(map[interface{}]interface{})
	nbytesread := 0
	var i uint
	for i = 0; i < nelems; i++ {
		k, n, e := Unpack(reader)
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		v, n, e := Unpack(reader)
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		retval[k.Interface()] = v.Interface()
	}
	return reflect.ValueOf(retval), nbytesread, nil
}

func unpackMapReflected(reader io.Reader, nelems uint) (v reflect.Value, n int, err error) {
	retval := make(map[interface{}]reflect.Value)
	nbytesread := 0
	var i uint
	for i = 0; i < nelems; i++ {
		k, n, e := UnpackReflected(reader)
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		v, n, e := UnpackReflected(reader)
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		retval[k] = v
	}
	return reflect.ValueOf(retval), nbytesread, nil
}

func unpack(reader io.Reader, reflected bool) (v reflect.Value, n int, err error) {
	var retval reflect.Value
	var nbytesread int = 0

	c, e := readByte(reader)
	if e != nil {
		return reflect.Value{}, 0, e
	}
	nbytesread += 1
	if c < 0x80 || c >= 0xe0 {
		retval = reflect.ValueOf(int8(c))
	} else if c >= 0x80 && c <= 0x8f {
		if reflected {
			retval, n, e = unpackMapReflected(reader, uint(c&0xf))
		} else {
			retval, n, e = unpackMap(reader, uint(c&0xf))
		}
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		nbytesread += n
	} else if c >= 0x90 && c <= 0x9f {
		if reflected {
			retval, n, e = unpackArrayReflected(reader, uint(c&0xf))
		} else {
			retval, n, e = unpackArray(reader, uint(c&0xf))
		}
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		nbytesread += n
	} else if c >= 0xa0 && c <= 0xbf {
		data := make([]byte, c&0x1f)
		n, e := reader.Read(data)
		nbytesread += n
		if e != nil {
			return reflect.Value{}, nbytesread, e
		}
		retval = reflect.ValueOf(data)
	} else {
		switch c {
		case 0xc0:
			retval = reflect.ValueOf(nil)
		case 0xc2:
			retval = reflect.ValueOf(false)
		case 0xc3:
			retval = reflect.ValueOf(true)
		case 0xca:
			data, n, e := readUint32(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(*(*float32)(unsafe.Pointer(&data)))
		case 0xcb:
			data, n, e := readUint64(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(*(*float64)(unsafe.Pointer(&data)))
		case 0xcc:
			data, e := readByte(reader)
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(uint8(data))
			nbytesread += 1
		case 0xcd:
			data, n, e := readUint16(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xce:
			data, n, e := readUint32(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xcf:
			data, n, e := readUint64(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xd0:
			data, e := readByte(reader)
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(int8(data))
			nbytesread += 1
		case 0xd1:
			data, n, e := readInt16(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xd2:
			data, n, e := readInt32(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xd3:
			data, n, e := readInt64(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xda:
			nbytestoread, n, e := readUint16(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			data := make([]byte, nbytestoread)
			n, e = reader.Read(data)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xdb:
			nbytestoread, n, e := readUint32(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			data := make([]byte, nbytestoread)
			n, e = reader.Read(data)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			retval = reflect.ValueOf(data)
		case 0xdc:
			nelemstoread, n, e := readUint16(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			if reflected {
				retval, n, e = unpackArrayReflected(reader, uint(nelemstoread))
			} else {
				retval, n, e = unpackArray(reader, uint(nelemstoread))
			}
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
		case 0xdd:
			nelemstoread, n, e := readUint32(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			if reflected {
				retval, n, e = unpackArrayReflected(reader, uint(nelemstoread))
			} else {
				retval, n, e = unpackArray(reader, uint(nelemstoread))
			}
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
		case 0xde:
			nelemstoread, n, e := readUint16(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			if reflected {
				retval, n, e = unpackMapReflected(reader, uint(nelemstoread))
			} else {
				retval, n, e = unpackMap(reader, uint(nelemstoread))
			}
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
		case 0xdf:
			nelemstoread, n, e := readUint32(reader)
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
			if reflected {
				retval, n, e = unpackMapReflected(reader, uint(nelemstoread))
			} else {
				retval, n, e = unpackMap(reader, uint(nelemstoread))
			}
			nbytesread += n
			if e != nil {
				return reflect.Value{}, nbytesread, e
			}
		default:
			panic("unsupported code: " + strconv.Itoa(int(c)))
		}
	}
	return retval, nbytesread, nil
}

// Reads a value from the reader, unpack and returns it.
func Unpack(reader io.Reader) (v reflect.Value, n int, err error) {
	return unpack(reader, false)
}

// Reads unpack a value from the reader, unpack and returns it.  When the
// value is an array or map, leaves the elements wrapped by corresponding
// wrapper objects defined in reflect package.
func UnpackReflected(reader io.Reader) (v reflect.Value, n int, err error) {
	return unpack(reader, true)
}
