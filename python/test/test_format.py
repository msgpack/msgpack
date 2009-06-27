from unittest import TestCase, main
from msgpack import packs, unpacks

class TestFormat(TestCase):
    def __check(self, obj, expected_packed):
        packed = packs(obj)
        self.assertEqual(packed, expected_packed)
        unpacked = unpacks(packed)
        self.assertEqual(unpacked, obj)

    def testSimpleValues(self):
        self.__check(None, '\xc0')
        self.__check(True, '\xc3')
        self.__check(False, '\xc2')
        self.__check(
                [None, False, True],
                '\x93\xc0\xc2\xc3'
                )

    def testFixnum(self):
        self.__check(
                [[0,64,127], [-32,-16,-1]],
                "\x92\x93\x00\x40\x7f\x93\xe0\xf0\xff"
                )
    
    def testFixArray(self):
        self.__check(
                [[],[[None]]],
                "\x92\x90\x91\x91\xc0"
                )

    def testFixRaw(self):
        self.__check(
                ["", "a", "bc", "def"],
                "\x94\xa0\xa1a\xa2bc\xa3def"
                )
        pass

    def testFixMap(self):
        self.__check(
                {False: {None: None}, True:{None:{}}},
                "\x82\xc2\x81\xc0\xc0\xc3\x81\xc0\x80"
                )
        pass


class TestUnpack(TestCase):
    def __check(self, packed, obj):
        self.assertEqual(unpacks(packed), obj)

    def testuint(self):
        self.__check(
                 "\x99\xcc\x00\xcc\x80\xcc\xff\xcd\x00\x00\xcd\x80\x00"
                 "\xcd\xff\xff\xce\x00\x00\x00\x00\xce\x80\x00\x00\x00"
                 "\xce\xff\xff\xff\xff",
                 [0, 128, 255, 0, 32768, 65535, 0,
                     2147483648, 4294967295],
                 )




if __name__ == '__main__':
    main()
