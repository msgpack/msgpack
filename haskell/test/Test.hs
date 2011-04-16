import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

import Control.Monad
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy.Char8 as L
import Data.MessagePack

instance Arbitrary a => Arbitrary (Assoc a) where
  arbitrary = liftM Assoc arbitrary

mid :: (Packable a, Unpackable a) => a -> a
mid = unpack . pack

prop_mid_int a = a == mid a
  where types = a :: Int
prop_mid_nil a = a == mid a
  where types = a :: ()
prop_mid_bool a = a == mid a
  where types = a :: Bool
prop_mid_double a = a == mid a
  where types = a :: Double
prop_mid_string a = a == mid a
  where types = a :: String
prop_mid_bytestring a = B.pack a == mid (B.pack a)
  where types = a :: String
prop_mid_lazy_bytestring a = (L.pack a) == mid (L.pack a)
  where types = a :: String
prop_mid_array_int a = a == mid a
  where types = a :: [Int]
prop_mid_array_string a = a == mid a
  where types = a :: [String]
prop_mid_pair2 a = a == mid a
  where types = a :: (Int, Int)
prop_mid_pair3 a = a == mid a
  where types = a :: (Int, Int, Int)
prop_mid_pair4 a = a == mid a
  where types = a :: (Int, Int, Int, Int)
prop_mid_pair5 a = a == mid a
  where types = a :: (Int, Int, Int, Int, Int)
prop_mid_list_int_double a = a == mid a
  where types = a :: [(Int, Double)]
prop_mid_list_string_string a = a == mid a
  where types = a :: [(String, String)]
prop_mid_map_string_int a = a == mid a
  where types = a :: Assoc [(String,Int)]

tests =
  [ testGroup "simple"
    [ testProperty "int" prop_mid_int
    , testProperty "nil" prop_mid_nil
    , testProperty "bool" prop_mid_bool
    , testProperty "double" prop_mid_double
    , testProperty "string" prop_mid_string
    , testProperty "bytestring" prop_mid_bytestring
    , testProperty "lazy-bytestring" prop_mid_lazy_bytestring
    , testProperty "[int]" prop_mid_array_int
    , testProperty "[string]" prop_mid_array_string
    , testProperty "(int, int)" prop_mid_pair2
    , testProperty "(int, int, int)" prop_mid_pair3
    , testProperty "(int, int, int, int)" prop_mid_pair4
    , testProperty "(int, int, int, int, int)" prop_mid_pair5
    , testProperty "[(int, double)]" prop_mid_list_int_double
    , testProperty "[(string, string)]" prop_mid_list_string_string
    , testProperty "Assoc [(string, int)]" prop_mid_map_string_int
    ]
  ]

main = defaultMain tests
