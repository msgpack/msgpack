import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck

import Control.Monad
import qualified Data.ByteString.Char8 as B
import Data.MessagePack

mid :: (ObjectGet a, ObjectPut a) => a -> a
mid = unpack . pack

prop_mid_int a = a == mid a
  where types = a :: Int
prop_mid_nil a = a == mid a
  where types = a :: ()
prop_mid_bool a = a == mid a
  where types = a :: Bool
prop_mid_double a = a == mid a
  where types = a :: Double
prop_mid_string a = a == B.unpack (mid (B.pack a))
  where types = a :: String
prop_mid_array_int a = a == mid a
  where types = a :: [Int]
prop_mid_array_string a = a == map B.unpack (mid (map B.pack a))
  where types = a :: [String]
prop_mid_map_int_double a = a == mid a
  where types = a :: [(Int, Double)]
prop_mid_map_string_string a = a == map (\(x, y) -> (B.unpack x, B.unpack y)) (mid (map (\(x, y) -> (B.pack x, B.pack y)) a))
  where types = a :: [(String, String)]

tests =
  [ testGroup "simple"
    [ testProperty "int" prop_mid_int
    , testProperty "nil" prop_mid_nil
    , testProperty "bool" prop_mid_bool
    , testProperty "double" prop_mid_double
    , testProperty "string" prop_mid_string
    , testProperty "[int]" prop_mid_array_int
    , testProperty "[string]" prop_mid_array_string
    , testProperty "[(int, double)]" prop_mid_map_int_double
    , testProperty "[(string, string)]" prop_mid_map_string_string
    ]
  ]

main = defaultMain tests
