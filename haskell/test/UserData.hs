{-# Language TemplateHaskell #-}

import Data.MessagePack

data T
  = A Int String
  | B Double
  deriving (Show, Eq)

deriveObject ''T

data U
  = C { c1 :: Int, c2 :: String }
  | D { d1 :: Double }
  deriving (Show, Eq)

deriveObject ''U

data V
  = E String | F
  deriving (Show, Eq)

deriveObject ''V

test :: (OBJECT a, Show a, Eq a) => a -> IO ()
test v = do
  let bs = pack v
  print bs
  print (unpack bs == v)

  let oa = toObject v
  print oa
  print (fromObject oa == v)

main :: IO ()
main = do
  test $ A 123 "hoge"
  test $ B 3.14
  test $ C 123 "hoge"
  test $ D 3.14
  test $ E "hello"
  test $ F
  return ()
