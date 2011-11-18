{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

import Data.MessagePack

data T
  = A Int String
  | B Double
  deriving (Show, Eq)

deriveObject True ''T

data U
  = C { c1 :: Int, c2 :: String }
  | D { z1 :: Double }
  deriving (Show, Eq)

deriveObject True ''U

data V
  = E String | F
  deriving (Show, Eq)

deriveObject True ''V

data W a
  = G a String
  | H { hHoge :: Int, h_age :: a }
  deriving (Show, Eq)

deriveObject True ''W

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
  test $ G (E "hello") "world"
  test $ H 123 F
  return ()
