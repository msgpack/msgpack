{-# Language TemplateHaskell #-}

import Data.MessagePack
import Data.MessagePack.Derive

data T
  = A Int String
  | B Double
  deriving (Show)

$(deriveObject ''T)

main = do
  let bs = pack $ A 123 "hoge"
  print bs
  print (unpack bs :: T)
  let cs = pack $ B 3.14
  print cs
  print (unpack cs :: T)
