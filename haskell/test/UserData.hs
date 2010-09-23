{-# Language TemplateHaskell #-}

import Data.MessagePack
import Data.MessagePack.Derive

data T
  = A Int String
  | B Double
  deriving (Show)

$(deriveObject ''T)

data U
  = C { c1 :: Int, c2 :: String }
  | D { d1 :: Double }
  deriving (Show)

$(deriveObject ''U)

main = do
  let bs = pack $ A 123 "hoge"
  print bs
  print (unpack bs :: T)
  let cs = pack $ B 3.14
  print cs
  print (unpack cs :: T)
  let oa = toObject $ A 123 "hoge"
  print oa
  print (fromObject oa :: T)
  let ob = toObject $ B 3.14
  print ob
  print (fromObject ob :: T)

  let ds = pack $ C 123 "hoge"
  print ds
  print (unpack ds :: U)
  let es = pack $ D 3.14
  print es
  print (unpack es :: U)
  let oc = toObject $ C 123 "hoge"
  print oc
  print (fromObject oc :: U)
  let od = toObject $ D 3.14
  print od
  print (fromObject od :: U)
