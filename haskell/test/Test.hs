import Control.Monad
import Data.MessagePack

{-
main = do
  sb <- newSimpleBuffer
  pc <- newPacker sb
  
  pack pc [(1,2),(2,3),(3::Int,4::Int)]
  pack pc [4,5,6::Int]
  pack pc "hoge"
  
  bs <- simpleBufferData sb
  print bs
  
  up <- newUnpacker defaultInitialBufferSize
  
  unpackerFeed up bs

  let f = do
        res <- unpackerExecute up
        when (res==1) $ do
          obj <- unpackerData up
          print obj
          f
  
  f

  return ()
-}

main = do
  bs <- packb [(1,2),(2,3),(3::Int,4::Int)]
  print bs
  dat <- unpackb bs
  print (dat :: Result [(Int, Int)])
