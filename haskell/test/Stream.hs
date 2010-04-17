import Control.Applicative
import qualified Data.ByteString as BS
import Data.MessagePack

main = do
  sb <- newSimpleBuffer
  pc <- newPacker sb
  pack pc [1,2,3::Int]
  pack pc True
  pack pc "hoge"
  bs <- simpleBufferData sb
  
  os <- unpackObjectsFromString bs
  mapM_ print os
