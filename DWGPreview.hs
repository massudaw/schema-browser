{-# LANGUAGE TupleSections #-}
module DWGPreview where
import qualified Data.ByteString.Lazy as BS
import Data.Maybe
import Data.Binary
import Data.Monoid
import Data.Binary.Get
import Data.Binary.Put

preview i =
  let parser  = do
        skip 13
        l <- getWord32host
        seekf (16 + l )
        size <- getWord32host
        r <- bytesRead
        return . runGet (do
          bytCnt <- getWord8
          sequence $ replicate (fromIntegral $  bytCnt ) (  do
            imageCode <- getWord8
            imageHeaderStart <- getWord32host
            imageHeaderSize <- getWord32host
            r <- bytesRead
            case  imageCode of
              2-> do
                skip 80
                image <- getLazyByteString (fromIntegral imageHeaderSize)
                size <-  return $ runGet (do
                    skip 0xE
                    biBitCount <- getWord16host
                    skip 4
                    biSizeImage <- getWord32host
                    let color = if (biBitCount < 9) then  4 * 2^biBitCount else  0
                    return (biBitCount,biSizeImage,color)
                  ) image
                return  $ Just $ Left (size,image)

              6 -> do
                skip 80
                Just . Right  <$> getLazyByteString (fromIntegral imageHeaderSize)
              1 -> return Nothing -- return (Right (imageHeaderStart,imageHeaderSize))
              i -> error ("invalid value " <> show i) ) )=<<  (getLazyByteString (fromIntegral size))





  in case last (catMaybes ( runGet parser i)) of
    Left ((biBitCount,biSizeImage,colorTableSize),image) ->  Left $ runPut $do
        putWord8 0x42
        putWord8 0x4D
        putWord32host (54 +colorTableSize + biSizeImage)
        putWord16host 0
        putWord16host 0
        putWord32host (54 + colorTableSize)
        putLazyByteString image
    Right v -> Right v

seekf x = do
  r <- bytesRead
  let diff = fromIntegral x - ( fromIntegral r)
  skip (diff )




