module Network.Data.IPv4.UDP
       (
         UDPPacket
       , UDPPortNumber
       , getUDPPacket
       , putUDPPacket
       ) where

import Data.Binary.Get
import Data.Binary.Put
import Data.Word
import qualified Data.ByteString as BS

type UDPHeader     = (UDPPortNumber, UDPPortNumber, Word16, Word16)
type UDPPortNumber = Word16

type UDPPacket = (UDPHeader, BS.ByteString)

getUDPPacket :: Int -> Get UDPPacket
getUDPPacket len = do
    h <- getUDPHeader
    b <- getByteString $ len - 8
    return (h,b)

getUDPHeader :: Get UDPHeader
getUDPHeader = do 
  srcp <- getWord16be
  dstp <- getWord16be
  len  <- getWord16be 
  csum <- getWord16be 
  skip 4
  return (srcp, dstp, len, csum)
{-# INLINE getUDPHeader #-}  

putUDPHeader :: UDPHeader -> Put
putUDPHeader (sport, dport, len, csum) = do
    putWord16be sport
    putWord16be dport
    putWord16be len
    putWord16be csum

putUDPPacket :: UDPPacket -> Put
putUDPPacket (h, b) = do
    putUDPHeader h
    putByteString b
