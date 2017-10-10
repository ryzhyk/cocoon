{-# LANGUAGE TypeSynonymInstances, TypeOperators, MultiParamTypeClasses, FunctionalDependencies, RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{-|

This module provides @Get@ values for parsing various 
IP packets and headers from ByteStrings into a byte-sequence-independent 
representation as Haskell datatypes. 

Warning: 

These are incomplete. The headers may not contain all the information
that the protocols specify. For example, the Haskell representation of an IP Header
only includes source and destination addresses and IP protocol number, even though
an IP packet has many more header fields. More seriously, an IP header may have an optional 
extra headers section after the destination address. We assume this is not present. If it is present, 
then the transport protocol header will not be directly after the destination address, but will be after 
these options. Therefore functions that assume this, such as the getExactMatch function below, will give 
incorrect results when applied to such IP packets. 

The Haskell representations of the headers for the transport protocols are similarly incomplete. 
Again, the Get instances for the transport protocols may not parse through the end of the 
transport protocol header. 

-}
module Network.Data.IPv4.IPPacket ( 
  -- * IP Packet 
  IPPacket
  , IPHeader(..)
  , DifferentiatedServicesCodePoint
  , FragOffset
  , IPProtocol
  , IPTypeOfService
  , TransportPort
  , ipProtocol
  , ipBodyLength
  , ipTypeTcp 
  , ipTypeUdp 
  , ipTypeIcmp
  , IPBody(..)
    
    -- * Parsers
  , getIPPacket
  , getIPHeader
  , ICMPHeader
  , ICMPType
  , ICMPCode
  , ICMPPacket
  , getICMPPacket
  , TCPHeader
  , TCPPortNumber
  , getTCPHeader
  , UDPPacket
  , UDPPortNumber
  , getUDPPacket
  , putIPPacket
  , putIPHeader
  , putICMPPacket
  ) where

import Network.Data.IPv4.IPAddress
-- import Network.Data.IPv4.DHCP
import Network.Data.IPv4.UDP
import Data.Bits
import Data.Word
import Data.Binary.Get
import Data.Binary.Put
import qualified Data.ByteString as B
import Control.Exception (assert)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Data.Tuple.Select

-- | An IP packet consists of a header and a body.
type IPPacket = (IPHeader, IPBody)

-- | An IP Header includes various information about the packet, including the type of payload it contains. 
-- Warning: this definition does not include every header field included in an IP packet. 
data IPHeader = IPHeader { ipSrcAddress  :: !IPAddress
                         , ipDstAddress  :: !IPAddress
                         , headerLength  :: !Int
                         , totalLength   :: !Int
                         , dscp          :: !DifferentiatedServicesCodePoint -- ^ differentiated services code point - 6 bit number
                         , ecn           :: !Word8 -- Explicit congestion notification (ECN); 2 bits.
                         , ttl           :: !Word8 -- ^ time-to-live.
                         , nwproto       :: !Word8
                         , ipChecksum    :: !Word16
                         , ident         :: !Word16
                         , flags         :: !Word16
                         }
                deriving (Read,Show,Eq,Generic,NFData)

type DifferentiatedServicesCodePoint = Word8
type FragOffset      = Word16
type IPProtocol      = Word8
type IPTypeOfService = Word8
type TransportPort   = Word16

ipProtocol :: IPBody -> IPProtocol
--ipProtocol (TCPInIP _ _) = ipTypeTcp
ipProtocol UDPInIP{}                     = ipTypeUdp
ipProtocol ICMPInIP{}                    = ipTypeIcmp
ipProtocol (UninterpretedIPBody proto _) = proto
{-# INLINE ipProtocol #-}

ipBodyLength :: IPHeader -> Int
ipBodyLength (IPHeader {..})
  = totalLength - (4 * headerLength)
{-# INLINE ipBodyLength #-}

ipTypeTcp, ipTypeUdp, ipTypeIcmp :: IPProtocol

ipTypeTcp  = 6
ipTypeUdp  = 17
ipTypeIcmp = 1

-- | The body of an IP packet can be either a TCP, UDP, ICMP or other packet. 
-- Packets other than TCP, UDP, ICMP are represented as unparsed @ByteString@ values.
data IPBody   = -- TCPInIP !TCPPortNumber !TCPPortNumber
                UDPInIP !UDPPacket
              | ICMPInIP !ICMPPacket
              | UninterpretedIPBody !IPProtocol B.ByteString
              deriving (Show,Eq,Generic,NFData)


getIPHeader :: Get IPHeader
getIPHeader = do 
  b1                 <- getWord8
  let version = shiftR b1 4
  assert (version == 4) $ do      
    diffServ           <- getWord8
    totalLen           <- getWord16be
    ident              <- getWord16be     -- ident
    flags              <- getWord16be     -- flagsAndFragOffset
    ttl                <- getWord8        -- ttl
    nwproto            <- getIPProtocol
    ipChecksum         <- getWord16be     -- hdrChecksum
    nwsrc              <- getIPAddress
    nwdst              <- getIPAddress
    let hdrLen = fromIntegral (b1 .&. 0x0f)
    skip (max 0 (4 * (hdrLen - 5)))
    return IPHeader { ipSrcAddress = nwsrc 
                    , ipDstAddress = nwdst 
                    , headerLength = hdrLen
                    , totalLength  = fromIntegral totalLen
                    , dscp         = shiftR diffServ 2
                    , ecn          = diffServ .&. 3
                    , ttl          = ttl
                    , nwproto      = nwproto
                    , ipChecksum   = ipChecksum
                    , ident        = ident
                    , flags        = flags
                    }
{-# INLINE getIPHeader #-}

getIPProtocol :: Get IPProtocol 
getIPProtocol = getWord8
{-# INLINE getIPProtocol #-}

getIPPacket :: Get IPPacket 
getIPPacket = getIPHeader >>= getIPBody 
{-# INLINE getIPPacket #-}

getIPBody :: IPHeader -> Get IPPacket
getIPBody hdr@(IPHeader {..})
  -- | nwproto == ipTypeTcp  = do (s,d) <- getTCPHeader (ipBodyLength hdr)
  --                              return (hdr, TCPInIP s d)
  | nwproto == ipTypeUdp  = do udp <- getUDPPacket $ ipBodyLength hdr
                               return (hdr, UDPInIP udp)
  | nwproto == ipTypeIcmp = do icmp <- getICMPPacket $ ipBodyLength hdr
                               return (hdr, ICMPInIP icmp)
  | otherwise             = do pl <- getByteString $ ipBodyLength hdr
                               return (hdr, UninterpretedIPBody nwproto pl)
{-# INLINE getIPBody #-}

-- ipChecksum_ :: IPHeader -> Word8 -> Word16
-- ipChecksum_ hdr nwproto = csum16 $ runPut $ putIPHeader hdr nwproto 0

{-
csum16 :: L.ByteString -> Word16
csum16 bs = complement $ x + y
  where
    x, y :: Word16
    x = fromIntegral (shiftR (z .&. 0xff00) 8)
    y = fromIntegral (z .&. 0x00ff)
    z :: Word32
    z = foldl (+) 0 ws
    ws :: [Word32]
    ws = runGet (sequence $ replicate (fromIntegral (L.length bs) `div` 4) getWord32be) bs
-}

putIPPacket :: IPPacket -> Put
putIPPacket (hdr, body) = do
  putIPHeader hdr $ ipChecksum hdr --(ipChecksum hdr nwproto)
  putIPBody (ipBodyLength hdr) body

putIPHeader :: IPHeader -> Word16 -> Put
putIPHeader (IPHeader {..}) chksum = do
  putWord8 b1
  putWord8 diffServ
  putWord16be $ fromIntegral totalLength
  putWord16be ident -- identification
  putWord16be flags -- flags and offset
  putWord8 ttl
  putWord8 nwproto
  putWord16be chksum
  putIPAddress ipSrcAddress
  putIPAddress ipDstAddress
  -- assume no options.
  where
    b1 = shiftL vERSION_4 4 .|. fromIntegral headerLength
    diffServ = shiftL dscp 2 .|. ecn

vERSION_4 :: Word8
vERSION_4 = 4

putIPBody :: Int -> IPBody -> Put
putIPBody _ (ICMPInIP icmp)           = putICMPPacket icmp $ sel3 $ fst icmp
putIPBody _ (UDPInIP p)               = putUDPPacket p
putIPBody _ (UninterpretedIPBody _ b) = putByteString b

-- Transport Header
type ICMPHeader = (ICMPType, ICMPCode, Word16)
type ICMPPacket = (ICMPHeader, B.ByteString)
type ICMPType = Word8
type ICMPCode = Word8

getICMPPacket :: Int -> Get ICMPPacket
getICMPPacket len = do
  icmp_type <- getWord8
  icmp_code <- getWord8
  check <- getWord16be
  bs <- getByteString $ len - 4
  return ((icmp_type, icmp_code, check), bs)
{-# INLINE getICMPPacket #-}

putICMPPacket :: ICMPPacket -> Word16 -> Put
putICMPPacket ((t, c, _), bs) check = do
    putWord8 t
    putWord8 c
    putWord16be check 
    putByteString bs

type TCPHeader  = (TCPPortNumber, TCPPortNumber)
type TCPPortNumber = Word16

getTCPHeader :: Int -> Get TCPHeader
getTCPHeader len = do 
  srcp <- getWord16be
  dstp <- getWord16be
  skip $ len - 4
  return (srcp,dstp)
{-# INLINE getTCPHeader #-}  
