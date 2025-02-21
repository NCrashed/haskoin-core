{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : Haskoin.Network.Bloom
-- Copyright   : No rights reserved
-- License     : MIT
-- Maintainer  : jprupp@protonmail.ch
-- Stability   : experimental
-- Portability : POSIX
--
-- Bloom filters are used to reduce data transfer when synchronizing thin cients.
-- When bloom filters are used a client will obtain filtered blocks that only
-- contain transactions that pass the bloom filter. Transactions announced via inv
-- messages also pass the filter.
module Haskoin.Network.Bloom
  ( -- * Bloom Filters
    BloomFlags (..),
    BloomFilter (..),
    FilterLoad (..),
    FilterAdd (..),
    bloomCreate,
    bloomInsert,
    bloomContains,
    isBloomValid,
    isBloomEmpty,
    isBloomFull,
    acceptsFilters,
    bloomRelevantUpdate,
  )
where

import Control.DeepSeq
import Control.Monad (forM_, replicateM)
import Crypto.Secp256k1 (Ctx)
import Data.Binary (Binary (..))
import Data.Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Bytes.Get
import Data.Bytes.Put
import Data.Bytes.Serial
import Data.Foldable qualified as F
import Data.Hash.Murmur (murmur3)
import Data.List (foldl')
import Data.Sequence qualified as S
import Data.Serialize (Serialize (..))
import Data.Word
import GHC.Generics (Generic)
import Haskoin.Network.Common
import Haskoin.Script.Standard
import Haskoin.Transaction.Common
import Haskoin.Util.Marshal

-- | 20,000 items with fp rate < 0.1% or 10,000 items and <0.0001%
maxBloomSize :: Int
maxBloomSize = 36000

maxHashFuncs :: Word32
maxHashFuncs = 50

ln2Squared :: Double
ln2Squared = 0.4804530139182014246671025263266649717305529515945455

ln2 :: Double
ln2 = 0.6931471805599453094172321214581765680755001343602552

bitMask :: [Word8]
bitMask = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80]

-- | The bloom flags are used to tell the remote peer how to auto-update
-- the provided bloom filter.
data BloomFlags
  = -- | never update
    BloomUpdateNone
  | -- | auto-update on all outputs
    BloomUpdateAll
  | -- | auto-update on pay-to-pubkey or pay-to-multisig (default)
    BloomUpdateP2PubKeyOnly
  deriving (Eq, Show, Read, Generic, NFData)

instance Serial BloomFlags where
  deserialize = go =<< getWord8
    where
      go 0 = return BloomUpdateNone
      go 1 = return BloomUpdateAll
      go 2 = return BloomUpdateP2PubKeyOnly
      go _ = fail "BloomFlags get: Invalid bloom flag"

  serialize f = putWord8 $ case f of
    BloomUpdateNone -> 0
    BloomUpdateAll -> 1
    BloomUpdateP2PubKeyOnly -> 2

instance Binary BloomFlags where
  get = deserialize
  put = serialize

instance Serialize BloomFlags where
  get = deserialize
  put = serialize

-- | A bloom filter is a probabilistic data structure that SPV clients send to
-- other peers to filter the set of transactions received from them. Bloom
-- filters can have false positives but not false negatives. Some transactions
-- that pass the filter may not be relevant to the receiving peer. By
-- controlling the false positive rate, SPV nodes can trade off bandwidth
-- versus privacy.
data BloomFilter = BloomFilter
  { -- | bloom filter data
    array :: !(S.Seq Word8),
    -- | number of hash functions for this filter
    functions :: !Word32,
    -- | hash function random nonce
    tweak :: !Word32,
    -- | bloom filter auto-update flags
    flags :: !BloomFlags
  }
  deriving (Eq, Show, Read, Generic, NFData)

instance Serial BloomFilter where
  deserialize =
    BloomFilter
      <$> (S.fromList <$> (readDat =<< deserialize))
      <*> getWord32le
      <*> getWord32le
      <*> deserialize
    where
      readDat (VarInt len) = replicateM (fromIntegral len) getWord8

  serialize BloomFilter {..} = do
    putVarInt $ S.length array
    mapM_ putWord8 (F.toList array)
    putWord32le functions
    putWord32le tweak
    serialize flags

instance Binary BloomFilter where
  put = serialize
  get = deserialize

instance Serialize BloomFilter where
  put = serialize
  get = deserialize

-- | Set a new bloom filter on the peer connection.
newtype FilterLoad = FilterLoad {filterLoad :: BloomFilter}
  deriving (Eq, Show, Read, Generic)
  deriving newtype (NFData)

instance Serial FilterLoad where
  deserialize = FilterLoad <$> deserialize
  serialize (FilterLoad f) = serialize f

instance Binary FilterLoad where
  put = serialize
  get = deserialize

instance Serialize FilterLoad where
  put = serialize
  get = deserialize

-- | Add the given data element to the connections current filter without
-- requiring a completely new one to be set.
newtype FilterAdd = FilterAdd {getFilterAdd :: ByteString}
  deriving (Eq, Show, Read, Generic)
  deriving newtype (NFData)

instance Serial FilterAdd where
  deserialize = do
    (VarInt len) <- deserialize
    dat <- getByteString $ fromIntegral len
    return $ FilterAdd dat

  serialize (FilterAdd bs) = do
    putVarInt $ BS.length bs
    putByteString bs

instance Binary FilterAdd where
  put = serialize
  get = deserialize

instance Serialize FilterAdd where
  put = serialize
  get = deserialize

-- | Build a bloom filter that will provide the given false positive rate when
-- the given number of elements have been inserted.
bloomCreate ::
  -- | number of elements
  Int ->
  -- | false positive rate
  Double ->
  -- | random nonce (tweak) for the hash function
  Word32 ->
  -- | bloom filter flags
  BloomFlags ->
  -- | bloom filter
  BloomFilter
bloomCreate numElem fpRate =
  BloomFilter (S.replicate bloomSize 0) numHashF
  where
    -- Bloom filter size in bytes
    bloomSize = truncate $ min a b / 8
    -- Suggested size in bits
    a = -1 / ln2Squared * fromIntegral numElem * log fpRate
    -- Maximum size in bits
    b = fromIntegral $ maxBloomSize * 8
    numHashF = truncate $ min c (fromIntegral maxHashFuncs)
    -- Suggested number of hash functions
    c = fromIntegral bloomSize * 8 / fromIntegral numElem * ln2

bloomHash :: BloomFilter -> Word32 -> ByteString -> Word32
bloomHash b hashNum bs =
  murmur3 seed bs `mod` (fromIntegral (S.length (array b)) * 8)
  where
    seed = hashNum * 0xfba4c795 + tweak b

-- | Insert arbitrary data into a bloom filter. Returns the new bloom filter
-- containing the new data.
bloomInsert ::
  -- | Original bloom filter
  BloomFilter ->
  -- | New data to insert
  ByteString ->
  -- | Bloom filter containing the new data
  BloomFilter
bloomInsert b bs
  | isBloomFull b = b
  | otherwise = b {array = dat}
  where
    idxs = map (\i -> bloomHash b i bs) [0 .. functions b - 1]
    upd s i =
      S.adjust
        (.|. bitMask !! fromIntegral (7 .&. i))
        (fromIntegral $ i `shiftR` 3)
        s
    dat = foldl upd (array b) idxs

-- | Tests if some arbitrary data matches the filter. This can be either because
-- the data was inserted into the filter or because it is a false positive.
bloomContains ::
  -- | Bloom filter
  BloomFilter ->
  -- | Data that will be checked against the given bloom filter
  ByteString ->
  -- | Returns True if the data matches the filter
  Bool
bloomContains b bs
  | isBloomFull b = True
  | isBloomEmpty b = False
  | otherwise = all isSet idxs
  where
    s = array b
    idxs = map (\i -> bloomHash b i bs) [0 .. functions b - 1]
    isSet i =
      S.index s (fromIntegral $ i `shiftR` 3)
        .&. (bitMask !! fromIntegral (7 .&. i))
        /= 0

-- | Checks if any of the outputs of a tx is in the current bloom filter.
-- If it is, add the txid and vout as an outpoint (i.e. so that
-- a future tx that spends the output won't be missed).
bloomRelevantUpdate ::
  Ctx ->
  -- | Bloom filter
  BloomFilter ->
  -- | Tx that may (or may not) have relevant outputs
  Tx ->
  -- | Returns an updated bloom filter adding relevant output
  Maybe BloomFilter
bloomRelevantUpdate ctx b tx
  | isBloomFull b || isBloomEmpty b = Nothing
  | flags b == BloomUpdateNone = Nothing
  | not (null matchOuts) = Just $ foldl' addRelevant b matchOuts
  | otherwise = Nothing
  where
    -- TxHash if we end up inserting an outpoint

    h = txHash tx
    -- Decode the scriptOutpus and add vOuts in case we make them outpoints
    decodedOutputScripts = traverse (unmarshal ctx . txOutScript) (txOutputs tx)
    err = error "Error Decoding output script"
    idxOutputScripts = either (const err) (zip [0 ..]) decodedOutputScripts
    -- Check if any txOuts were contained in the bloom filter
    matchFilter =
      filter (\(_, op) -> any (bloomContains b) (encodeScriptOut op))
    matchOuts = matchFilter idxOutputScripts
    addRelevant :: BloomFilter -> (Word32, ScriptOutput) -> BloomFilter
    addRelevant bf (id', scriptOut) =
      case (flags b, scriptType) of
        -- We filtered out BloomUpdateNone so we insert any PayPk or PayMulSig

        (_, True) -> bloomInsert bf outpoint
        (BloomUpdateAll, _) -> bloomInsert bf outpoint
        _ -> error "Error Updating Bloom Filter with relevant outpoint"
      where
        outpoint = runPutS $ serialize $ OutPoint {hash = h, index = id'}
        scriptType = (\s -> isPayPK s || isPayMulSig s) scriptOut
    -- Encodes a scriptOutput so it can be checked agains the Bloom Filter
    encodeScriptOut :: ScriptOutput -> [ByteString]
    encodeScriptOut (PayPK pk) =
      return $ marshal ctx pk
    encodeScriptOut (PayPKHash ph) =
      return . runPutS $ serialize ph
    encodeScriptOut (PayMulSig outputMuSig _) =
      map (marshal ctx) outputMuSig
    encodeScriptOut (PayScriptHash sh) =
      return . runPutS $ serialize sh
    encodeScriptOut (PayWitnessPKHash ph) =
      return . runPutS $ serialize ph
    encodeScriptOut (PayWitnessScriptHash sh) =
      return . runPutS $ serialize sh
    encodeScriptOut (PayWitness _ wd) =
      return wd
    encodeScriptOut (DataCarrier dat) =
      return dat

-- | Returns True if the filter is empty (all bytes set to 0x00)
isBloomEmpty :: BloomFilter -> Bool
isBloomEmpty b = all (== 0x00) $ F.toList $ array b

-- | Returns True if the filter is full (all bytes set to 0xff)
isBloomFull :: BloomFilter -> Bool
isBloomFull b = all (== 0xff) $ F.toList $ array b

-- | Tests if a given bloom filter is valid.
isBloomValid ::
  -- | Bloom filter to test
  BloomFilter ->
  -- | True if the given filter is valid
  Bool
isBloomValid BloomFilter {..} =
  S.length array <= maxBloomSize && functions <= maxHashFuncs

-- | Does the peer with these version services accept bloom filters?
acceptsFilters :: Word64 -> Bool
acceptsFilters srv = srv .&. (1 `shiftL` 2) /= 0
