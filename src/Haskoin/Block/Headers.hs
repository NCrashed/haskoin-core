{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : Haskoin.Block.Headers
-- Copyright   : No rights reserved
-- License     : MIT
-- Maintainer  : jprupp@protonmail.ch
-- Stability   : experimental
-- Portability : POSIX
--
-- Block chain header synchronization and proof-of-work consensus functions.
module Haskoin.Block.Headers
  ( -- * Block Headers
    BlockNode (..),
    BlockHeaders (..),
    BlockWork,
    genesisNode,
    genesisBlock,
    isGenesis,
    chooseBest,

    -- ** Header Store
    parentBlock,
    getParents,
    getAncestor,
    splitPoint,
    connectBlocks,
    connectBlock,
    blockLocator,

    -- ** Header Memory Store
    HeaderMemory (..),
    ShortBlockHash,
    BlockMap,
    shortBlockHash,
    initialChain,
    genesisMap,

    -- ** Helper Functions
    appendBlocks,
    validBlock,
    validCP,
    afterLastCP,
    bip34,
    validVersion,
    lastNoMinDiff,
    nextWorkRequired,
    nextEdaWorkRequired,
    nextDaaWorkRequired,
    nextAsertWorkRequired,
    computeAsertBits,
    computeTarget,
    getSuitableBlock,
    nextPowWorkRequired,
    calcNextWork,
    isValidPOW,
    blockPOW,
    headerWork,
    diffInterval,
    blockLocatorNodes,
    mineBlock,
    computeSubsidy,
    mtp,
    firstGreaterOrEqual,
    lastSmallerOrEqual,
  )
where

import Control.Applicative ((<|>))
import Control.DeepSeq
import Control.Monad (guard, mzero, unless, when)
import Control.Monad.Except (ExceptT (..), runExceptT, throwError)
import Control.Monad.State.Strict as State (StateT, get, gets, lift, modify)
import Control.Monad.Trans.Maybe
import Data.Binary (Binary (..))
import Data.Bits (shiftL, shiftR, (.&.))
import Data.ByteString qualified as B
import Data.ByteString.Short (ShortByteString, fromShort, toShort)
import Data.Bytes.Get
import Data.Bytes.Put
import Data.Bytes.Serial
import Data.Function (on)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.Hashable
import Data.List (sort, sortBy)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Serialize (Serialize (..))
import Data.Typeable (Typeable)
import Data.Word (Word32, Word64)
import GHC.Generics (Generic)
import Haskoin.Block.Common
import Haskoin.Crypto
import Haskoin.Network.Data
import Haskoin.Transaction.Genesis
import Haskoin.Util

-- | Short version of the block hash. Uses the good end of the hash (the part
-- that doesn't have a long string of zeroes).
type ShortBlockHash = Word64

-- | Memory-based map to a serialized 'BlockNode' data structure.
-- 'ShortByteString' is used to avoid memory fragmentation and make the data
-- structure compact.
type BlockMap = HashMap ShortBlockHash ShortByteString

-- | Represents accumulated work in the block chain so far.
type BlockWork = Integer

-- | Data structure representing a block header and its position in the
-- block chain.
data BlockNode = BlockNode
  { nodeHeader :: !BlockHeader,
    height :: !BlockHeight,
    -- | accumulated work so far
    work :: !BlockWork,
    -- | skip magic block hash
    nodeSkip :: !BlockHash
  }
  deriving (Show, Read, Generic, Hashable, NFData)

instance Serial BlockNode where
  deserialize = do
    nodeHeader <- deserialize
    height <- getWord32le
    work <- getInteger
    if height == 0
      then do
        let nodeSkip = headerHash nodeHeader
        return BlockNode {..}
      else do
        nodeSkip <- deserialize
        return BlockNode {..}
  serialize bn = do
    serialize $ nodeHeader bn
    putWord32le $ height bn
    putInteger $ work bn
    case height bn of
      0 -> return ()
      _ -> serialize $ nodeSkip bn

instance Serialize BlockNode where
  put = serialize
  get = deserialize

instance Binary BlockNode where
  put = serialize
  get = deserialize

instance Eq BlockNode where
  (==) = (==) `on` nodeHeader

instance Ord BlockNode where
  compare = compare `on` height

-- | Memory-based header tree.
data HeaderMemory = HeaderMemory
  { blocks :: !BlockMap,
    best :: !BlockNode
  }
  deriving (Eq, Typeable, Show, Read, Generic, Hashable, NFData)

-- | Typeclass for block header chain storage monad.
class (Monad m) => BlockHeaders m where
  -- | Add a new 'BlockNode' to the chain. Does not validate.
  addBlockHeader :: BlockNode -> m ()

  -- | Get a 'BlockNode' associated with a 'BlockHash'.
  getBlockHeader :: BlockHash -> m (Maybe BlockNode)

  -- | Locate the 'BlockNode' for the highest block in the chain
  getBestBlockHeader :: m BlockNode

  -- | Set the highest block in the chain.
  setBestBlockHeader :: BlockNode -> m ()

  -- | Add a continuous bunch of block headers the chain. Does not validate.
  addBlockHeaders :: [BlockNode] -> m ()
  addBlockHeaders = mapM_ addBlockHeader

instance (Monad m) => BlockHeaders (StateT HeaderMemory m) where
  addBlockHeader = modify . addBlockHeaderMemory
  getBlockHeader bh = getBlockHeaderMemory bh <$> State.get
  getBestBlockHeader = gets best
  setBestBlockHeader bn = modify $ \s -> s {best = bn}

-- | Initialize memory-based chain.
initialChain :: Network -> HeaderMemory
initialChain net =
  HeaderMemory
    { blocks = genesisMap net,
      best = genesisNode net
    }

-- | Initialize map for memory-based chain.
genesisMap :: Network -> BlockMap
genesisMap net =
  HashMap.singleton
    (shortBlockHash (headerHash $ genesisHeader net))
    (toShort (runPutS (serialize (genesisNode net))))

-- | Add block header to memory block map.
addBlockHeaderMemory :: BlockNode -> HeaderMemory -> HeaderMemory
addBlockHeaderMemory bn s = s {blocks = addBlockToMap bn $ blocks s}

-- | Get block header from memory block map.
getBlockHeaderMemory :: BlockHash -> HeaderMemory -> Maybe BlockNode
getBlockHeaderMemory bh s = do
  bs <- shortBlockHash bh `HashMap.lookup` blocks s
  eitherToMaybe . runGetS deserialize $ fromShort bs

-- | Calculate short block hash taking eight non-zero bytes from the 16-byte
-- hash. This function will take the bytes that are not on the zero-side of the
-- hash, making colissions between short block hashes difficult.
shortBlockHash :: BlockHash -> ShortBlockHash
shortBlockHash =
  either error id . runGetS deserialize . B.take 8 . runPutS . serialize

-- | Add a block to memory-based block map.
addBlockToMap :: BlockNode -> BlockMap -> BlockMap
addBlockToMap node =
  HashMap.insert
    (shortBlockHash $ headerHash $ nodeHeader node)
    (toShort $ runPutS $ serialize node)

-- | Get the ancestor of the provided 'BlockNode' at the specified
-- 'BlockHeight'.
getAncestor ::
  (BlockHeaders m) =>
  BlockHeight ->
  BlockNode ->
  m (Maybe BlockNode)
getAncestor h node
  | h > height node = return Nothing
  | otherwise = go node
  where
    e1 = error "Could not get current walk skip"
    e2 = error "Could not get previous walk skip"
    go walk
      | height walk > h =
          let height_b = skipHeight (height walk)
              height_a = skipHeight (height walk - 1)
              not_genesis = not (isGenesis walk)
              is_b = height_b == h
              below_b = height_b > h
              at_or_below_a = h <= height_a
              far_enough = height_b - 2 > height_a && at_or_below_a
              recurse_b = below_b && not far_enough
              cond = not_genesis && (is_b || recurse_b)
           in if cond
                then do
                  walk' <- fromMaybe e1 <$> getBlockHeader (nodeSkip walk)
                  go walk'
                else do
                  walk' <- fromMaybe e2 <$> getBlockHeader (prev . nodeHeader $ walk)
                  go walk'
      | otherwise = return $ Just walk

-- | Is the provided 'BlockNode' the Genesis block?
isGenesis :: BlockNode -> Bool
isGenesis BlockNode {height = 0} = True
isGenesis _ = False

-- | Build the genesis 'BlockNode' for the supplied 'Network'.
genesisNode :: Network -> BlockNode
genesisNode net =
  BlockNode
    { nodeHeader = genesisHeader net,
      height = 0,
      work = headerWork $ genesisHeader net,
      nodeSkip = headerHash $ genesisHeader net
    }

-- | Validate a list of continuous block headers and import them to the
-- block chain. Return 'Left' on failure with error information.
connectBlocks ::
  (BlockHeaders m) =>
  Network ->
  -- | current time
  Timestamp ->
  [BlockHeader] ->
  m (Either String [BlockNode])
connectBlocks _ _ [] = return $ Right []
connectBlocks net t bhs@(bh : _) =
  runExceptT $ do
    unless (chained bhs) $
      throwError "Blocks to connect do not form a chain"
    par <-
      maybeToExceptT
        "Could not get parent block"
        (MaybeT (parentBlock bh))
    pars <- lift $ getParents 10 par
    bb <- lift getBestBlockHeader
    go par [] bb par pars bhs >>= \case
      bns@(bn : _) -> do
        lift $ addBlockHeaders bns
        let bb' = chooseBest bn bb
        when (bb' /= bb) $ lift $ setBestBlockHeader bb'
        return bns
      _ -> undefined
  where
    chained (h1 : h2 : hs) = headerHash h1 == prev h2 && chained (h2 : hs)
    chained _ = True
    skipit lbh ls par
      | sh == height lbh = return lbh
      | sh < height lbh = do
          skM <- lift $ getAncestor sh lbh
          case skM of
            Just sk -> return sk
            Nothing ->
              throwError $
                "BUG: Could not get skip for block "
                  ++ show (headerHash $ nodeHeader par)
      | otherwise = do
          let sn = ls !! fromIntegral (height par - sh)
          when (height sn /= sh) $
            throwError "BUG: Node height not right in skip"
          return sn
      where
        sh = skipHeight (height par + 1)
    go _ acc _ _ _ [] = return acc
    go lbh acc bb par pars (h : hs) = do
      sk <- skipit lbh acc par
      bn <- ExceptT . return $ validBlock net t bb par pars h sk
      go lbh (bn : acc) (chooseBest bn bb) bn (take 10 $ par : pars) hs

-- | Block's parent. If the block header is in the store, its parent must also
-- be there. No block header get deleted or pruned from the store.
parentBlock ::
  (BlockHeaders m) =>
  BlockHeader ->
  m (Maybe BlockNode)
parentBlock = getBlockHeader . prev

-- | Validate and connect single block header to the block chain. Return 'Left'
-- if fails to be validated.
connectBlock ::
  (BlockHeaders m) =>
  Network ->
  -- | current time
  Timestamp ->
  BlockHeader ->
  m (Either String BlockNode)
connectBlock net t bh =
  runExceptT $ do
    par <-
      maybeToExceptT
        "Could not get parent block"
        (MaybeT (parentBlock bh))
    pars <- lift $ getParents 10 par
    skM <- lift $ getAncestor (skipHeight (height par + 1)) par
    sk <-
      case skM of
        Just sk -> return sk
        Nothing ->
          throwError $
            "BUG: Could not get skip for block "
              ++ show (headerHash $ nodeHeader par)
    bb <- lift getBestBlockHeader
    bn <- ExceptT . return $ validBlock net t bb par pars bh sk
    let bb' = chooseBest bb bn
    lift $ addBlockHeader bn
    when (bb /= bb') . lift $ setBestBlockHeader bb'
    return bn

-- | Validate this block header. Build a 'BlockNode' if successful.
validBlock ::
  Network ->
  -- | current time
  Timestamp ->
  -- | best block
  BlockNode ->
  -- | immediate parent
  BlockNode ->
  -- | 10 parents above
  [BlockNode] ->
  -- | header to validate
  BlockHeader ->
  -- | skip node (black magic)
  BlockNode ->
  Either String BlockNode
validBlock net t bb par pars bh sk = do
  let mt = medianTime . map (timestamp . nodeHeader) $ par : pars
      nt = timestamp bh
      hh = headerHash bh
      nv = version bh
      ng = height par + 1
      aw = work par + headerWork bh
  unless (isValidPOW net bh) $
    Left $
      "Proof of work failed: " ++ show (headerHash bh)
  unless (nt <= t + 2 * 60 * 60) $
    Left $
      "Invalid header timestamp: " ++ show nt
  unless (nt >= mt) $
    Left $
      "Block timestamp too early: " ++ show nt
  unless (afterLastCP net (height bb) ng) $
    Left $
      "Rewriting pre-checkpoint chain: " ++ show ng
  unless (validCP net ng hh) $
    Left $
      "Rejected checkpoint: " ++ show ng
  unless (bip34 net ng hh) $
    Left $
      "Rejected BIP-34 block: " ++ show hh
  unless (validVersion net ng nv) $
    Left $
      "Invalid block version: " ++ show nv
  return
    BlockNode
      { nodeHeader = bh,
        height = ng,
        work = aw,
        nodeSkip = headerHash $ nodeHeader sk
      }

-- | Return the median of all provided timestamps. Can be unsorted. Error on
-- empty list.
medianTime :: [Timestamp] -> Timestamp
medianTime ts
  | null ts = error "Cannot compute median time of empty header list"
  | otherwise = sort ts !! (length ts `div` 2)

-- | Calculate the height of the skip (magic) block that corresponds to the
-- given height. The block hash of the ancestor at that height will be placed on
-- the 'BlockNode' structure to help locate ancestors at any height quickly.
skipHeight :: BlockHeight -> BlockHeight
skipHeight height
  | height < 2 = 0
  | height .&. 1 /= 0 = invertLowestOne (invertLowestOne $ height - 1) + 1
  | otherwise = invertLowestOne height

-- | Part of the skip black magic calculation.
invertLowestOne :: BlockHeight -> BlockHeight
invertLowestOne height = height .&. (height - 1)

-- | Get a number of parents for the provided block.
getParents ::
  (BlockHeaders m) =>
  Int ->
  BlockNode ->
  -- | starts from immediate parent
  m [BlockNode]
getParents = getpars []
  where
    getpars acc 0 _ = return $ reverse acc
    getpars acc n BlockNode {..}
      | height == 0 = return $ reverse acc
      | otherwise = do
          parM <- getBlockHeader $ prev nodeHeader
          case parM of
            Just bn -> getpars (bn : acc) (n - 1) bn
            Nothing -> error "BUG: All non-genesis blocks should have a parent"

-- | Verify that checkpoint location is valid.
validCP ::
  Network ->
  -- | new child height
  BlockHeight ->
  -- | new child hash
  BlockHash ->
  Bool
validCP net height newChildHash =
  case lookup height $ checkpoints net of
    Just cpHash -> cpHash == newChildHash
    Nothing -> True

-- | New block height above the last checkpoint imported. Used to prevent a
-- reorg below the highest checkpoint that was already imported.
afterLastCP ::
  Network ->
  -- | best height
  BlockHeight ->
  -- | new imported block height
  BlockHeight ->
  Bool
afterLastCP net bestHeight newChildHeight =
  case lM of
    Just l -> l < newChildHeight
    Nothing -> True
  where
    lM =
      listToMaybe . reverse $
        [c | (c, _) <- checkpoints net, c <= bestHeight]

-- | This block should be at least version 2 (BIP34). Block height must be
-- included in the coinbase transaction to prevent non-unique transaction
-- hashes.
bip34 ::
  Network ->
  -- | new child height
  BlockHeight ->
  -- | new child hash
  BlockHash ->
  Bool
bip34 net h hsh
  | fst (bip34Block net) == 0 = True
  | fst (bip34Block net) == h = snd (bip34Block net) == hsh
  | otherwise = True

-- | Check if the provided block height and version are valid.
validVersion ::
  Network ->
  -- | new child height
  BlockHeight ->
  -- | new child version
  Word32 ->
  Bool
validVersion net height version
  | version < 2 = height < fst (bip34Block net)
  | version < 3 = height < (bip66Height net)
  | version < 4 = height < (bip65Height net)
  | otherwise = True

-- | Find last block with normal, as opposed to minimum difficulty (for test
-- networks).
lastNoMinDiff :: (BlockHeaders m) => Network -> BlockNode -> m BlockNode
lastNoMinDiff _ bn@BlockNode {height = 0} = return bn
lastNoMinDiff net bn = do
  let i = height bn `mod` diffInterval net /= 0
      c = encodeCompact $ powLimit net
      l = (bits . nodeHeader $ bn) == c
      e1 =
        error $
          "Could not get block header for parent of "
            ++ show (headerHash . nodeHeader $ bn)
  if i && l
    then do
      bn' <- fromMaybe e1 <$> getBlockHeader (prev . nodeHeader $ bn)
      lastNoMinDiff net bn'
    else return bn

-- | Returns the work required on a block header given the previous block. This
-- coresponds to @bitcoind@ function @GetNextWorkRequired@ in @main.cpp@.
nextWorkRequired ::
  (BlockHeaders m) =>
  Network ->
  BlockNode ->
  BlockHeader ->
  m Word32
nextWorkRequired net par bh = do
  ma <- getAsertAnchor net
  case asert ma <|> daa <|> eda <|> pow of
    Just f -> f par bh
    Nothing -> error "Could not determine difficulty algorithm"
  where
    asert ma = do
      anchor <- ma
      guard (height par > height anchor)
      return $ nextAsertWorkRequired net anchor
    daa = do
      daa_height <- daaHeight net
      guard (height par + 1 >= daa_height)
      return $ nextDaaWorkRequired net
    eda = do
      eda_height <- edaHeight net
      guard (height par + 1 >= eda_height)
      return $ nextEdaWorkRequired net
    pow = return $ nextPowWorkRequired net

-- | Find out the next amount of work required according to the Emergency
-- Difficulty Adjustment (EDA) algorithm from Bitcoin Cash.
nextEdaWorkRequired ::
  (BlockHeaders m) => Network -> BlockNode -> BlockHeader -> m Word32
nextEdaWorkRequired net par bh
  | height par + 1 `mod` diffInterval net == 0 =
      nextWorkRequired net par bh
  | mindiff = return (encodeCompact $ powLimit net)
  | (bits . nodeHeader $ par) == encodeCompact (powLimit net) =
      return (encodeCompact $ powLimit net)
  | otherwise = do
      par6 <- fromMaybe e1 <$> getAncestor (height par - 6) par
      pars <- getParents 10 par
      pars6 <- getParents 10 par6
      let par6med =
            medianTime $ map (timestamp . nodeHeader) (par6 : pars6)
          parmed = medianTime $ map (timestamp . nodeHeader) (par : pars)
          mtp6 = parmed - par6med
      if mtp6 < 12 * 3600
        then return $ bits . nodeHeader $ par
        else
          return $
            let (diff, _) = decodeCompact (bits . nodeHeader $ par)
                ndiff = diff + (diff `shiftR` 2)
             in if powLimit net > ndiff
                  then encodeCompact $ powLimit net
                  else encodeCompact ndiff
  where
    mindiff = timestamp bh > (timestamp . nodeHeader $ par) + targetSpacing net * 2
    e1 = error "Could not get seventh ancestor of block"

-- | Find the next amount of work required according to the Difficulty
-- Adjustment Algorithm (DAA) from Bitcoin Cash.
nextDaaWorkRequired ::
  (BlockHeaders m) => Network -> BlockNode -> BlockHeader -> m Word32
nextDaaWorkRequired net par bh
  | mindiff = return (encodeCompact $ powLimit net)
  | otherwise = do
      unless (height par >= diffInterval net) $
        error "Block height below difficulty interval"
      l <- getSuitableBlock par
      par144 <- fromMaybe e1 <$> getAncestor (height par - 144) par
      f <- getSuitableBlock par144
      let nextTarget = computeTarget net f l
      if nextTarget > powLimit net
        then return $ encodeCompact $ powLimit net
        else return $ encodeCompact nextTarget
  where
    e1 = error "Cannot get ancestor at parent - 144 height"
    mindiff = timestamp bh > (timestamp . nodeHeader $ par) + targetSpacing net * 2

mtp :: (BlockHeaders m) => BlockNode -> m Timestamp
mtp bn
  | height bn == 0 = return 0
  | otherwise = do
      pars <- getParents 11 bn
      return $ medianTime (map (timestamp . nodeHeader) pars)

firstGreaterOrEqual ::
  (BlockHeaders m) =>
  Network ->
  (BlockNode -> m Ordering) ->
  m (Maybe BlockNode)
firstGreaterOrEqual = binSearch False

lastSmallerOrEqual ::
  (BlockHeaders m) =>
  Network ->
  (BlockNode -> m Ordering) ->
  m (Maybe BlockNode)
lastSmallerOrEqual = binSearch True

binSearch ::
  (BlockHeaders m) =>
  Bool ->
  Network ->
  (BlockNode -> m Ordering) ->
  m (Maybe BlockNode)
binSearch top net f = runMaybeT $ do
  (a, b) <- lift $ extremes net
  go a b
  where
    go a b = do
      m <- lift $ middleBlock a b
      a' <- lift $ f a
      b' <- lift $ f b
      m' <- lift $ f m
      r (a, a') (b, b') (m, m')
    r (a, a') (b, b') (m, m')
      | out_of_bounds a' b' = mzero
      | select_first a' = return a
      | select_last b' = return b
      | no_middle a b = choose_one a b
      | is_between a' m' = go a m
      | is_between m' b' = go m b
      | otherwise = mzero
    select_first a'
      | not top = a' /= LT
      | otherwise = False
    select_last b'
      | top = b' /= GT
      | otherwise = False
    out_of_bounds a' b'
      | top = a' == GT
      | otherwise = b' == LT
    no_middle a b = height b - height a <= 1
    is_between a' b' = a' /= GT && b' /= LT
    choose_one a b
      | top = return a
      | otherwise = return b

extremes :: (BlockHeaders m) => Network -> m (BlockNode, BlockNode)
extremes net = do
  b <- getBestBlockHeader
  return (genesisNode net, b)

middleBlock :: (BlockHeaders m) => BlockNode -> BlockNode -> m BlockNode
middleBlock a b =
  getAncestor h b >>= \case
    Nothing -> error "You fell into a pit full of mud and snakes"
    Just x -> return x
  where
    h = middleOf (height a) (height b)

middleOf :: (Integral a) => a -> a -> a
middleOf a b = a + ((b - a) `div` 2)

-- TODO: Use known anchor after fork
getAsertAnchor :: (BlockHeaders m) => Network -> m (Maybe BlockNode)
getAsertAnchor net =
  case asertActivationTime net of
    Nothing -> return Nothing
    Just act -> firstGreaterOrEqual net (f act)
  where
    f act bn = do
      m <- mtp bn
      return $ compare m act

-- | Find the next amount of work required according to the aserti3-2d algorithm.
nextAsertWorkRequired ::
  (BlockHeaders m) =>
  Network ->
  BlockNode ->
  BlockNode ->
  BlockHeader ->
  m Word32
nextAsertWorkRequired net anchor par bh = do
  anchor_parent <-
    fromMaybe e_fork <$> getBlockHeader (prev . nodeHeader $ anchor)
  let anchor_parent_time = toInteger (timestamp . nodeHeader $ anchor_parent)
      time_diff = current_time - anchor_parent_time
  return $ computeAsertBits halflife anchor_bits time_diff height_diff
  where
    halflife = asertHalfLife net
    anchor_height = toInteger (height anchor)
    anchor_bits = bits . nodeHeader $ anchor
    current_height = toInteger (height par) + 1
    height_diff = current_height - anchor_height
    current_time = toInteger (timestamp bh)
    e_fork = error "Could not get fork block header"

idealBlockTime :: Integer
idealBlockTime = 10 * 60

rBits :: Int
rBits = 16

radix :: Integer
radix = 1 `shiftL` rBits

maxBits :: Word32
maxBits = 0x1d00ffff

maxTarget :: Integer
maxTarget = fst $ decodeCompact maxBits

computeAsertBits ::
  Integer ->
  Word32 ->
  Integer ->
  Integer ->
  Word32
computeAsertBits halflife anchor_bits time_diff height_diff =
  if e2 >= 0 && e2 < 65536
    then
      if g4 == 0
        then encodeCompact 1
        else
          if g4 > maxTarget
            then maxBits
            else encodeCompact g4
    else error $ "Exponent not in range: " ++ show e2
  where
    g1 = fst (decodeCompact anchor_bits)
    e1 =
      ((time_diff - idealBlockTime * (height_diff + 1)) * radix)
        `quot` halflife
    s = e1 `shiftR` rBits
    e2 = e1 - s * radix
    g2 =
      g1
        * ( radix
              + ( (195766423245049 * e2 + 971821376 * e2 ^ 2 + 5127 * e2 ^ 3 + 2 ^ 47)
                    `shiftR` (rBits * 3)
                )
          )
    g3 =
      if s < 0
        then g2 `shiftR` negate (fromIntegral s)
        else g2 `shiftL` fromIntegral s
    g4 = g3 `shiftR` rBits

-- | Compute Bitcoin Cash DAA target for a new block.
computeTarget :: Network -> BlockNode -> BlockNode -> Integer
computeTarget net f l =
  let w = (work l - work f) * fromIntegral (targetSpacing net)
      tspan = (timestamp . nodeHeader $ l) - (timestamp . nodeHeader $ f)
      tspan'
        | tspan > 288 * (targetSpacing net) =
            288 * (targetSpacing net)
        | tspan < 72 * (targetSpacing net) =
            72 * (targetSpacing net)
        | otherwise = tspan
      work' = w `div` fromIntegral tspan'
   in 2 ^ (256 :: Integer) `div` work'

-- | Get suitable block for Bitcoin Cash DAA computation.
getSuitableBlock :: (BlockHeaders m) => BlockNode -> m BlockNode
getSuitableBlock par = do
  unless (height par >= 3) $ error "Block height is less than three"
  blocks <- (par :) <$> getParents 2 par
  return $ sortBy (compare `on` (timestamp . nodeHeader)) blocks !! 1

-- | Returns the work required on a block header given the previous block. This
-- coresponds to bitcoind function GetNextWorkRequired in main.cpp.
nextPowWorkRequired ::
  (BlockHeaders m) => Network -> BlockNode -> BlockHeader -> m Word32
nextPowWorkRequired net par bh
  | height par + 1 `mod` diffInterval net /= 0 =
      if minDiffBlocks net
        then
          if ht > pt + delta
            then return $ encodeCompact (powLimit net)
            else do
              d <- lastNoMinDiff net par
              return $ bits . nodeHeader $ d
        else return $ bits . nodeHeader $ par
  | otherwise = do
      let rh = height par - diffInterval net - 1
      a <- fromMaybe e1 <$> getAncestor rh par
      let t = timestamp . nodeHeader $ a
      return $ calcNextWork net (nodeHeader par) t
  where
    e1 = error "Could not get ancestor for block header"
    pt = timestamp . nodeHeader $ par
    ht = timestamp bh
    delta = targetSpacing net * 2

-- | Computes the work required for the first block in a new retarget period.
calcNextWork ::
  Network ->
  -- | last block in previous retarget (parent)
  BlockHeader ->
  -- | timestamp of first block in previous retarget
  Timestamp ->
  Word32
calcNextWork net header time
  | powNoRetarget net = bits header
  | new > powLimit net = encodeCompact $ powLimit net
  | otherwise = encodeCompact new
  where
    s = timestamp header - time
    n
      | s < targetTimespan net `div` 4 = targetTimespan net `div` 4
      | s > targetTimespan net * 4 = targetTimespan net * 4
      | otherwise = s
    l = fst $ decodeCompact $ bits header
    new = l * fromIntegral n `div` fromIntegral (targetTimespan net)

-- | Returns True if the difficulty target (bits) of the header is valid and the
-- proof of work of the header matches the advertised difficulty target. This
-- function corresponds to the function @CheckProofOfWork@ from @bitcoind@ in
-- @main.cpp@.
isValidPOW :: Network -> BlockHeader -> Bool
isValidPOW net h
  | target <= 0 || over || target > powLimit net = False
  | otherwise = blockPOW (headerHash h) <= fromIntegral target
  where
    (target, over) = decodeCompact $ bits h

-- | Returns the proof of work of a block header hash as an 'Integer' number.
blockPOW :: BlockHash -> Integer
blockPOW = bsToInteger . B.reverse . runPutS . serialize

-- | Returns the work represented by this block. Work is defined as the number
-- of tries needed to solve a block in the average case with respect to the
-- target.
headerWork :: BlockHeader -> Integer
headerWork bh = largestHash `div` (target + 1)
  where
    target = fst $ decodeCompact $ bits bh
    largestHash = 1 `shiftL` 256

-- | Number of blocks on average between difficulty cycles (2016 blocks).
diffInterval :: Network -> Word32
diffInterval net = targetTimespan net `div` targetSpacing net

-- | Compare two blocks to get the best.
chooseBest :: BlockNode -> BlockNode -> BlockNode
chooseBest b1 b2
  | work b1 == work b2 =
      if height b1 >= height b2
        then b1
        else b2
  | work b1 > work b2 = b1
  | otherwise = b2

-- | Get list of blocks for a block locator.
blockLocatorNodes :: (BlockHeaders m) => BlockNode -> m [BlockNode]
blockLocatorNodes best =
  reverse <$> go [] best 1
  where
    e1 = error "Could not get ancestor"
    go loc bn n =
      let loc' = bn : loc
          n' =
            if length loc' > 10
              then n * 2
              else 1
       in if height bn < n'
            then do
              a <- fromMaybe e1 <$> getAncestor 0 bn
              return $ a : loc'
            else do
              let h = height bn - n'
              bn' <- fromMaybe e1 <$> getAncestor h bn
              go loc' bn' n'

-- | Get block locator.
blockLocator :: (BlockHeaders m) => BlockNode -> m BlockLocator
blockLocator bn = map (headerHash . nodeHeader) <$> blockLocatorNodes bn

-- | Become rich beyond your wildest dreams.
mineBlock :: Network -> Word32 -> BlockHeader -> BlockHeader
mineBlock net seed h =
  head
    [ j
      | i <- (+ seed) <$> [0 .. maxBound],
        let j = h {nonce = i},
        isValidPOW net j
    ]

-- | Generate and append new blocks (mining). Only practical in regtest network.
appendBlocks ::
  Network ->
  -- | random seed
  Word32 ->
  BlockHeader ->
  Int ->
  [BlockHeader]
appendBlocks _ _ _ 0 = []
appendBlocks net seed bh i =
  bh' : appendBlocks net seed bh' (i - 1)
  where
    bh' =
      mineBlock
        net
        seed
        bh
          { prev = headerHash bh,
            -- Just to make it different in every header
            merkle = sha256 $ runPutS $ serialize seed
          }

-- | Find the last common block ancestor between provided block headers.
splitPoint :: (BlockHeaders m) => BlockNode -> BlockNode -> m BlockNode
splitPoint l r = do
  let h = min (height l) (height r)
  ll <- fromMaybe e <$> getAncestor h l
  lr <- fromMaybe e <$> getAncestor h r
  f ll lr
  where
    e = error "BUG: Could not get ancestor at lowest height"
    f ll lr =
      if ll == lr
        then return lr
        else do
          let h = height ll - 1
          pl <- fromMaybe e <$> getAncestor h ll
          pr <- fromMaybe e <$> getAncestor h lr
          f pl pr

-- | Generate the entire Genesis block for 'Network'.
genesisBlock :: Network -> Ctx -> Block
genesisBlock net ctx = Block (genesisHeader net) [genesisTx ctx]

-- | Compute block subsidy at particular height.
computeSubsidy :: Network -> BlockHeight -> Word64
computeSubsidy net height =
  let halvings = height `div` (halvingInterval net)
      ini = 50 * 100 * 1000 * 1000
   in if halvings >= 64
        then 0
        else ini `shiftR` fromIntegral halvings
