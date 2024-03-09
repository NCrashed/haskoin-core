{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      : Haskoin.Keys.Common
-- Copyright   : No rights reserved
-- License     : MIT
-- Maintainer  : jprupp@protonmail.ch
-- Stability   : experimental
-- Portability : POSIX
--
-- ECDSA private and public key functions.
module Haskoin.Crypto.Keys.Common
  ( -- * Bitcoin Public & Private Keys
    PublicKey (..),
    PrivateKey (..),
    wrapPubKey,
    derivePublicKey,
    wrapSecKey,
    fromMiniKey,
    tweakPubKey,
    tweakSecKey,

    -- ** Private Key Wallet Import Format (WIF)
    fromWif,
    toWif,
  )
where

import Control.DeepSeq
import Control.Monad (guard, mzero, (<=<))
import Crypto.Secp256k1
import Data.Aeson
  ( Encoding,
    FromJSON,
    ToJSON (..),
    Value (String),
    object,
    parseJSON,
    withText,
  )
import Data.Aeson.Encoding (text, unsafeToEncoding)
import Data.Aeson.Types (Parser)
import Data.Binary (Binary (..))
import Data.Bool (bool)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder (char7)
import Data.Bytes.Get
import Data.Bytes.Put
import Data.Bytes.Serial
import Data.Hashable
import Data.Maybe (fromMaybe)
import Data.Serialize (Serialize (..))
import Data.String (IsString, fromString)
import Data.String.Conversions (cs)
import GHC.Generics (Generic)
import Haskoin.Address.Base58
import Haskoin.Crypto.Hash
import Haskoin.Network.Data
import Haskoin.Util

-- | Elliptic curve public key type with expected serialized compression flag.
data PublicKey = PublicKey
  { point :: !PubKey,
    pkCompress :: !Bool
  }
  deriving (Generic, Show, Read, Hashable, Eq, NFData)

instance MarshalJSON Ctx PublicKey where
  marshalValue ctx = String . encodeHex . runPutS . marshalPut ctx

  marshalEncoding ctx = hexEncoding . runPutL . marshalPut ctx

  unmarshalValue ctx =
    withText "PublicKey" $ \t -> do
      bs <- maybe (fail "Expected hex public key") return $ decodeHex t
      either fail return $ unmarshal ctx bs

instance Marshal Ctx PublicKey where
  marshalGet ctx = do
    c <-
      lookAhead $
        getWord8 >>= \case
          0x02 -> return True
          0x03 -> return True
          0x04 -> return False
          _ -> fail "Not a public key"
    bs <- getByteString $ if c then 33 else 65
    case importPubKey ctx bs of
      Nothing -> fail "Could not decode public key"
      Just k -> return $ PublicKey k c

  marshalPut ctx pk =
    putByteString $ exportPubKey ctx (pkCompress pk) $ point pk

-- | Wrap a public key from secp256k1 library adding information about compression.
wrapPubKey :: Bool -> PubKey -> PublicKey
wrapPubKey c p = PublicKey p c

-- | Derives a public key from a private key. This function will preserve
-- compression flag.
derivePublicKey :: Ctx -> PrivateKey -> PublicKey
derivePublicKey ctx (PrivateKey d c) = PublicKey (derivePubKey ctx d) c

-- | Tweak a public key.
tweakPubKey :: Ctx -> PubKey -> Hash256 -> Maybe PubKey
tweakPubKey ctx p =
  tweakAddPubKey ctx p <=< tweak . runPutS . serialize

-- | Elliptic curve private key type with expected public key compression
-- information. Compression information is stored in private key WIF formats and
-- needs to be preserved to generate the correct address from the corresponding
-- public key.
data PrivateKey = PrivateKey
  { key :: !SecKey,
    prvCompress :: !Bool
  }
  deriving (Eq, Show, Read, Generic, NFData)

instance Serial PrivateKey where
  serialize p = do
    putByteString (getSecKey . key $ p)
    serialize $ prvCompress p
  deserialize = do
    k <- getByteString 32
    c <- deserialize
    return PrivateKey {key = SecKey k, prvCompress = c}

instance MarshalJSON Network PrivateKey where
  marshalValue net = String . toWif net
  marshalEncoding net = text . toWif net
  unmarshalValue net =
    withText "PrivateKey" $
      maybe (fail "Could not decode WIF") return . fromWif net

-- | Wrap private key with corresponding public key compression flag.
wrapSecKey :: Bool -> SecKey -> PrivateKey
wrapSecKey c d = PrivateKey d c

-- | Tweak a private key.
tweakSecKey :: Ctx -> SecKey -> Hash256 -> Maybe SecKey
tweakSecKey ctx k =
  tweakAddSecKey ctx k <=< tweak . runPutS . serialize

-- | Decode Casascius mini private keys (22 or 30 characters).
fromMiniKey :: ByteString -> Maybe PrivateKey
fromMiniKey bs = do
  guard checkShortKey
  wrapSecKey False <$> (secKey . runPutS . serialize . sha256) bs
  where
    checkHash = runPutS $ serialize $ sha256 $ bs `BS.append` "?"
    checkShortKey = BS.length bs `elem` [22, 30] && BS.head checkHash == 0x00

-- | Decode private key from WIF (wallet import format) string.
fromWif :: Network -> Base58 -> Maybe PrivateKey
fromWif net wif = do
  bs <- decodeBase58Check wif
  -- Check that this is a private key
  guard (BS.head bs == secretPrefix net)
  case BS.length bs of
    -- Uncompressed format
    33 -> wrapSecKey False <$> (secKey . BS.tail) bs
    -- Compressed format
    34 -> do
      guard $ BS.last bs == 0x01
      wrapSecKey True <$> (secKey . BS.tail . BS.init) bs
    -- Bad length
    _ -> Nothing

-- | Encode private key into a WIF string.
toWif :: Network -> PrivateKey -> Base58
toWif net (PrivateKey k c) =
  encodeBase58Check . BS.cons (secretPrefix net) $
    if c then getSecKey k `BS.snoc` 0x01 else getSecKey k
