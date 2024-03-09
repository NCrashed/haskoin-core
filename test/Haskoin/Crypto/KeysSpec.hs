{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module Haskoin.Crypto.KeysSpec (spec) where

import Control.Lens
import Control.Monad
import Data.Aeson as A
import Data.Aeson.Lens hiding (key)
import qualified Data.Aeson.Lens as A
import Data.ByteString qualified as B
import Data.ByteString.Char8 qualified as C
import Data.Bytes.Get
import Data.Bytes.Put
import Data.Bytes.Serial
import Data.Default (def)
import Data.Maybe
import Data.Serialize qualified as S
import Data.String (fromString)
import Data.String.Conversions (cs)
import Data.Text (Text)
import Haskoin.Address
import Haskoin.Crypto
import Haskoin.Network.Constants
import Haskoin.Script
import Haskoin.Util
import Haskoin.Util.Arbitrary
import Test.HUnit
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

identityTests :: Ctx -> IdentityTests
identityTests ctx =
  def
    { readTests =
        [ ReadBox (arbitrary :: Gen SecKey),
          ReadBox arbitraryPrivateKey,
          ReadBox (arbitraryPublicKey ctx)
        ],
      marshalJsonTests =
        [ MarshalJsonBox $ (,) <$> arbitraryNetwork <*> arbitraryPrivateKey,
          MarshalJsonBox ((,) ctx <$> arbitraryPublicKey ctx)
        ],
      serialTests =
        [ SerialBox arbitraryPrivateKey
        ],
      marshalTests =
        [ MarshalBox ((,) ctx <$> arbitraryPublicKey ctx)
        ]
    }

spec :: Spec
spec = prepareContext $ \ctx -> do
  describe "Key pair property checks" $ do
    testIdentity $ identityTests ctx
    prop "Public key is canonical" $
      forAll (arbitraryKeyPair ctx) (isCanonicalPubKey ctx . snd)
    prop "Key pair key show . read identity" $
      forAll (arbitraryKeyPair ctx) $ \x ->
        (read . show) x == x
    prop "Public key binary serialization" $ do
      forAll (arbitraryKeyPair ctx) $ \(sec, pub) ->
        (unmarshal ctx . marshal ctx) pub == Right pub
    prop "fromWif . toWif identity" $
      forAll arbitraryNetwork $ \net ->
        forAll (arbitraryKeyPair ctx) $ \(key, _) ->
          (fromWif net . toWif net) key == Just key
    prop "WIF binary identity" $
      forAll arbitraryNetwork $ \net ->
        forAll (arbitraryKeyPair ctx) $ \(key, _) ->
          (runGetS deserialize . runPutS . serialize) key == Right key
  describe "Bitcoin core vectors /src/test/key_tests.cpp" $ do
    it "Passes WIF decoding tests" testPrivkey
    it "Passes SecKey compression tests" testPrvKeyCompressed
    it "Passes PubKey compression tests" $ testKeyCompressed ctx
    it "Passes address matching tests" $ testMatchingAddress ctx
    it "Passes signature verification" $ testSigs ctx
    it "Passes deterministic signing tests" $ testDetSigning ctx
  describe "MiniKey vectors" $
    it "Passes MiniKey decoding tests" testMiniKey
  describe "key_io_valid.json vectors" $ do
    vectors <- runIO (readTestFile "key_io_valid.json" :: IO [(Text, Text, A.Value)])
    it "Passes the key_io_valid.json vectors" $
      mapM_ (testKeyIOValidVector ctx) vectors
  describe "key_io_invalid.json vectors" $ do
    vectors <- runIO (readTestFile "key_io_invalid.json" :: IO [[Text]])
    it "Passes the key_io_invalid.json vectors" $
      mapM_ (testKeyIOInvalidVector ctx) vectors

-- github.com/bitcoin/bitcoin/blob/master/src/script.cpp
-- from function IsCanonicalPubKey
isCanonicalPubKey :: Ctx -> PublicKey -> Bool
isCanonicalPubKey ctx p =
  not $
    -- Non-canonical public key: too short
    (B.length bs < 33)
      ||
      -- Non-canonical public key: invalid length for uncompressed key
      (B.index bs 0 == 4 && B.length bs /= 65)
      ||
      -- Non-canonical public key: invalid length for compressed key
      (B.index bs 0 `elem` [2, 3] && B.length bs /= 33)
      ||
      -- Non-canonical public key: compressed nor uncompressed
      (B.index bs 0 `notElem` [2, 3, 4])
  where
    bs = marshal ctx p

testMiniKey :: Assertion
testMiniKey =
  assertEqual "fromMiniKey" (Just res) (go "S6c56bnXQiBjk9mqSYE7ykVQ7NzrRy")
  where
    go = fmap (encodeHex . (getSecKey . key)) . fromMiniKey
    res = "4c7a9640c72dc2099f23715d0c8a0d8a35f8906e3cab61dd3f78b67bf887c9ab"

-- Test vectors from:
-- https://github.com/bitcoin/bitcoin/blob/master/src/test/key_io_tests.cpp

testKeyIOValidVector :: Ctx -> (Text, Text, A.Value) -> Assertion
testKeyIOValidVector ctx (a, payload, obj)
  | disabled = return () -- There are invalid version 1 bech32 addresses
  | isPrv = do
      -- Test from WIF to SecKey
      let isComp = obj ^?! A.key "isCompressed" . _Bool
          prvKeyM = fromWif net a
          prvKeyHexM = encodeHex . (getSecKey . key) <$> prvKeyM
      assertBool "Valid PrvKey" $ isJust prvKeyM
      assertEqual "Valid compression" (Just isComp) (prvCompress <$> prvKeyM)
      assertEqual "WIF matches payload" (Just payload) prvKeyHexM
      let prvAsPubM :: Maybe ScriptOutput
          prvAsPubM = (eitherToMaybe . unmarshal ctx <=< decodeHex) a
      assertBool "PrvKey is invalid ScriptOutput" $ isNothing prvAsPubM
      -- Test from SecKey to WIF
      let secM = secKey =<< decodeHex payload
          wifM = toWif net . wrapSecKey isComp <$> secM
      assertEqual "Payload matches WIF" (Just a) wifM
  | otherwise = do
      -- Test Addr to Script
      let addrM = textToAddr net a
          scriptM = encodeHex . marshal ctx . addressToOutput <$> addrM
      assertBool ("Valid Address " <> cs a) $ isJust addrM
      assertEqual "Address matches payload" (Just payload) scriptM
      let pubAsWifM = fromWif net a
          pubAsSecM = secKey =<< decodeHex a
      assertBool "Address is invalid Wif" $ isNothing pubAsWifM
      assertBool "Address is invalid PrvKey" $ isNothing pubAsSecM
      -- Test Script to Addr
      let outM = eitherToMaybe . unmarshal ctx =<< decodeHex payload
          resM = addrToText net =<< outputAddress ctx =<< outM
      assertEqual "Payload matches address" (Just a) resM
  where
    isPrv = obj ^?! A.key "isPrivkey" . _Bool
    disabled = fromMaybe False $ obj ^? A.key "disabled" . _Bool
    chain = obj ^?! A.key "chain" . _String
    net =
      case chain of
        "main" -> btc
        "test" -> btcTest
        "regtest" -> btcRegTest
        _ -> error "Invalid chain key in key_io_valid.json"

testKeyIOInvalidVector :: Ctx -> [Text] -> Assertion
testKeyIOInvalidVector ctx [a] = do
  let wifMs = (`fromWif` a) <$> allNets
      secKeyM = (secKey <=< decodeHex) a
      scriptM :: Maybe ScriptOutput
      scriptM = (eitherToMaybe . unmarshal ctx <=< decodeHex) a
  assertBool "Payload is invalid WIF" $ all isNothing wifMs
  assertBool "Payload is invalid SecKey" $ isNothing secKeyM
  assertBool "Payload is invalid Script" $ isNothing scriptM
testKeyIOInvalidVector _ _ = assertFailure "Invalid test vector"

-- Test vectors from:
-- https://github.com/bitcoin/bitcoin/blob/master/src/test/key_tests.cpp

testPrivkey :: Assertion
testPrivkey = do
  assertBool "Key 1" $ isJust $ fromWif btc strSecret1
  assertBool "Key 2" $ isJust $ fromWif btc strSecret2
  assertBool "Key 1C" $ isJust $ fromWif btc strSecret1C
  assertBool "Key 2C" $ isJust $ fromWif btc strSecret2C
  assertBool "Bad key" $ isNothing $ fromWif btc strAddressBad

testPrvKeyCompressed :: Assertion
testPrvKeyCompressed = do
  assertBool "Key 1" $ not $ prvCompress sec1
  assertBool "Key 2" $ not $ prvCompress sec2 
  assertBool "Key 1C" $ prvCompress sec1C 
  assertBool "Key 2C" $ prvCompress sec2C

testKeyCompressed :: Ctx -> Assertion
testKeyCompressed ctx = do
  assertBool "Key 1" $ not $ pkCompress (pub1 ctx)
  assertBool "Key 2" $ not $ pkCompress (pub2 ctx)
  assertBool "Key 1C" $ pkCompress (pub1C ctx)
  assertBool "Key 2C" $ pkCompress (pub2C ctx)

testMatchingAddress :: Ctx -> Assertion
testMatchingAddress ctx = do
  assertEqual "Key 1" (Just addr1) $ addrToText btc (pubKeyAddr ctx (pub1 ctx))
  assertEqual "Key 2" (Just addr2) $ addrToText btc (pubKeyAddr ctx (pub2 ctx))
  assertEqual "Key 1C" (Just addr1C) $ addrToText btc (pubKeyAddr ctx (pub1C ctx))
  assertEqual "Key 2C" (Just addr2C) $ addrToText btc (pubKeyAddr ctx (pub2C ctx))

testSigs :: Ctx -> Assertion
testSigs ctx = forM_ sigMsg $ testSignature ctx . doubleSHA256

sigMsg :: [B.ByteString]
sigMsg =
  [ mconcat ["Very secret message ", C.pack (show (i :: Int)), ": 11"]
    | i <- [0 .. 15]
  ]

testSignature :: Ctx -> Hash256 -> Assertion
testSignature ctx h = do
  let sign1 = signHash ctx (key sec1) h
      sign2 = signHash ctx (key sec2) h
      sign1C = signHash ctx (key sec1C) h
      sign2C = signHash ctx (key sec2C) h
  assertBool "Key 1, Sign1" $ verifyHashSig ctx h sign1 (point $ pub1 ctx)
  assertBool "Key 1, Sign2" $ not $ verifyHashSig ctx h sign2 (point $ pub1 ctx)
  assertBool "Key 1, Sign1C" $ verifyHashSig ctx h sign1C (point $ pub1 ctx)
  assertBool "Key 1, Sign2C" $ not $ verifyHashSig ctx h sign2C (point $ pub1 ctx)
  assertBool "Key 2, Sign1" $ not $ verifyHashSig ctx h sign1 (point $ pub2 ctx)
  assertBool "Key 2, Sign2" $ verifyHashSig ctx h sign2 (point $ pub2 ctx)
  assertBool "Key 2, Sign1C" $ not $ verifyHashSig ctx h sign1C (point $ pub2 ctx)
  assertBool "Key 2, Sign2C" $ verifyHashSig ctx h sign2C (point $ pub2 ctx)
  assertBool "Key 1C, Sign1" $ verifyHashSig ctx h sign1 (point $ pub1C ctx)
  assertBool "Key 1C, Sign2" $ not $ verifyHashSig ctx h sign2 (point $ pub1C ctx)
  assertBool "Key 1C, Sign1C" $ verifyHashSig ctx h sign1C (point $ pub1C ctx)
  assertBool "Key 1C, Sign2C" $ not $ verifyHashSig ctx h sign2C (point $ pub1C ctx)
  assertBool "Key 2C, Sign1" $ not $ verifyHashSig ctx h sign1 (point $ pub2C ctx)
  assertBool "Key 2C, Sign2" $ verifyHashSig ctx h sign2 (point $ pub2C ctx)
  assertBool "Key 2C, Sign1C" $ not $ verifyHashSig ctx h sign1C (point $ pub2C ctx)
  assertBool "Key 2C, Sign2C" $ verifyHashSig ctx h sign2C (point $ pub2C ctx)

testDetSigning :: Ctx -> Assertion
testDetSigning ctx = do
  let m = doubleSHA256 ("Very deterministic message" :: B.ByteString)
  assertEqual
    "Det sig 1"
    (signHash ctx (key sec1) m)
    (signHash ctx (key sec1C) m)
  assertEqual
    "Det sig 2"
    (signHash ctx (key sec2) m)
    (signHash ctx (key sec2C) m)

strSecret1, strSecret2, strSecret1C, strSecret2C :: Text
strSecret1 = "5HxWvvfubhXpYYpS3tJkw6fq9jE9j18THftkZjHHfmFiWtmAbrj"
strSecret2 = "5KC4ejrDjv152FGwP386VD1i2NYc5KkfSMyv1nGy1VGDxGHqVY3"
strSecret1C = "Kwr371tjA9u2rFSMZjTNun2PXXP3WPZu2afRHTcta6KxEUdm1vEw"
strSecret2C = "L3Hq7a8FEQwJkW1M2GNKDW28546Vp5miewcCzSqUD9kCAXrJdS3g"

sec1, sec2, sec1C, sec2C :: PrivateKey
sec1 = fromJust $ fromWif btc strSecret1
sec2 = fromJust $ fromWif btc strSecret2
sec1C = fromJust $ fromWif btc strSecret1C
sec2C = fromJust $ fromWif btc strSecret2C

addr1, addr2, addr1C, addr2C :: Text
addr1 = "1QFqqMUD55ZV3PJEJZtaKCsQmjLT6JkjvJ"
addr2 = "1F5y5E5FMc5YzdJtB9hLaUe43GDxEKXENJ"
addr1C = "1NoJrossxPBKfCHuJXT4HadJrXRE9Fxiqs"
addr2C = "1CRj2HyM1CXWzHAXLQtiGLyggNT9WQqsDs"

strAddressBad :: Text
strAddressBad = "1HV9Lc3sNHZxwj4Zk6fB38tEmBryq2cBiF"

pub1, pub2, pub1C, pub2C :: Ctx -> PublicKey
pub1 ctx = derivePublicKey ctx sec1
pub2 ctx = derivePublicKey ctx sec2
pub1C ctx = derivePublicKey ctx sec1C
pub2C ctx = derivePublicKey ctx sec2C
