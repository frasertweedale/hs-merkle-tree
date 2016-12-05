{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Data.Maybe (fromJust)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty

import Crypto.Hash
import qualified Data.ByteString as B

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

import Crypto.Hash.Tree

#if ! MIN_VERSION_QuickCheck(2,9,0)
instance Arbitrary a => Arbitrary (NonEmpty a) where
  arbitrary = (:|) <$> arbitrary <*> arbitrary
#endif

main :: IO ()
main = defaultMain $ testGroup "Properties"
  [ testProperty "generation = count - 1"
      (prop_generationCount :: HashTree SHA256 -> Bool)
  , testProperty "inclusion proofs"
      (prop_inclusion :: HashTree SHA256 -> Bool)
  , testProperty "verifyInclusion is total"
      (prop_verifyInclusion_total :: Digest SHA256 -> InclusionProof SHA256 -> RootHash SHA256 -> Bool)
  , testProperty "consistency proofs"
      (prop_consistency :: HashTree SHA256 -> [Digest SHA256] -> Bool)
  , testProperty "verifyConsistency is total"
      (prop_verifyConsistency_total :: RootHash SHA256 -> RootHash SHA256 -> ConsistencyProof SHA256 -> Bool)
  ]

instance HashAlgorithm a => Arbitrary (Digest a) where
  arbitrary = do
    l <- vector (hashDigestSize (undefined :: a))
    pure $ fromJust $ digestFromByteString (B.pack l)

instance HashAlgorithm a => Arbitrary (HashTree a) where
  arbitrary = fromList <$> arbitrary

instance HashAlgorithm a => Arbitrary (RootHash a) where
  arbitrary = RootHash <$> arbitrary <*> arbitrary

instance HashAlgorithm a => Arbitrary (InclusionProof a) where
  arbitrary = InclusionProof <$> arbitrary <*> arbitrary

instance HashAlgorithm a => Arbitrary (ConsistencyProof a) where
  arbitrary = ConsistencyProof <$> arbitrary

prop_generationCount :: HashAlgorithm a => HashTree a -> Bool
prop_generationCount t =
  let
    RootHash n _ = rootHash t
  in
    n == count t - 1

-- | Generate and validate an inclusion proof for every leaf in a tree
--
prop_inclusion :: HashAlgorithm a => HashTree a -> Bool
prop_inclusion t =
  all
    (\(m, h) -> verifyInclusion h (inclusionProof t m) (rootHash t))
    (Data.List.NonEmpty.zip (0 :| [1..]) (leaves t))

prop_verifyInclusion_total
  :: HashAlgorithm a
  => Digest a -> InclusionProof a -> RootHash a -> Bool
prop_verifyInclusion_total h proof root =
  verifyInclusion h proof root
  || True  -- we don't care what result is, as long as there is one.

-- | Given a tree and a list of additional leaves, grow the tree,
-- then generate and validate a consistency proof.
--
prop_consistency :: HashAlgorithm a => HashTree a -> [Digest a] -> Bool
prop_consistency t hs =
  let
    t' = foldr appendLeaf t hs
    m = count t - 1
    proof = consistencyProof t' m
  in
    verifyConsistency (rootHash t) (rootHash t') proof

prop_verifyConsistency_total
  :: HashAlgorithm a
  => RootHash a -> RootHash a -> ConsistencyProof a -> Bool
prop_verifyConsistency_total hr hr' proof =
  verifyConsistency hr hr' proof
  || True  -- we don't care what result is, as long as there is one.
