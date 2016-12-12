module Crypto.Hash.Tree where

import Data.Bits (Bits(..), shiftL, shiftR, testBit)
import Data.Semigroup ((<>))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty
import Numeric.Natural

import Crypto.Hash
import Data.ByteArray (ByteArrayAccess, Bytes, singleton)

data HashTree a
  = Leaf (Digest a)
  | Comb Natural (Digest a) (HashTree a) (HashTree a)

instance Show (HashTree a) where
  show t = show $ leaves t

-- | Combines a root hash with the generation (number of leaves minus 1)
--
data RootHash a = RootHash
  Natural
  (Digest a)
  deriving (Show)

data InclusionProof a = InclusionProof Natural [Digest a]
  deriving (Show)

data ConsistencyProof a = ConsistencyProof [Digest a]
  deriving (Show)

leaf :: (HashAlgorithm a, ByteArrayAccess ba) => ba -> HashTree a
leaf = Leaf . hashLeaf

leaves :: HashTree a -> NonEmpty (Digest a)
leaves (Leaf h) = h :| []
leaves (Comb _ h l r) = leaves l <> leaves r

count :: HashTree a -> Natural
count (Leaf _) = 1
count (Comb n _ _ _) = n

rootHash :: HashTree a -> RootHash a
rootHash (Leaf h) = RootHash 0 h
rootHash (Comb n h _ _) = RootHash (n - 1) h

hashLeaf :: (HashAlgorithm a, ByteArrayAccess ba) => ba -> Digest a
hashLeaf ba =
  let
    c1 = hashInit
    c2 = hashUpdate c1 (singleton 0x00 :: Bytes)
    c3 = hashUpdate c2 ba
  in
    hashFinalize c3

hashComb
  :: (HashAlgorithm a, ByteArrayAccess ba1, ByteArrayAccess ba2)
  => ba1
  -> ba2
  -> Digest a
hashComb ba1 ba2 =
  let
    c1 = hashInit
    c2 = hashUpdate c1 (singleton 0x01 :: Bytes)
    c3 = hashUpdate c2 ba1
    c4 = hashUpdate c3 ba2
  in
    hashFinalize c4

append :: (HashAlgorithm a, ByteArrayAccess ba) => ba -> HashTree a -> HashTree a
append = appendLeaf . hashLeaf

-- | Append a leaf digest to the tree.
--
-- The digest is the leaf hash of the value, /not/ the raw hash.
--
appendLeaf :: (HashAlgorithm a) => Digest a -> HashTree a -> HashTree a
appendLeaf h t =
  let
    leaf = Leaf h
  in case t of
    l@(Leaf hl) -> Comb 2 (hashComb hl h) l leaf
    c@(Comb n hc l r) ->
      let
        RootHash nl hl = rootHash l
        RootHash nr hr = rootHash r
        r' = append h r
        RootHash _ hr' = rootHash r'
      in
        if nl == nr   -- 'c' is balanced
        then Comb (n + 1) (hashComb hc h) c leaf
        else Comb (n + 1) (hashComb hl hr') l r'

-- | Creates hash tree from list of LEAF HASHES
--
fromList :: (HashAlgorithm a) => NonEmpty (Digest a) -> HashTree a
fromList = go . Data.List.NonEmpty.reverse
  where
  go (h :| []) = Leaf h
  go (h :| (hh:hs)) = appendLeaf h (go (hh :| hs))


-- | Generate an inclusion proof for the mth hash in the tree
--
-- The first hash in the proof is the "lowest" in the proof path.
--
-- It's assumed that 0 < m < (count t - 1).  Function is total but result is
-- nonsense if this condition is violated.
--
inclusionProof :: HashTree a -> Natural -> InclusionProof a
inclusionProof t m = InclusionProof m (reverse $ go t m)
  where
  go (Leaf h) _ = []
  go (Comb _ h l r) m =
    let
      RootHash nl hl = rootHash l
      RootHash _  hr = rootHash r
    in
      if m <= nl
      then hr : go l m
      else hl : go r (m - count l)

-- | For the given index and root hash, verify an inclusion proof
--
verifyInclusion
  :: HashAlgorithm a
  => Digest a           -- ^ _leaf_ hash to check
  -> InclusionProof a   -- ^ inclusion proof
  -> RootHash a         -- ^ root hash of tree
  -> Bool
verifyInclusion h (InclusionProof m hs) (RootHash n hr) =
  go h (m, n) hs == hr
  where
    go h _ [] = h
    go h (m, n) (hx:hs) =
      let
        p n m = m `testBit` 0 || m == n
        h' = if p n m then hashComb hx h else hashComb h hx
        (m', n') = if p n m then shiftBothUntil (p 0) (m, n) else (m, n)
      in go h' (shiftBoth (m', n')) hs


-- | Produce consistency proof between this hash tree
-- and an earlier generation
--
consistencyProof
  :: HashTree a
  -> Natural
  -- ^ Create consistency proof from this generation to current tree.
  -- 0 < m <= n
  -> ConsistencyProof a
consistencyProof t m = ConsistencyProof (reverse (go True t m))
  where
  go :: Bool -> HashTree a -> Natural -> [Digest a]
  go isSubtree t m
    | m == count t - 1 && isSubtree   = []
    | m == count t - 1 {-!isSubtree-} = let RootHash _ h = rootHash t in [h]
    | otherwise = case t of
        Leaf _ -> []  -- is this correct?
        Comb _ _ l r
          | m < count l  -> let RootHash _ hr = rootHash r in hr : go isSubtree l m
          | otherwise     -> let RootHash _ hl = rootHash l in hl : go False r (m - count l)

verifyConsistency
  :: HashAlgorithm a
  => RootHash a           -- ^ root hash of original tree
  -> RootHash a           -- ^ root hash of successor tree
  -> ConsistencyProof a   -- ^ consistency proof
  -> Bool
verifyConsistency (RootHash m hm) (RootHash n hn) (ConsistencyProof hs) =
  let
    hs' = if popCount (m + 1) == 1 || m == n then hm:hs else hs
    (fn, sn) = shiftBothUntil (not . (`testBit` 0)) (m, n)
  in
    case hs' of
      [] -> False
      fr : hs'' ->
        let (fr', sr') = go fr fr (fn, sn) hs''
        in fr' == hm && sr' == hn
  where
  go fr sr _        []     = (fr, sr)
  go fr sr (fn, sn) (h:hs) =
    let
      p n m = m `testBit` 0 || m == n
      fr' = if p sn fn then hashComb h fr else fr
      sr' = if p sn fn then hashComb h sr else hashComb sr h
      (fn', sn') = if p sn fn then shiftBothUntil (p 0) (fn, sn) else (fn, sn)
    in go fr' sr' (shiftBoth (fn', sn')) hs


-- | Right shift both numbers until predicate holds for first number
--
shiftBothUntil :: (Bits a, Bits b) => (a -> Bool) -> (a, b) -> (a, b)
shiftBothUntil p (m, n)
  | p m = (m, n)
  | otherwise = shiftBothUntil p (shiftBoth (m, n))

-- | Right shift both numbers
--
shiftBoth :: (Bits a, Bits b) => (a, b) -> (a, b)
shiftBoth (m, n) = (m `shiftR` 1, n `shiftR` 1)
