open import Aeres.Binary
open import Aeres.Prelude
  hiding (foldl)

module Aeres.Foreign.ByteString where

{-# FOREIGN GHC import qualified Data.ByteString as ByteString #-}
{-# FOREIGN GHC import           Data.Word #-}

postulate
  ByteString : Set
  Word8      : Set

module Word8 where
  postulate
    toNat : Word8 → ℕ

  -- axiom
  postulate
    @0 toNat< : (w : Word8) → toNat w < 256

  toUInt8 : Word8 → UInt8
  toUInt8 w = Fin.fromℕ< (uneraseDec (toNat< w) (_ ≤? _))

postulate
  foldl : ∀ {A : Set} → (A → Word8 → A) → A → ByteString → A

toUInt8 : ByteString → List UInt8
toUInt8 = reverse ∘ foldl (λ xs w → Word8.toUInt8 w ∷ xs) []

{-# COMPILE GHC ByteString  = type ByteString.ByteString #-}
{-# COMPILE GHC Word8       = type Word8 #-}
{-# COMPILE GHC Word8.toNat = toInteger #-}
{-# COMPILE GHC foldl       = \ _ -> ByteString.foldl #-}

