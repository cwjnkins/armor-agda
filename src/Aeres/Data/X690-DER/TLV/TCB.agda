{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Length.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.TLV.TCB where

record TLV (t : UInt8) (@0 A : List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkTLV
  field
    @0 {l v} : List UInt8
    len : Length l
    val : A v
    @0 len≡ : getLength len ≡ length v
    @0 bs≡  : bs ≡ t ∷ l ++ v

TLVNonEmptyVal : ∀ {t}{@0 A} → (@0 bs : List UInt8) (tlv : TLV t A bs) → Set
TLVNonEmptyVal bs tlv = 1 ≤ getLength (TLV.len tlv)

-- TODO: remove?
TLVLenBounded : ∀ {t}{@0 A} → (l u : ℕ) → (@0 bs : List UInt8) (tlv : TLV t A bs) → Set
TLVLenBounded l u bs tlv = InRange l u (getLength (TLV.len tlv))

TLVSizeBounded : ∀ {t} {@0 A} (len : ∀ {@0 bs} → A bs → ℕ) (l u : ℕ) → ∀ (@0 bs) → TLV t A bs → Set
TLVSizeBounded len l u bs tlv = InRange l u (len (TLV.val tlv))
