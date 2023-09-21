{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.OID.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

LeastBytes : List UInt8 → Set
LeastBytes = maybe (Fin._> # 128) ⊤ ∘ head

leastBytes? : Decidable LeastBytes
leastBytes? [] = yes tt
leastBytes? (b ∷ bs) = (# 128) Fin.<? b

leastBytesUnique : ∀ {bs} → Unique (LeastBytes bs)
leastBytesUnique{[]} tt tt = refl
leastBytesUnique{b ∷ bs} x₁ x₂ = ≤-irrelevant x₁ x₂
  where open import Data.Nat.Properties

record OIDSub (@0 bs : List UInt8) : Set where
  constructor mkOIDSub
  field
    lₚ : List UInt8
    @0 lₚ≥128 : All (λ d → toℕ d ≥ 128) lₚ
    lₑ   : UInt8
    @0 lₑ<128 : toℕ lₑ < 128
    @0 leastDigs : LeastBytes lₚ
    @0 bs≡ : bs ≡ lₚ ∷ʳ lₑ

-- TODO: sharpen this
RawOIDSub : Raw OIDSub
Raw.D RawOIDSub = List UInt8
Raw.to RawOIDSub (_ , mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs bs≡) = lₚ ∷ʳ lₑ

OIDValue : @0 List UInt8 → Set
OIDValue = NonEmptySequenceOf OIDSub

RawOIDValue : Raw OIDValue
RawOIDValue = RawBoundedSequenceOf RawOIDSub

OID : @0 List UInt8 → Set
OID = TLV Tag.ObjectIdentifier OIDValue

RawOID : Raw OID
RawOID = RawTLV RawOIDValue
