{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.BitString.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

UnusedBits : UInt8 → List UInt8 → Set
UnusedBits bₕ [] = toℕ bₕ ≡ 0
UnusedBits bₕ (bₜ ∷ []) = drop (8 - toℕ bₕ) (Vec.toList (toBinary{8} bₜ)) ≡ replicate (toℕ bₕ) #0
UnusedBits bₕ (bₜ ∷ x ∷ bₜ') = UnusedBits bₕ (x ∷ bₜ')

toBitRep : UInt8 → List UInt8 → List Bool
toBitRep bₕ [] = []
toBitRep bₕ (bₜ ∷ [])= take (8 - toℕ bₕ) (Vec.toList{n = 8} (toBinary bₜ))
toBitRep bₕ (bₜ ∷ x ∷ bₜ') = Vec.toList{n = 8} (toBinary bₜ) ++ toBitRep bₕ (x ∷ bₜ')

record BitStringValue (@0 bs : List UInt8) : Set where
    constructor mkBitStringValue
    field
      @0 bₕ : UInt8
      @0 bₜ : List UInt8
      @0 bₕ<8 : toℕ bₕ < 8
      bits : Singleton (toBitRep bₕ bₜ)
      @0 unusedBits : UnusedBits bₕ bₜ
      @0 bs≡ : bs ≡ bₕ ∷ bₜ

BitString : @0 List UInt8 → Set
BitString = TLV Tag.BitString BitStringValue

RawBitStringValue : Raw BitStringValue
Raw.D RawBitStringValue = List Bool
Raw.to RawBitStringValue = uncurry─ (↑_ ∘ BitStringValue.bits)
