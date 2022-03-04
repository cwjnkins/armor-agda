{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TCB.TLV
import      Aeres.Data.X690-DER.TCB.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.BitString where

open Base256

UnusedBits : Dig → List Dig → Set
UnusedBits bₕ [] = toℕ bₕ ≡ 0
UnusedBits bₕ (bₜ ∷ []) = toℕ bₜ %2^ (toℕ bₕ) ≡ 0
UnusedBits bₕ (bₜ ∷ x ∷ bₜ') = UnusedBits bₕ (x ∷ bₜ')

toBitRep : Dig → List Dig → List Bool
toBitRep bₕ [] = []
toBitRep bₕ (bₜ ∷ []) = take (8 - toℕ bₜ) (Vec.toList{n = 8} (toBinary bₜ))
toBitRep bₕ (bₜ ∷ x ∷ bₜ') = Vec.toList{n = 8} (toBinary bₜ) ++ toBitRep bₕ (x ∷ bₜ')

record BitStringValue (@0 bs : List UInt8) : Set where
    constructor mkBitStringValue
    field
      @0 bₕ : Dig
      @0 bₜ : List Dig
      @0 bₕ<8 : toℕ bₕ < 8
      bits : Singleton (toBitRep bₕ bₜ)
      @0 unusedBits : UnusedBits bₕ bₜ
      @0 bs≡ : bs ≡ bₕ ∷ bₜ

BitString : @0 List UInt8 → Set
BitString = TLV Tag.BitString BitStringValue
