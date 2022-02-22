{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.Length where

open Base256

record Short (@0 bs : List UInt8) : Set where
  constructor mkShort
  field
    l : UInt8
    @0 l<128 : toℕ l < 128
    @0 bs≡ : bs ≡ [ l ]

-- Needs to be proof irrelevant (UP)
MinRepLong : UInt8 → List UInt8 → Set
MinRepLong lₕ lₜ =
  if ⌊ lₜ ≟ [] ⌋ then toℕ lₕ ≥ 128 else ⊤

record Long (@0 bs : List UInt8) : Set where
  constructor mkLong
  field
    l : UInt8
    @0 l>128 : 128 < toℕ l
    lₕ : UInt8
    @0 lₕ≢0 : toℕ lₕ > 0
    lₜ : List UInt8
    @0 lₜLen : length lₜ ≡ toℕ l - 129
    @0 lₕₜMinRepLong : MinRepLong lₕ lₜ
    @0 bs≡ : bs ≡ l ∷ lₕ ∷ lₜ

data Length : (@0 _ : List UInt8) → Set where
  short : ∀ {@0 bs} → Short bs → Length bs
  long  : ∀ {@0 bs} → Long  bs → Length bs

-- read the value of a length field
getLength : ∀ {@0 bs} → Length bs → ℕ
getLength {bs} (short (mkShort l l<128 bs≡)) = toℕ l
getLength {bs} (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen _ bs≡)) = go (reverse (lₕ ∷ lₜ))
  where
  go : List Dig → ℕ
  go [] = 0
  go (b ∷ bs') = toℕ b + 256 * go bs'

