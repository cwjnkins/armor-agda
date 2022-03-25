{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary

module Aeres.Data.UTF8 where

open import Aeres.Data.UTF8.TCB    public
open import Aeres.Data.UTF8.Parser public

open Base256

mapUTF8Char1Range
  : (low range : ℕ) (shift : ℤ)
    → ℤ.+0    ℤ.≤ (ℤ.+ low) ℤ.+ shift
    → ℤ.+ 127 ℤ.≥ (ℤ.+_ ∘ (_+ range) $ low) ℤ.+ shift
    → ∀ {@0 bs} → UTF8Char1 bs
    → Exists─ (List UInt8) UTF8Char1
mapUTF8Char1Range low range shift 0≤ 128≥ c
  with toℕ (utf81 c) ≥? low
  |    toℕ (utf81 c) ≤? low + range
... | no _ | _ = _ , c
... | yes _ | no _ = _ , c
... | yes low≤ | yes low+range≥ =
  _ , mkUTF8Char1 dUInt8 (s≤s (subst (_≤ 127) (sym (Fin.toℕ-fromℕ< dℕ<256)) dℕ≤127)) refl
  where
    open import Data.Nat.Properties
    import      Data.Integer.Properties as ℤ
    import      Data.Fin.Properties     as Fin

    dℤ = (ℤ.+_ ∘ toℕ ∘ utf81 $ c) ℤ.+ shift

    0≤dℤ : ℤ.+0 ℤ.≤ dℤ
    0≤dℤ = begin
      ℤ.+0 ≤⟨ 0≤ ⟩
      ℤ.+ low ℤ.+ shift ≤⟨ ℤ.+-monoˡ-≤ shift (ℤ.+≤+ low≤) ⟩
      dℤ ∎
      where
      open ℤ.≤-Reasoning

    dℤ≤128 : ℤ.+ 127 ℤ.≥ dℤ
    dℤ≤128 = begin
      ℤ.+ (toℕ (utf81 c)) ℤ.+ shift ≤⟨ ℤ.+-monoˡ-≤ shift (ℤ.+≤+ low+range≥) ⟩
      ℤ.+ (low + range) ℤ.+ shift ≤⟨ 128≥ ⟩
      ℤ.+ 127 ∎
      where
      open ℤ.≤-Reasoning

    dℤ≡ : Σ[ n ∈ ℕ ] ℤ.+ n ≡ dℤ
    dℤ≡ with ℤ.nonNegative 0≤dℤ
    ... | nn
       with dℤ
    ... | ℤ.+ n = n , refl

    dℕ = proj₁ dℤ≡

    dℕ≤127 : dℕ ≤ 127
    dℕ≤127 with subst ((ℤ.+ 127) ℤ.≥_) (sym (proj₂ dℤ≡)) dℤ≤128
    ... | ℤ.+≤+ m≤n = m≤n

    dℕ<256 = ≤-trans (s≤s dℕ≤127) (toWitness{Q = _ ≤? _} tt)

    dUInt8 : UInt8
    dUInt8 = Fin.fromℕ< dℕ<256
