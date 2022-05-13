{-# OPTIONS --subtyping #-}

open import Aeres.Binary renaming (module Base64 to B64)
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude
import      Aeres.Data.Base64.TCB as Base64

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Sum         Char

module Aeres.Data.Base64.Properties where

module Base64Char where
  Rep : @0 List Char → Set
  Rep =
    Σₚ (Erased ∘ (ExactLengthString 1))
       λ where
         ._ (─ xs) →
           let @0 c : Char
               c = lookupELS xs (# 0)
           in Exists─ (c ∈ B64.charset) (λ c∈ → Singleton (Any.index c∈))

  equiv : Equivalent Rep Base64.Base64Char
  proj₁ equiv {xs“} (mk×ₚ (─ xs'@(mk×ₚ self (─ xsLen) refl)) (─ c∈ , i) refl) =
    Base64.mk64 (lookupELS xs' (# 0)) c∈ i (‼ lem xsLen)
    where
    @0 lem : ∀ {xs“} (xsLen : length xs“ ≡ 1)
             → xs“ ≡ [ lookupELS (mk×ₚ (singleton xs“ refl) (─ xsLen) refl) (# 0) ]
    lem {x ∷ []} refl = refl
  proj₂ equiv (Base64.mk64 c c∈ i refl) =
    mk×ₚ (─ (mk×ₚ (singleton (c ∷ []) refl) (─ refl) refl)) ((─ c∈) , i) refl

module Base64Str where
  Rep : @0 List Char → Set
  Rep = (&ₚ (IList Base64.Base64Char) Base64.Pad) ×ₚ λ bs → length bs % 4 ≡ 0

  equiv : Equivalent Rep Base64.Base64Str
  proj₁ equiv (mk×ₚ (mk&ₚ{bs₁}{bs₂} cs p refl) %4 refl) =
    Base64.mk64Str bs₁ bs₂ cs p %4 refl
  proj₂ equiv (Base64.mk64Str s p str pad mult refl) =
    mk×ₚ (mk&ₚ str pad refl) (‼ mult) refl
