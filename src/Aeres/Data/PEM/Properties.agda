{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude
import Aeres.Data.PEM.TCB as PEM

open import Aeres.Grammar.Definitions Char
open import Aeres.Grammar.IList Char
open import Aeres.Grammar.Sum   Char

module Aeres.Data.PEM.Properties where

module CertLine where
  Rep : @0 List Char → Set
  Rep =
    &ₚ (Σₚ Singleton (λ where xs self → Erased (All (_∈ Base64.charset) xs)))
       (_≡ PEM.certEOL)

  equiv : Equivalent Rep (λ xs → ∃[ n ] PEM.CertLine n xs)
  proj₁ equiv (mk&ₚ (mk×ₚ (singleton s refl) (─ mem) refl) refl refl) =
    (length s) , (PEM.mkCertLine s mem refl refl)
  proj₂ equiv (._ , PEM.mkCertLine line valid64 refl refl) =
    mk&ₚ (mk×ₚ (singleton line refl) (─ valid64) refl) refl refl
