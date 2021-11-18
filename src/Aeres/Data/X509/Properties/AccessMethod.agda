{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Properties.AccessMethod where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig
open        Aeres.Grammar.Sum         Dig

@0 nonnesting : NonNesting X509.AccessMethod
nonnesting x (X509.caissid x₁) (X509.caissid x₂) = trans x₁ (sym x₂)
nonnesting () (X509.caissid refl) (X509.ocspid refl)
nonnesting () (X509.ocspid refl) (X509.caissid refl)
nonnesting x (X509.ocspid x₁) (X509.ocspid x₂) = trans x₁ (sym x₂)

iso : Iso (Sum (Erased ∘ (_≡ X509.ACMOID.CAISSUERS)) (Erased ∘ (_≡ X509.ACMOID.OCSP))) X509.AccessMethod 
proj₂ (proj₁ iso) (X509.caissid x) = inj₁ (─ x)
proj₂ (proj₁ iso) (X509.ocspid x) = inj₂ (─ x)
proj₁ (proj₁ iso) (Sum.inj₁ (─ x)) = X509.caissid x
proj₁ (proj₁ iso) (Sum.inj₂ (─ x)) = X509.ocspid x
proj₂ (proj₂ iso) (X509.caissid x) = refl
proj₂ (proj₂ iso) (X509.ocspid x) = refl
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl


@0 unambiguous : Unambiguous X509.AccessMethod
unambiguous =
  isoUnambiguous iso
    (unambiguousSum (erased-unique ≡-unique) (erased-unique ≡-unique)
      (λ where () (─ refl) (─ refl)))
