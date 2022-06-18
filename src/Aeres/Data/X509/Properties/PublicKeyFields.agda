{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.BitstringValue as BitstringProps
import      Aeres.Data.X509.Properties.SignAlgFields  as SignAlgFieldsProps
import      Aeres.Data.X509.Properties.PkAlg          as PkAlgProps
import      Aeres.Data.X509.Properties.PkVal          as PkValProps
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PublicKeyFields where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning

Rep : @0 List UInt8 → Set
Rep = &ₚᵈ X509.PkAlg λ _ → X509.PkVal ∘ X509.PkAlg.getOID

equivalent : Equivalent Rep X509.PublicKeyFields
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkPublicKeyFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (X509.mkPublicKeyFields pkalg pubkey bs≡) = Aeres.Grammar.Definitions.mk&ₚ pkalg pubkey bs≡

iso : Iso Rep X509.PublicKeyFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkPublicKeyFields pkalg pubkey bs≡) = refl

@0 unambiguous : Unambiguous X509.PublicKeyFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚᵈ PkAlgProps.unambiguous PkAlgProps.nonnesting
      λ _ → PkValProps.unambiguous _)

nonnesting : NonNesting X509.PublicKeyFields
nonnesting{xs₁}{ys₁}{xs₂}{ys₂} x (X509.mkPublicKeyFields {alg = alg} {pk = pk} pkalg pubkey bs≡) (X509.mkPublicKeyFields {alg = alg₁} {pk = pk₁} pkalg₁ pubkey₁ bs≡₁) = {!!}
