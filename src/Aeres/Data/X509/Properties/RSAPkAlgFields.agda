{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
open import Aeres.Data.X509
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.RSAPkAlgFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum Dig
open import Aeres.Grammar.Properties  Dig
open ≡-Reasoning

Rep = &ₚ (_≡ X509.PKOID.RsaEncPk) (_≡ X509.ExpNull)

equivalent : Equivalent Rep X509.RSAPkAlgFields
proj₁ equivalent (mk&ₚ refl refl refl) = X509.mkRSAPkAlgFields self self refl
proj₂ equivalent (X509.mkRSAPkAlgFields self self refl) = mk&ₚ refl refl refl

iso : Iso Rep X509.RSAPkAlgFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ refl refl refl) = refl
proj₂ (proj₂ iso) (X509.mkRSAPkAlgFields self self refl) = refl

@0 nonnesting : NonNesting X509.RSAPkAlgFields
nonnesting {xs₁} {ys₁} {xs₂} {ys₂} a (X509.mkRSAPkAlgFields (singleton x x≡) (singleton x₂ x≡₂) bs≡) (X509.mkRSAPkAlgFields (singleton x₁ x≡₁) (singleton x₃ x≡₃) bs≡₁) =
  (begin
    xs₁ ≡⟨ bs≡ ⟩
    x ++ x₂ ≡⟨ cong (_++ x₂) x≡  ⟩
    X509.PKOID.RsaEncPk ++ x₂ ≡⟨ cong (X509.PKOID.RsaEncPk ++_) x≡₂ ⟩
    X509.PKOID.RsaEncPk ++ X509.ExpNull ≡⟨ cong (_++ X509.ExpNull) (sym x≡₁) ⟩
    x₁ ++ X509.ExpNull ≡⟨ cong (x₁ ++_) (sym x≡₃) ⟩
    x₁ ++ x₃ ≡⟨ sym bs≡₁ ⟩
    xs₂ ∎)

@0 unambiguous : Unambiguous X509.RSAPkAlgFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ ≡-unique (λ where _ refl refl → refl) ≡-unique)
