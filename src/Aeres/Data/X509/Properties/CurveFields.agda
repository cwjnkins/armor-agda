{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.TLV as TLVProps
import      Aeres.Data.X509.Properties.OctetstringValue as OCProps
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.CurveFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig
open ≡-Reasoning


equivalent : Equivalent (&ₚ (&ₚ OctetString OctetString) (Option BitString)) X509.CurveFields
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ (Aeres.Grammar.Definitions.mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) = X509.mkCurveFields fstₚ₁ sndₚ₂ sndₚ₁
  (begin (_ ≡⟨ bs≡ ⟩ ++-assoc bs₁ bs₂ _))
proj₂ equivalent (X509.mkCurveFields{p}{q} a b seed bs≡) = Aeres.Grammar.Definitions.mk&ₚ (Aeres.Grammar.Definitions.mk&ₚ a b refl) seed
  (begin (_ ≡⟨ bs≡ ⟩ sym (++-assoc p q _)))


iso : Iso (&ₚ (&ₚ OctetString OctetString) (Option BitString)) X509.CurveFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ (mk&ₚ fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) = {!!}
proj₂ (proj₂ iso) (X509.mkCurveFields a b seed bs≡) = subst₀ (λ x → X509.mkCurveFields  a b seed x ≡ X509.mkCurveFields a b seed bs≡) (≡-unique bs≡ _) refl


@0 unambiguous : Unambiguous X509.CurveFields
unambiguous = isoUnambiguous iso
  (unambiguous&ₚ (unambiguous&ₚ (TLVProps.unambiguous OCProps.unambiguous) TLVProps.nonnesting (TLVProps.unambiguous OCProps.unambiguous))
    (NonNesting&ₚ TLVProps.nonnesting TLVProps.nonnesting) {!!})
