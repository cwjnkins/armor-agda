{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.OctetstringValue as OCProps
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Serializer
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.CurveFields where

open Base256
open Aeres.Grammar.Definitions UInt8
  hiding (module Option)
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Serializer  UInt8
open ≡-Reasoning

module Option = Aeres.Grammar.Option  UInt8

Rep = &ₚ (&ₚ OctetString OctetString) (Option BitString)

equivalent : Equivalent Rep X509.CurveFields
proj₁ equivalent (mk&ₚ (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) = X509.mkCurveFields fstₚ₁ sndₚ₂ sndₚ₁
  (begin (_ ≡⟨ bs≡ ⟩ ++-assoc bs₁ bs₂ _))
proj₂ equivalent (X509.mkCurveFields{p}{q} a b seed bs≡) = mk&ₚ (mk&ₚ a b refl) seed
  (begin (_ ≡⟨ bs≡ ⟩ sym (++-assoc p q _)))


iso : Iso (&ₚ (&ₚ OctetString OctetString) (Option BitString)) X509.CurveFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ{bs₂ = bs₃} (mk&ₚ{bs₁ = bs₁}{bs₂} a b refl) seed refl) = ‼
  ≡-elimₖ
    (λ e → mk&ₚ (mk&ₚ a b refl) seed e ≡  mk&ₚ (mk&ₚ a b refl) seed refl)
    refl
    (trans (++-assoc bs₁ bs₂ bs₃) (sym ((++-assoc bs₁ bs₂ bs₃))))
proj₂ (proj₂ iso) (X509.mkCurveFields a b seed refl) = ‼
  ≡-elimₖ
    (λ e → X509.mkCurveFields a b seed e ≡ X509.mkCurveFields a b seed refl)
    refl _

@0 unambiguous : Unambiguous X509.CurveFields
unambiguous = isoUnambiguous iso
  (unambiguous&ₚ (unambiguous&ₚ (TLV.unambiguous OCProps.unambiguous) TLV.nonnesting (TLV.unambiguous OCProps.unambiguous))
    (NonNesting&ₚ TLV.nonnesting TLV.nonnesting)
      (Unambiguous.option₁ (TLV.unambiguous BitString.unambiguous) TLV.nonempty))

serialize : Serializer X509.CurveFields
serialize =
  serializeEquivalent equivalent
    (serialize&ₚ
      (serialize&ₚ (TLV.serialize id) (TLV.serialize id))
      (Option.serialize BitString.serialize))
