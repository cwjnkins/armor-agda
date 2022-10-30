{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.EcPkAlg.Params.Curve.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.EcPkAlg.Params.Curve.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open ≡-Reasoning

Rep = &ₚ (&ₚ OctetString OctetString) (Option BitString)

equivalent : Equivalent Rep CurveFields
proj₁ equivalent (mk&ₚ (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) = mkCurveFields fstₚ₁ sndₚ₂ sndₚ₁
  (begin (_ ≡⟨ bs≡ ⟩ ++-assoc bs₁ bs₂ _))
proj₂ equivalent (mkCurveFields{p}{q} a b seed bs≡) = mk&ₚ (mk&ₚ a b refl) seed
  (begin (_ ≡⟨ bs≡ ⟩ sym (++-assoc p q _)))


iso : Iso (&ₚ (&ₚ OctetString OctetString) (Option BitString)) CurveFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ{bs₂ = bs₃} (mk&ₚ{bs₁ = bs₁}{bs₂} a b refl) seed refl) = ‼
  ≡-elimₖ
    (λ e → mk&ₚ (mk&ₚ a b refl) seed e ≡  mk&ₚ (mk&ₚ a b refl) seed refl)
    refl
    (trans (++-assoc bs₁ bs₂ bs₃) (sym ((++-assoc bs₁ bs₂ bs₃))))
proj₂ (proj₂ iso) (mkCurveFields a b seed refl) = ‼
  ≡-elimₖ
    (λ e → mkCurveFields a b seed e ≡ mkCurveFields a b seed refl)
    refl _

@0 unambiguous : Unambiguous CurveFields
unambiguous = isoUnambiguous iso
  (unambiguous&ₚ (unambiguous&ₚ (TLV.unambiguous OctetString.unambiguous) TLV.nonnesting (TLV.unambiguous OctetString.unambiguous))
    (NonNesting&ₚ TLV.nonnesting TLV.nonnesting)
      (Unambiguous.option₁ (TLV.unambiguous BitString.unambiguous) TLV.nonempty))
