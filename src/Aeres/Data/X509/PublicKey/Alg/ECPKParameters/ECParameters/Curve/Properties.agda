open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.Curve.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8
open ≡-Reasoning

iso : Iso CurveFieldsRep CurveFields
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

@0 unambiguousFields : Unambiguous CurveFields
unambiguousFields = Iso.unambiguous iso
  (Seq.unambiguous (Seq.unambiguous OctetString.unambiguous TLV.nosubstrings OctetString.unambiguous)
    (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings)
      (Option.unambiguous BitString.unambiguous TLV.nonempty))

@0 unambiguous : Unambiguous Curve
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawCurveFields
nonmalleableFields =
  Iso.nonmalleable iso RawCurveFieldsRep
    (Seq.nonmalleable (Seq.nonmalleable OctetString.nonmalleable OctetString.nonmalleable)
      (Option.nonmalleable _ BitString.nonmalleable))

@0 nonmalleable : NonMalleable RawCurve
nonmalleable = TLV.nonmalleable nonmalleableFields
