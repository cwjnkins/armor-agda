{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Time.GeneralizedTime.TCB
open import Aeres.Data.X690-DER.Time.MDHMS
open import Aeres.Data.X690-DER.Time.TimeType
open import Aeres.Data.X690-DER.Time.Year
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.GeneralizedTime.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

@0 nosubstrings : NoSubstrings GeneralizedTimeFields
nosubstrings = Iso.nosubstrings equivalent
  (Seq.nosubstrings TimeType.nosubstrings
  (Seq.nosubstrings MDHMS.nosubstrings λ where _ refl refl → refl))

iso : Iso GeneralizedTimeFieldsRep GeneralizedTimeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ year (mk&ₚ mdhms refl refl) bs≡) = refl
proj₂ (proj₂ iso) (mkGeneralizedTime year mdhms bs≡) = refl

@0 unambiguousFields : Unambiguous GeneralizedTimeFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous TimeType.unambiguous TimeType.nosubstrings
    (Seq.unambiguous MDHMS.unambiguous MDHMS.nosubstrings ≡-unique))

@0 unambiguous : Unambiguous GeneralizedTime
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawGeneralizedTimeFields
nonmalleableFields =
  Iso.nonmalleable iso RawGeneralizedTimeFieldsRep nm
  where
  nm : NonMalleable RawGeneralizedTimeFieldsRep
  nm =  Seq.nonmalleable TimeType.nonmalleable
       (Seq.nonmalleable MDHMS.nonmalleable
                         (subsingleton⇒nonmalleable λ where (─ _ , refl) (─ _ , refl) → refl))

@0 nonmalleable : NonMalleable RawGeneralizedTime
nonmalleable = TLV.nonmalleable nonmalleableFields
