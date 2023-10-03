{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Time.UTCTime.TCB
open import Aeres.Data.X690-DER.Time.MDHMS
open import Aeres.Data.X690-DER.Time.TimeType
open import Aeres.Data.X690-DER.Time.Year
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.UTCTime.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

@0 nosubstrings : NoSubstrings UTCTimeFields
nosubstrings =
  Iso.nosubstrings equivalent
    (Seq.nosubstrings TimeType.nosubstrings
    (Seq.nosubstrings MDHMS.nosubstrings (λ where _ refl refl → refl)))

iso : Iso UTCTimeFieldsRep UTCTimeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ year (mk&ₚ mdhms refl refl) bs≡) = refl
proj₂ (proj₂ iso) (mkUTCTime year mdhms bs≡) = refl

@0 unambiguousFields : Unambiguous UTCTimeFields
unambiguousFields =
  Iso.unambiguous iso
    (Seq.unambiguous TimeType.unambiguous TimeType.nosubstrings
    (Seq.unambiguous MDHMS.unambiguous MDHMS.nosubstrings
    ≡-unique))

@0 unambiguous : Unambiguous UTCTime
unambiguous = TLV.unambiguous unambiguousFields

@0 nonmalleableFields : NonMalleable RawUTCTimeFields
nonmalleableFields =
  Iso.nonmalleable iso RawUTCTimeFieldsRep nm
  where
  nm : NonMalleable RawUTCTimeFieldsRep
  nm =  Seq.nonmalleable TimeType.nonmalleable
       (Seq.nonmalleable MDHMS.nonmalleable
                         (subsingleton⇒nonmalleable (λ where (─ _ , refl) (─ _ , refl) → refl)))

@0 nonmalleable : NonMalleable RawUTCTime
nonmalleable = TLV.nonmalleable nonmalleableFields
