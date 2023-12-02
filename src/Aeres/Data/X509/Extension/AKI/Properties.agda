open import Aeres.Binary
open import Aeres.Data.X509.Extension.AKI.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq

open import Aeres.Prelude

module Aeres.Data.X509.Extension.AKI.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

iso : Iso AKIFieldsSeqFieldsRep AKIFieldsSeqFields
proj₁ iso = equivalentAKIFieldsSeqFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (mkAKIFieldsSeqFields akeyid authcertiss authcertsn refl) = refl

@0 unambiguous : Unambiguous AKIFields
unambiguous =
  TLV.unambiguous (TLV.unambiguous (Iso.unambiguous iso
    (Seq.unambiguous₂Option₃
      (TLV.unambiguous OctetString.unambiguousValue) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous GeneralNames.GeneralNamesElems.unambiguous) TLV.nosubstrings TLV.nonempty
      Int.[ _ ]unambiguous TLV.nonempty
      (TLV.noconfusion (λ ())) (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))))

@0 nonmalleable : NonMalleable RawAKIFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                 (Iso.nonmalleable iso RawAKIFieldsSeqFieldsRep nm))
  where
  nm : NonMalleable RawAKIFieldsSeqFieldsRep
  nm = Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable OctetString.nonmalleableValue))
      (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable GeneralNames.GeneralNamesElems.nonmalleable))
                        (Option.nonmalleable _ Int.[ _ ]nonmalleable))
