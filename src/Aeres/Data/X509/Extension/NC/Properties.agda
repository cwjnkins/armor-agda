open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree
open import Aeres.Data.X509.Extension.NC.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

iso : Iso NCFieldsSeqFieldsRep NCFieldsSeqFields
proj₁ iso = equivalentNCFieldsSeqFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkNCFieldsSeqFields permt excld refl) = refl

@0 unambiguous : Unambiguous NCFields
unambiguous = TLV.unambiguous  (TLV.unambiguous
  (Iso.unambiguous iso
    (Seq.unambiguousOption₂
      (TLV.unambiguous GeneralSubtree.unambiguous)
        TLV.nosubstrings TLV.nonempty
       (TLV.unambiguous  GeneralSubtree.unambiguous)
       TLV.nonempty (TLV.noconfusion (λ ()))))) 

@0 nonmalleable : NonMalleable RawNCFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                 (Iso.nonmalleable iso RawNCFieldsSeqFieldsRep
                 (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable GeneralSubtree.nonmalleable))
                                   (Option.nonmalleable _ (TLV.nonmalleable GeneralSubtree.nonmalleable)))))
