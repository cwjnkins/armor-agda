{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

iso : Iso DistPointFieldsRep DistPointFields
proj₁ iso = equivalentDistPointFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (mkDistPointFields crldp crldprsn crlissr refl) = refl

@0 unambiguous : Unambiguous DistPoint
unambiguous =
  TLV.unambiguous (Iso.unambiguous iso
    (Unambiguous.option₃&₂
      (Name.unambiguous) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous BitString.unambiguousValue) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous GeneralNames.GeneralNamesElems.unambiguous) TLV.nonempty
      (TLV.noconfusion (λ ())) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())))

@0 nonmalleable : NonMalleable RawDistPoint
nonmalleable = TLV.nonmalleable (Iso.nonmalleable iso RawDistPointFieldsRep
               (Seq.nonmalleable (Option.nonmalleable _ Name.nonmalleable)
               (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable BitString.nonmalleableValue))
                                 (Option.nonmalleable _ (TLV.nonmalleable GeneralNames.GeneralNamesElems.nonmalleable)))))
