open import Armor.Binary
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso DistPointFieldsRep DistPointFields
proj₁ iso = equivalentDistPointFields
proj₁ (proj₂ iso) (mk×ₚ (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) nor)
  with T-irrel nor
... | nor'
  with ‼ T-unique nor nor'
... | refl = refl
proj₂ (proj₂ iso) (mkDistPointFields crldp crldprsn crlissr nor refl)
  with T-irrel nor
... | nor'
  with ‼ T-unique nor nor'
... | refl = refl

@0 unambiguous' : Unambiguous (&ₚ (Option DistPointName) (&ₚ (Option ReasonFlags) (Option CrlIssuer)))
unambiguous' =
  Seq.unambiguous₂Option₃
    Name.unambiguous TLV.nosubstrings TLV.nonempty
    (TLV.unambiguous BitString.unambiguousValue) TLV.nosubstrings TLV.nonempty
    (TLV.unambiguous GeneralNames.GeneralNamesElems.unambiguous) TLV.nonempty
    (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())

@0 unambiguous : Unambiguous DistPoint
unambiguous =
  TLV.unambiguous (Iso.unambiguous iso
    (Parallel.unambiguous unambiguous' (λ _ → T-unique)))

@0 nonmalleable : NonMalleable RawDistPoint
nonmalleable = TLV.nonmalleable (Iso.nonmalleable iso RawDistPointFieldsRep nm)
  where
  nm : NonMalleable RawDistPointFieldsRep
  nm = Parallel.nonmalleable₁ _
         (Seq.nonmalleable (Option.nonmalleable _ Name.nonmalleable)
         (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable BitString.nonmalleableValue))
                           (Option.nonmalleable _ (TLV.nonmalleable GeneralNames.GeneralNamesElems.nonmalleable))))
         λ _ → T-unique
