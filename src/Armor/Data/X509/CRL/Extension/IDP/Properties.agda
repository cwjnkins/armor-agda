open import Armor.Binary
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.Sequence
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Default
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.CRL.Extension.IDP.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Seq         UInt8

postulate
  @0 nosubstrings : NoSubstrings  IDPFieldsSeqFields
  @0 nonempty : NonEmpty  IDPFieldsSeqFields

iso : Iso IDPFieldsSeqFieldsRep IDPFieldsSeqFields
proj₁ iso = equivalentIDPFieldsSeqFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) refl) = refl
proj₂ (proj₂ iso) (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons indirectCRL onlyContainsAttributeCerts refl) = refl

postulate 
  @0 unambiguous : Unambiguous IDPFields
 
@0 nonmalleable : NonMalleable RawIDPFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable (SequenceOf.Bounded.nonmalleable
   nonempty nosubstrings
   (Iso.nonmalleable iso RawIDPFieldsSeqFieldsRep
     (Seq.nonmalleable (Option.nonmalleable _ Name.nonmalleable)
     (Seq.nonmalleable (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
     (Seq.nonmalleable (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
     (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable BitString.nonmalleableValue))
     (Seq.nonmalleable (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
                       (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))))))))))
