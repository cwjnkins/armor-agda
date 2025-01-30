open import Armor.Binary
open import Armor.Data.X509.CRL.Extension.IDP.Properties
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq

open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.IDP.Eq where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ IDPFieldsSeqFields
  eq≋ = Iso.isoEq≋ iso (Parallel.eq≋Σₚ (Seq.eq≋&ₚ it (Seq.eq≋&ₚ (Default.eq≋ [ Tag.A81 ]falseBoool)
                                           (Seq.eq≋&ₚ (Default.eq≋ [ Tag.A82 ]falseBoool) (Seq.eq≋&ₚ it (Seq.eq≋&ₚ
                                           (Default.eq≋ [ Tag.A84 ]falseBoool) (Default.eq≋ [ Tag.A85 ]falseBoool))))))
           (λ _ → record { _≟_ = λ x y → yes (T-unique x y) }))
