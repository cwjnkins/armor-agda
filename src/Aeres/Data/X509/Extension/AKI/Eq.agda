open import Aeres.Binary
open import Aeres.Data.X509.Extension.AKI.Properties
open import Aeres.Data.X509.Extension.AKI.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Seq

open import Aeres.Prelude

module Aeres.Data.X509.Extension.AKI.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ AKIFieldsSeqFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it (Seq.eq≋&ₚ it it))
