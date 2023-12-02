open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.Properties
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X690-DER.Default
open import Aeres.Data.X690-DER.Int
import      Aeres.Data.X690-DER.OctetString.Properties as OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.GeneralSubtree.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ GeneralSubtreeFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it (Seq.eq≋&ₚ (Default.eq≋ _) it))
