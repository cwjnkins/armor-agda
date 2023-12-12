open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.SCP6 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.6
-- If the Subject is a CA (e.g., the Basic Constraints extension, is present and the value of CA is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.

SCP6 : ∀ {@0 bs} → Cert bs → Set
SCP6 c = T (isCA (Cert.getBC c)) → (0 < Cert.getSubjectLen c)

scp6 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP6 c)
scp6 c = T-dec →-dec 0 <? _
