open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude
open import Relation.Nullary.Implication

module Aeres.Data.X509.Semantic.Cert.SCP6 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.6
-- If the Subject is a CA (e.g., the Basic Constraints extension, is present and the value of CA is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.

SCP6 : ∀ {@0 bs} → Cert bs → Set
SCP6 c = T (isCA (Cert.getBC c)) → (0 < Cert.getSubjectLen c)

scp6 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP6 c)
scp6 c = T-dec →-dec 0 <? _
