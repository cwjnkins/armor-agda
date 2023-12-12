open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.SCP12 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.6
-- If the Subject Alternative Name extension is present, the sequence MUST contain at least one entry.

SCP12 : ∀ {@0 bs} → Cert bs → Set
SCP12 c = T (isSANPresent (Cert.getSAN c)) → (0 < getSANLength (Cert.getSAN c))

scp12 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP12 c)
scp12 c = T-dec →-dec 0 <? _
