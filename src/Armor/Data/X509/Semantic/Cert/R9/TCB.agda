open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
import      Data.List.Membership.Propositional as List
import      Data.List.Membership.Propositional.Properties as List
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R9.TCB where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
-- When the Key Usage extension appears in a certificate, at least one of the bits MUST be set to 1.

R9' : ∀ {@0 bs} → Option ExtensionFieldKU bs → Set
R9' none = ⊤
R9' (some ku) = ∃ λ bf → T (assertsKUBitField ku bf)

R9 : ∀ {@0 bs} → Cert bs → Set
R9 c = R9' (proj₂ (Cert.getKU c))
