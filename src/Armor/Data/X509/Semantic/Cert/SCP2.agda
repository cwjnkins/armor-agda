open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.SCP2 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.9
-- Extension field MUST only appear if the Version is 3(2).

SCP2 : ∀ {@0 bs} → Cert bs → Set
SCP2 c = T (isSome (proj₂ (Cert.getExtensions c))) → Cert.getVersion c ≡ TBSCert.v3

scp2 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP2 c)
scp2 c = T-dec →-dec _ ≟ TBSCert.v3
