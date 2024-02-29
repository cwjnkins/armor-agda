open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.R4 where

open Armor.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
-- The Issuer field MUST contain a non-empty distinguished name (DN).
-- TODO : fix the parser to enforce set length to minimum 1

R4 : ∀ {@0 bs} → Cert bs → Set
R4 c = 0 ≢ SequenceOf.length (Name.getRDNs (Cert.getIssuer c))

r4 : ∀ {@0 bs} → (c : Cert bs) → Dec (R4 c)
r4 c = 0 ≠ _
