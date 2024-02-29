open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R5 where

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.6
-- If the Subject is a CA (e.g., the Basic Constraints extension, is present and the value of CA is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.

R5 : ∀ {@0 bs} → Cert bs → Set
R5 c = IsConfirmedCA c → 0 ≢ SequenceOf.length (Name.getRDNs (Cert.getSubject c))

r5 : ∀ {@0 bs} (c : Cert bs) → Dec (R5 c)
r5 c = (isConfirmedCA? c) →-dec (0 ≠ _)
