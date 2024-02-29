open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R10 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.6
-- The subject name MAY be carried in the subject field and/or the
-- subjectAltName extension.
-- [...]
-- If subject naming information is present only in the Subject Alternative Name extension ,
-- then the Subject name MUST be an empty sequence and the Subject
-- Alternative Name extension MUST be critical.

-- is SAN extension critical ? 
isSANCritical : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.SANLit) Extension.SANFields)) → Bool
isSANCritical (─ _ , none) = false
isSANCritical (─ _ , some san) = ExtensionFields.getCrit san

R10 : ∀ {@0 bs} → Cert bs → Set
R10 c = 0 ≡ SequenceOf.length (Name.getRDNs (Cert.getSubject c)) → T (isSANCritical (Cert.getSAN c))

r10 : ∀ {@0 bs} (c : Cert bs) → Dec (R10 c)
r10 c = 0 ≟ _ →-dec T-dec
