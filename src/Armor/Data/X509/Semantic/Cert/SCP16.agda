open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.SCP16 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.4
-- A certificate policy OID MUST NOT appear more than once in a Certificate Policies extension.

SCP16 : ∀ {@0 bs} → Cert bs → Set
SCP16 c = List.Unique _≟_ (getPolicyOIDList (Cert.getCPOL c))

scp16 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP16 c)
scp16 c = List.unique? _≟_ (getPolicyOIDList (Cert.getCPOL c))
