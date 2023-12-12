open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.SCP1 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.1.2
-- SignatureAlgorithm field MUST contain the same algorithm identifier as
-- the Signature field in the sequence TbsCertificate.

SCP1 : ∀ {@0 bs} → Cert bs → Set
SCP1 c = Cert.getTBSCertSignAlg c ≡ Cert.getCertSignAlg c

scp1 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP1 c)
scp1 c = Cert.getTBSCertSignAlg c ≟ Cert.getCertSignAlg c
