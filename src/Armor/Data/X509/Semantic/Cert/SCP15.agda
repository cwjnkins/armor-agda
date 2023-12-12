open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.SCP15 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2
-- A certificate-using system MUST reject the certificate if it encounters a critical Extension
-- it does not recognize or a critical Extension that contains information that it cannot process.

SCP15 : ∀ {@0 bs} → Cert bs → Set
SCP15 c = T (not (isAnyOtherExtnCritical (Cert.getExtensionsList c)))

scp15 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP15 c)
scp15 c = T-dec
