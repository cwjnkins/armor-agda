open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.SCP4 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.2
-- The Serial number MUST be a positive integer assigned by the CA to each certificate.

SCP4 : ∀ {@0 bs} → Cert bs → Set
SCP4 c = ℤ.+ 0 ℤ.< Cert.getSerial c

scp4 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP4 c)
scp4 c = (ℤ.+ 0 ℤ.<? Cert.getSerial c)
