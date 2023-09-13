{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP4 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- The Serial number MUST be a positive integer assigned by the CA to each certificate.
SCP4 : ∀ {@0 bs} → Cert bs → Set
SCP4 c = ℤ.+ 0 ℤ.< Cert.getSerial c

scp4 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP4 c)
scp4 c = (ℤ.+ 0 ℤ.<? Cert.getSerial c)
