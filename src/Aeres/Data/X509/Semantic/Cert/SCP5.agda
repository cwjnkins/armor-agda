{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP5 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
-- The Issuer field MUST contain a non-empty distinguished name (DN).
-- TODO : fix the parser to enforce set length to minimum 1

SCP5 : ∀ {@0 bs} → Cert bs → Set
SCP5 c = 0 < Cert.getIssuerLen c 

scp5 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP5 c)
scp5 c = 0 <? Cert.getIssuerLen c 
