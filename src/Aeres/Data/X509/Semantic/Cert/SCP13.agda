{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude
open import Relation.Nullary.Implication

module Aeres.Data.X509.Semantic.Cert.SCP13 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
-- If the KeyCertSign bit is asserted, then the CA bit in the Basic Constraints extension MUST also be asserted.

SCP13 : ∀ {@0 bs} → Cert bs → Set
SCP13 c = T (isKeyCertSignPresent (Cert.getKU c)) → T (isCA (Cert.getBC c))

scp13 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP13 c)
scp13 c = T-dec →-dec T-dec
