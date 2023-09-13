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

module Aeres.Data.X509.Semantic.Cert.SCP19 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

--- consistency of certificate purposes based on key usage bits and extended key usage OIDs
SCP19 : ∀ {@0 bs} → Cert bs → Set
SCP19 c = T (checkPurposeConsistency (Cert.getKU c) (getEKUOIDList (Cert.getEKU c)))

scp19 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP19 c)
scp19 c = T-dec

