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

module Aeres.Data.X509.Semantic.Cert.SCP10 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

SCP10 : ∀ {@0 bs} → Cert bs → Set
SCP10 c = T (isKUPresent (Cert.getKU c)) → (true ∈ getKUBits (Cert.getKU c))

scp10 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP10 c)
scp10 c = T-dec →-dec true ∈? _
