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

module Aeres.Data.X509.Semantic.Cert.SCP2 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- Extension field MUST only appear if the Version is 3(2).
SCP2 : ∀ {@0 bs} → Cert bs → Set
SCP2 c = T (isSome (proj₂ (Cert.getExtensions c))) → Cert.getVersion c ≡ ℤ.+ 2

scp2 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP2 c)
scp2 c = T-dec →-dec _ ≟ ℤ.+ 2
