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

module Aeres.Data.X509.Semantic.Cert.SCP11 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

SCP11 : ∀ {@0 bs} → Cert bs → Set
SCP11 c = (0 ≡ Cert.getSubjectLen c) → T (isSANCritical (Cert.getSAN c))

scp11 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP11 c)
scp11 c = 0 ≟ _ →-dec T-dec