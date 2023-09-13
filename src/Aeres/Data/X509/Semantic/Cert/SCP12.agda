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

module Aeres.Data.X509.Semantic.Cert.SCP12 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- If the Subject Alternative Name extension is present, the sequence MUST contain at least one entry.
SCP12 : ∀ {@0 bs} → Cert bs → Set
SCP12 c = T (isSANPresent (Cert.getSAN c)) → (0 < getSANLength (Cert.getSAN c))

scp12 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP12 c)
scp12 c = T-dec →-dec 0 <? _
