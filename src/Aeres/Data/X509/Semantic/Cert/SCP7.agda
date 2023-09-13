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

module Aeres.Data.X509.Semantic.Cert.SCP7 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- Unique Identifiers fields MUST only appear if the Version is 2 or 3.
SCP7₁ : ∀ {@0 bs} → Cert bs → Set
SCP7₁ c = T (isSome (proj₂ (Cert.getSubUID c))) → (Cert.getVersion c ≡ ℤ.+ 1 ⊎ Cert.getVersion c ≡  ℤ.+ 2)

SCP7₂ : ∀ {@0 bs} → Cert bs → Set
SCP7₂ c = T (isSome (proj₂ (Cert.getIssUID c))) → (Cert.getVersion c ≡ ℤ.+ 1 ⊎ Cert.getVersion c ≡  ℤ.+ 2)

scp7₁ : ∀ {@0 bs} (c : Cert bs) → Dec (SCP7₁ c)
scp7₁ c = T-dec →-dec ((_ ≟ ℤ.+ 1) ⊎-dec (_ ≟ ℤ.+ 2))

scp7₂ : ∀ {@0 bs} (c : Cert bs) → Dec (SCP7₂ c)
scp7₂ c = T-dec →-dec (_ ≟ ℤ.+ 1 ⊎-dec _ ≟ ℤ.+ 2)
