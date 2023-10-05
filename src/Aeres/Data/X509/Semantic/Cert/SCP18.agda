{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP18 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- The certificate Validity period includes the current time
SCP18 : ∀ {@0 bs₁ bs₂} → Cert bs₁ → Validity.Time bs₂ → Set
SCP18 c t = Validity.ValidTime t (Cert.getValidity c)
  -- T (Time.lessEq (proj₂ (Cert.getValidityStartTime c)) t ∧ Time.lessEq t (proj₂ (Cert.getValidityEndTime c)))

scp18 : ∀ {@0 bs₁ bs₂} → (c : Cert bs₁) → (t : Validity.Time bs₂) → Dec (SCP18 c t)
scp18 c t = Validity.validTime? t (Cert.getValidity c)
