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

module Aeres.Data.X509.Semantic.Cert.SCP9 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- if the Subject is a CRL issuer (e.g., the Key Usage extension, is present and the value of CRLSign is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
SCP9 : ∀ {@0 bs} → Cert bs → Set
SCP9 c = T (isCRLSignPresent (Cert.getKU c)) → (0 < Cert.getSubjectLen c)

scp9 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP9 c)
scp9 c = T-dec →-dec 0 <? _
