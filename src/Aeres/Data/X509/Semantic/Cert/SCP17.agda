{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP17 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.
SCP17 : ∀ {@0 bs} → Cert bs → Set
SCP17 c = T (checkCRLDistStruct (Cert.getCRLDIST c))

scp17 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP17 c)
scp17 c = T-dec

