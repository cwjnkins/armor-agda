{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP16 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- A certificate policy OID MUST NOT appear more than once in a Certificate Policies extension.
SCP16 : ∀ {@0 bs} → Cert bs → Set
SCP16 c = List.Unique _≟_ (getPolicyOIDList (Cert.getCPOL c))

scp16 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP16 c)
scp16 c = List.unique? _≟_ (getPolicyOIDList (Cert.getCPOL c))
