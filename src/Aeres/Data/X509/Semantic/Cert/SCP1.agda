{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP1 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.1.2
-- SignatureAlgorithm field MUST contain the same algorithm identifier as
-- the Signature field in the sequence TbsCertificate.

SCP1 : ∀ {@0 bs} → Cert bs → Set
SCP1 c = Cert.getTBSCertSignAlg c ≡ Cert.getCertSignAlg c

scp1 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP1 c)
scp1 c = Cert.getTBSCertSignAlg c ≟ Cert.getCertSignAlg c
