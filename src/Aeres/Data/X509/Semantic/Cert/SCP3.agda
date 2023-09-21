{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP3 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- At a minimum, conforming implementations MUST recognize Version 3 certificates.
-- Generation of Version 2 certificates is not expected by implementations based on this profile.
-- note : but, version 1 and 2 certs can be present for CA certificates. So, we are checking whether
-- the version is 1, 2, or 3 (0 - 2).
SCP3 : ∀ {@0 bs} → Cert bs → Set
SCP3 c = ((Cert.getVersion c ≡ ℤ.+ 0) ⊎ (Cert.getVersion c ≡  ℤ.+ 1)) ⊎ (Cert.getVersion c ≡  ℤ.+ 2)

scp3 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP3 c)
scp3 c = ((Cert.getVersion c ≟ ℤ.+ 0) ⊎-dec (Cert.getVersion c ≟  ℤ.+ 1)) ⊎-dec (Cert.getVersion c ≟  ℤ.+ 2)