{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.SCP8 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
-- Where it appears, the PathLenConstraint field MUST be greater than or equal to zero.

SCP8' : Exists─ (List UInt8) (Option Int) → Set
SCP8' (─ .[] , none) = ⊤
SCP8' (fst , some x) = ℤ.+ 0 ℤ.≤ Int.getVal x

SCP8 : ∀ {@0 bs} → Cert bs → Set
SCP8 c = SCP8' (getBCPathLen (Cert.getBC c))

scp8 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP8 c)
scp8 c =
  case (getBCPathLen (Cert.getBC c)) ret (λ x → Dec (SCP8' x)) of λ where
    (─ .[] , none) → yes tt
    (fst , some x) → ℤ.+ 0 ℤ.≤? Int.getVal x
