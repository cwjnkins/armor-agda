{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.TBSCertFields as TBSCert
import      Aeres.Data.X509.Properties.SignAlgFields as SignAlg
import      Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Cert where

open Aeres.Grammar.Definitions UInt8

Rep : @0 List UInt8 → Set
Rep = &ₚ X509.TBSCert (&ₚ X509.SignAlg BitString)

postulate -- Joy
  equiv : Equivalent Rep X509.CertFields
  iso   : Iso Rep X509.CertFields

instance
  CertEq : Eq (Exists─ (List UInt8) X509.Cert)
  CertEq = Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ (isoEq iso eq) ⦄)
    where
    eq : Eq (Exists─ (List UInt8) Rep)
    eq = eq&ₚ it (eq&ₚ (Eq≋⇒Eq it) (Eq≋⇒Eq (TLV.EqTLV ⦃ Eq⇒Eq≋ BitString.eq ⦄)))
