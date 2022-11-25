{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Cert.Properties
open import Aeres.Data.X509.Cert.TCB
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X509.SignAlg
open import Aeres.Data.X509.TBSCert
import      Aeres.Data.X509.TBSCert.UID.TCB as TBSCert
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Cert.Eq where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.IList        UInt8
open Aeres.Grammar.Option       UInt8

instance
  eq≋ : Eq≋ CertFields
  eq≋ = isoEq≋ iso
          (eq≋&ₚ (eq≋Σₚ it λ _ → it)
            (eq≋&ₚ it (eq≋Σₚ it λ _ → it)))

  eq : Eq (Exists─ _ CertFields)
  eq = Eq≋⇒Eq it
