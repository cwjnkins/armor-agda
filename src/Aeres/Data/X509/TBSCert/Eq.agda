{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey
open import Aeres.Data.X509.RDN
open import Aeres.Data.X509.SignAlg
open import Aeres.Data.X509.TBSCert.Properties
open import Aeres.Data.X509.TBSCert.TCB
open import Aeres.Data.X509.TBSCert.UID.TCB
open import Aeres.Data.X509.TBSCert.Version
open import Aeres.Data.X509.Validity
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Int
import      Aeres.Data.X690-DER.OctetString.Properties
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ TBSCertFields
  eq≋ =
    Iso.isoEq≋ iso
      (Seq.eq≋&ₚ (Seq.eq≋&ₚ it it)
        (Seq.eq≋&ₚ it
          (Seq.eq≋&ₚ it
            (Seq.eq≋&ₚ it
              (Seq.eq≋&ₚ it
                (Seq.eq≋&ₚ
                  (Parallel.eq≋Σₚ it λ _ →
                    record
                      { _≟_ = λ where
                        self self → yes refl
                      })
                  (Seq.eq≋&ₚ it (Seq.eq≋&ₚ it it))))))))
    where
    instance
      e₁ : Eq≋ (NonEmptySequenceOf Extension)
      e₁ = SequenceOf.BoundedSequenceOfEq≋

  eq : Eq (Exists─ _ TBSCertFields)
  eq = Eq≋⇒Eq it
