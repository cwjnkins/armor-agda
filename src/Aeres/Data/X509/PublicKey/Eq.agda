{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg
open import Aeres.Data.X509.PublicKey.Alg.TCB.OIDs
open import Aeres.Data.X509.PublicKey.Val
open import Aeres.Data.X509.PublicKey.Properties
open import Aeres.Data.X509.PublicKey.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ PublicKeyFields
  eq≋ =
    Iso.isoEq≋ iso
      (Seq.eq≋&ₚᵈ{A = PublicKeyAlg} (TLV.EqTLV ⦃ Alg.eq≋ ⦄) λ a → Val.eq≋{a = a})
