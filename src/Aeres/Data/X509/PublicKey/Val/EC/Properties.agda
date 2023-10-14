{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel   
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Seq         UInt8

@0 unambiguous : Unambiguous ECBitString
unambiguous =
  TLV.unambiguous
    (Seq.unambiguous ≡-unique (λ where _ refl refl → refl) OctetString.unambiguousValue)

@0 nonmalleable : NonMalleable RawECBitString
nonmalleable =
  TLV.nonmalleable
    (Seq.nonmalleable
      (subsingleton⇒nonmalleable (λ where (─ _ , refl) (─ _ , refl) → refl))
      OctetString.nonmalleableValue)
