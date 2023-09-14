{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.RDN.ATV
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X509.RDN.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguousElems : Unambiguous RDNElems
unambiguousElems =
  unambiguousΣₚ
    (SequenceOf.unambiguous ATV.unambiguous TLV.nonempty TLV.nonnesting)
    (λ _ _ _ → Nat.≤-irrelevant _ _)

@0 unambiguous : Unambiguous Name
unambiguous =
  TLV.unambiguous
    (SequenceOf.unambiguous (TLV.unambiguous unambiguousElems)
      TLV.nonempty
      TLV.nonnesting)

instance
  RDNElemsEq≋ : Eq≋ RDNElems
  RDNElemsEq≋ = SequenceOf.BoundedSequenceOfEq≋
