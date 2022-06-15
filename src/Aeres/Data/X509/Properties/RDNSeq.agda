{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
import      Aeres.Data.X509.Properties.RDNATVFields as RDNATVFieldsProps
open import Aeres.Data.X690-DER
open import Data.Nat.Properties

module Aeres.Data.X509.Properties.RDNSeq where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

module RDN where
  @0 unambiguous : Unambiguous X509.RDN
  unambiguous =
    TLV.unambiguous
      (unambiguousΣₚ
        (SequenceOf.unambiguous
          (TLV.unambiguous RDNATVFieldsProps.unambiguous)
          TLV.nonempty
          TLV.nonnesting)
        (λ atv pf₁ pf₂ → ≤-irrelevant pf₁ pf₂))

@0 unambiguous : Unambiguous X509.RDNSeq
unambiguous =
  TLV.unambiguous
    (SequenceOf.unambiguous
      RDN.unambiguous TLV.nonempty TLV.nonnesting)
