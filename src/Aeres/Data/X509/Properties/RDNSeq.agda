{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
import      Aeres.Data.X509.Properties.RDNATVFields as RDNATVFieldsProps
import      Aeres.Data.X509.Properties.SequenceOf   as SeqProps
import      Aeres.Data.X509.Properties.TLV          as TLVProps
open import Data.Nat.Properties

module Aeres.Data.X509.Properties.RDNSeq where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

module RDN where
  @0 unambiguous : Unambiguous X509.RDN
  unambiguous =
    TLVProps.unambiguous
      (unambiguousΣₚ
        (SeqProps.unambiguous
          (TLVProps.unambiguous RDNATVFieldsProps.unambiguous)
          TLVProps.nonempty
          TLVProps.nonnesting)
        (λ atv pf₁ pf₂ → ≤-irrelevant pf₁ pf₂))

@0 unambiguous : Unambiguous X509.RDNSeq
unambiguous =
  TLVProps.unambiguous
    (SeqProps.unambiguous
      RDN.unambiguous TLVProps.nonempty TLVProps.nonnesting)
