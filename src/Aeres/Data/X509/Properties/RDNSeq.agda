{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
import      Aeres.Data.X509.Properties.RDNATVFields as RDNATVFieldsProps
import      Aeres.Data.X509.Properties.Seq          as SeqProps
import      Aeres.Data.X509.Properties.TLV          as TLVProps

module Aeres.Data.X509.Properties.RDNSeq where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

module RDN where
  @0 unambiguous : Unambiguous X509.RDN
  unambiguous =
    TLVProps.unambiguous
      (SeqProps.unambiguous
        (TLVProps.unambiguous RDNATVFieldsProps.unambiguous)
        TLVProps.nonempty TLVProps.nonnesting)

@0 unambiguous : Unambiguous X509.RDNSeq
unambiguous =
  TLVProps.unambiguous
    (SeqProps.unambiguous
      RDN.unambiguous TLVProps.nonempty TLVProps.nonnesting)
