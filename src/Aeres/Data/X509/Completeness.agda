{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
  hiding (module Generic)
open import Aeres.Prelude

module Aeres.Data.X509.Completeness where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private 
  module Generic where
    open import Aeres.Grammar.Parser.Completeness UInt8 public
    open Proofs (Logging ∘ Dec) Logging.val public

open Generic.Definitions (Logging ∘ Dec) Logging.val

@0 soundness : Sound parseCert
soundness = Generic.soundness parseCert

@0 weakCompleteness : WeaklyComplete parseCert
weakCompleteness = Generic.weakCompleteness parseCert

@0 strongCompleteness : StronglyComplete parseCert
strongCompleteness = Generic.strongCompleteness parseCert Cert.unambiguous TLV.nosubstrings

