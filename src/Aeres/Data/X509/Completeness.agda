{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Cert
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Completeness where

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Parser      Dig

completeness : ∀ {bs} → Success X509.Cert bs → True (Logging.val (runParser parseCert bs))
completeness{bs} cert
  with Logging.val $ runParser parseCert bs
... | (yes _) = tt
... | no ¬cert = contradiction cert ¬cert
