{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Version where

open Base256

module parseVersion where
  here' = "parseVersion"

  open ≡-Reasoning

  parseVersion : Parser Dig (Logging ∘ Dec) X509.Version
  parseVersion = parseTLV Tag.AA0 "version" Int p
    where
    p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Int n)
    p = parseExactLength Dig Props.TLV.nonnesting (tell $ here' String.++ ": length mismatch") parseInt

open parseVersion public using (parseVersion)

private
  module Test where

    Version₁ : List Dig
    Version₁ = Tag.AA0 ∷ # 3 ∷ Tag.Integer ∷ # 1 ∷ [ # 0 ]

    Version₂ : List Dig
    Version₂ = Tag.AA0 ∷ # 3 ∷ Tag.Integer ∷ # 1 ∷ [ # 1 ]

    Version₃ : List Dig
    Version₃ = Tag.AA0 ∷ # 3 ∷ Tag.Integer ∷ # 1 ∷ [ # 2 ]

    Version₄ : List Dig
    Version₄ = Tag.AA0 ∷ # 3 ∷ Tag.Integer ∷ # 1 ∷ [ # 3 ]

    VersionBadLen : List Dig
    VersionBadLen = Tag.AA0 ∷ # 4 ∷ Tag.Integer ∷ # 1 ∷ [ # 3 ]

    test₁ : X509.Version Version₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseVersion Version₁)} tt)

    test₂ : X509.Version Version₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseVersion Version₂)} tt)

    test₃ : X509.Version Version₃
    test₃ = Success.value (toWitness {Q = Logging.val (runParser parseVersion Version₃)} tt)

    test₄ : X509.Version Version₄
    test₄ = Success.value (toWitness {Q = Logging.val (runParser parseVersion Version₄)} tt)

    test₅ : ¬ Success _ X509.Version VersionBadLen
    test₅ = toWitnessFalse {Q = Logging.val (runParser parseVersion VersionBadLen)} tt


