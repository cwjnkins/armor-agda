{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.DirectoryString where

open Base256

module parseDirectoryString where
  here' = "parseDirectoryString"
  open ≡-Reasoning

  parseDirectoryString : Parser Dig (Logging ∘ Dec) X509.DirectoryString
  runParser parseDirectoryString xs = do
    no ¬teletex ← runParser parseTeletexString xs
      where yes t → return (yes (mapSuccess Dig (λ {bs} → X509.teletexString{bs}) t))
    no ¬printable ← runParser parsePrintableString xs
      where yes p → return (yes (mapSuccess Dig (λ {bs} → X509.printableString{bs}) p))
    no ¬universal ← runParser parseUniversalString xs
      where yes u → return (yes (mapSuccess Dig (λ {bs} → X509.universalString{bs}) u))
    no ¬utf8 ← runParser parseUTF8String xs
      where yes u → return (yes (mapSuccess Dig (λ {bs} → X509.utf8String{bs}) u))
    no ¬bmp ← runParser parseBMPString xs
      where yes b → return (yes (mapSuccess Dig (λ {bs} → X509.bmpString{bs}) b))
    return ∘ no $ λ where
      (success prefix read read≡ (X509.teletexString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬teletex
      (success prefix read read≡ (X509.printableString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬printable
      (success prefix read read≡ (X509.universalString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬universal
      (success prefix read read≡ (X509.utf8String x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬utf8
      (success prefix read read≡ (X509.bmpString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬bmp

open parseDirectoryString public using (parseDirectoryString)

private                         
  module Test where

  Dir₁ : List Dig
  Dir₁ = Tag.TeletexString ∷ # 2 ∷ # 85 ∷ [ # 87 ]

  Dir₂ : List Dig
  Dir₂ = Tag.PrintableString ∷ # 2 ∷ # 85 ∷ [ # 87 ]


  test₁ : X509.DirectoryString Dir₁
  test₁ = Success.value (toWitness {Q = Logging.val (runParser parseDirectoryString Dir₁)} tt)

  test₂ : X509.DirectoryString Dir₂
  test₂ = Success.value (toWitness {Q = Logging.val (runParser parseDirectoryString Dir₂)} tt)
