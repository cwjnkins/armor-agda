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

module Aeres.Data.X509.Decidable.DisplayText where

open Base256

module parseDisplayText where
  here' = "parseDisplayText"
  open ≡-Reasoning

  parseDisplayText : Parser Dig (Logging ∘ Dec) X509.DisplayText
  runParser parseDisplayText xs = do
    no ¬ia5String ← runParser parseIA5String xs
      where yes b → return (yes (mapSuccess Dig (λ {bs} → X509.ia5String{bs}) b))
    no ¬visibleString ← runParser parseVisibleString xs
      where yes b → return (yes (mapSuccess Dig (λ {bs} → X509.visibleString{bs}) b))
    no ¬bmp ← runParser parseBMPString xs
      where yes b → return (yes (mapSuccess Dig (λ {bs} → X509.bmpString{bs}) b))
    no ¬utf8 ← runParser parseUTF8String xs
      where yes u → return (yes (mapSuccess Dig (λ {bs} → X509.utf8String{bs}) u))
    return ∘ no $ λ where
      (success prefix read read≡ (X509.ia5String x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬ia5String
      (success prefix read read≡ (X509.visibleString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬visibleString
      (success prefix read read≡ (X509.bmpString x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬bmp
      (success prefix read read≡ (X509.utf8String x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬utf8

open parseDisplayText public using (parseDisplayText)