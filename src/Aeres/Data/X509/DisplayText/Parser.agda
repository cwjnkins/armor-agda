{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DisplayText.TCB
open import Aeres.Data.X509.IA5String
open import Aeres.Data.X509.Strings
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.DisplayText.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X509: DisplayText"

parseDisplayText : Parser (Logging ∘ Dec) DisplayText
runParser parseDisplayText xs = do
  no ¬ia5String ← runParser (parseTLVLenBound 1 200 parseIA5String) xs
    where yes b → return (yes (mapSuccess (λ {bs} → ia5String{bs}) b))
  no ¬visibleString ← runParser (parseTLVLenBound 1 200 parseVisibleString) xs
    where yes b → return (yes (mapSuccess (λ {bs} → visibleString{bs}) b))
  no ¬bmp ← runParser (parseTLVLenBound 1 200 parseBMPString) xs
    where yes b → return (yes (mapSuccess (λ {bs} → bmpString{bs}) b))
  no ¬utf8 ← runParser (parseTLVLenBound 1 200 parseUTF8String) xs
    where yes u → return (yes (mapSuccess (λ {bs} → utf8String{bs}) u))
  return ∘ no $ λ where
    (success prefix read read≡ (ia5String x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬ia5String
    (success prefix read read≡ (visibleString x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬visibleString
    (success prefix read read≡ (bmpString x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬bmp
    (success prefix read read≡ (utf8String x) suffix ps≡) →
      contradiction (success _ _ read≡ x _ ps≡) ¬utf8
