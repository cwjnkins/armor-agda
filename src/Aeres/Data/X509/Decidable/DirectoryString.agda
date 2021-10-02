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

  parseTeletexString : Parser Dig (Logging ∘ Dec) X509.TeletexString
  parseTeletexString =
    parseTLV Tag.TeletexString "teletex string" Generic.OctetstringValue Aeres.Data.X509.Decidable.Octetstring.parseOctetstringValue

  parsePrintableString : Parser Dig (Logging ∘ Dec) X509.PrintableString
  parsePrintableString =
    parseTLV Tag.PrintableString "printable string" Generic.OctetstringValue  Aeres.Data.X509.Decidable.Octetstring.parseOctetstringValue

  parseUniversalString : Parser Dig (Logging ∘ Dec) X509.UniversalString
  parseUniversalString =
    parseTLV Tag.UniversalString "universal string" Generic.OctetstringValue  Aeres.Data.X509.Decidable.Octetstring.parseOctetstringValue

  parseUTF8String : Parser Dig (Logging ∘ Dec) X509.UTF8String
  parseUTF8String =
    parseTLV Tag.UTF8String "UTF8 string" Generic.OctetstringValue Aeres.Data.X509.Decidable.Octetstring.parseOctetstringValue

  parseBMPString : Parser Dig (Logging ∘ Dec) X509.BMPString
  parseBMPString =
    parseTLV Tag.BMPString "BMP string" Generic.OctetstringValue Aeres.Data.X509.Decidable.Octetstring.parseOctetstringValue

  postulate
    parseIA5String : Parser Dig (Logging ∘ Dec) X509.IA5String

  parseVisibleString : Parser Dig (Logging ∘ Dec) X509.VisibleString
  parseVisibleString =
    parseTLV Tag.VisibleString "universal string" Generic.OctetstringValue  Aeres.Data.X509.Decidable.Octetstring.parseOctetstringValue

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
