{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)


module Aeres.Data.X509.Decidable.Octetstring where

open Base256

module parseOctetstringValue where
  here' = "parseOctetStringValue"

  open ≡-Reasoning

  parseOctetstringValue : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.OctetstringValue n)
  parseOctetstringValue = λ n → parseN Dig n (tell $ here' String.++ ": underflow")

open parseOctetstringValue public using (parseOctetstringValue)

module parseOctetstring where
  here' = "parseOctetString"

  open ≡-Reasoning

  parseOctetstring : Parser Dig (Logging ∘ Dec) Generic.Octetstring
  parseOctetstring = parseTLV Tag.Octetstring  "Octet string" Generic.OctetstringValue parseOctetstringValue 

open parseOctetstring public using (parseOctetstring)

parseTeletexString : Parser Dig (Logging ∘ Dec) X509.TeletexString
parseTeletexString =
  parseTLV Tag.TeletexString "teletex string" Generic.OctetstringValue parseOctetstringValue

parsePrintableString : Parser Dig (Logging ∘ Dec) X509.PrintableString
parsePrintableString =
  parseTLV Tag.PrintableString "printable string" Generic.OctetstringValue  parseOctetstringValue

parseUniversalString : Parser Dig (Logging ∘ Dec) X509.UniversalString
parseUniversalString =
  parseTLV Tag.UniversalString "universal string" Generic.OctetstringValue  parseOctetstringValue

parseUTF8String : Parser Dig (Logging ∘ Dec) X509.UTF8String
parseUTF8String =
  parseTLV Tag.UTF8String "UTF8 string" Generic.OctetstringValue parseOctetstringValue

parseBMPString : Parser Dig (Logging ∘ Dec) X509.BMPString
parseBMPString =
  parseTLV Tag.BMPString "BMP string" Generic.OctetstringValue parseOctetstringValue

parseVisibleString : Parser Dig (Logging ∘ Dec) X509.VisibleString
parseVisibleString =
  parseTLV Tag.VisibleString "universal string" Generic.OctetstringValue parseOctetstringValue

module parseIA5StringValue where

  here' = "parseIA5StringValue"

  parseIA5StringValue : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig X509.IA5StringValue n)
  runParser (parseIA5StringValue n) xs = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton os₀ refl) osLen refl) suf₀ ps≡₀) ← runParser (parseOctetstringValue n) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (X509.mkIA5StringValue str all<128) strLen refl) suffix ps≡) →
            contradiction
              (success prefix _ read≡
                (mk×ₚ str strLen refl) _ ps≡)
              ¬parse
    case All.all? (Fin._<? (# 128)) os₀ of λ where
      (no  all≮128) → do
        tell $ here' String.++ ": value violation"
        return ∘ no $ λ where
          (success .str' _ read≡ (mk×ₚ (X509.mkIA5StringValue (singleton str' refl) all<128) strLen refl) suffix ps≡) → ‼
            let @0 pre₀≡ : pre₀ ≡ str'
                pre₀≡ = proj₁ $
                  Lemmas.length-++-≡ _ suf₀ _ suffix
                    (trans ps≡₀ (sym ps≡))
                    (trans osLen (sym strLen))
            in
            contradiction (subst (All _) (sym pre₀≡) all<128) all≮128
      (yes all<128) →
        return (yes
          (success pre₀ _ r₀≡
            (mk×ₚ (X509.mkIA5StringValue (singleton os₀ refl) all<128) osLen refl)
            suf₀ ps≡₀))

open parseIA5StringValue public using (parseIA5StringValue)

parseIA5String : Parser Dig (Logging ∘ Dec) X509.IA5String
parseIA5String = parseTLV _ "IA5String" _ parseIA5StringValue

Oct₁ : List Dig
Oct₁ = Tag.Octetstring ∷ # 2 ∷ # 1 ∷ [ # 1 ]

I5₂ : List Dig
I5₂ = Tag.IA5String ∷ # 2 ∷ # 1 ∷ [ # 1 ]

I5₃ : List Dig
I5₃ = Tag.IA5String ∷ # 2 ∷ # 1 ∷ [ # 160 ]

test₁ : Generic.Octetstring Oct₁
test₁ = Success.value (toWitness {Q = Logging.val (runParser parseOctetstring Oct₁)} tt)

test₂ :  X509.IA5String I5₂
test₂ = Success.value (toWitness {Q = Logging.val (runParser parseIA5String I5₂)} tt)

test₃ : ¬ Success _ X509.IA5String I5₃
test₃ = toWitnessFalse {Q = Logging.val (runParser parseIA5String I5₃)} tt
