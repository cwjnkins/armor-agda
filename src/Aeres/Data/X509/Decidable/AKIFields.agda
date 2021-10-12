{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.AKIFields where

open Base256

module parseAKIFields where
  module Here where
    AKIKeyId = "AKI key id"
    AKIAuthCertIssuer = "AKI auth. cert. issuer"
    AKIAuthCertSN = "AKI auth. cert. SN"

  open ≡-Reasoning

  parseAKIKeyId : Parser Dig (Logging ∘ Dec) X509.AKIKeyId
  parseAKIKeyId = parseTLV _ Here.AKIKeyId _ parseOctetstringValue

  parseAKIAuthCertIssuer : Parser Dig (Logging ∘ Dec) X509.AKIAuthCertIssuer
  parseAKIAuthCertIssuer = parseTLV _ Here.AKIAuthCertIssuer _ parseGeneralNamesElems

  parseAKIAuthCertSN : Parser Dig (Logging ∘ Dec) X509.AKIAuthCertSN
  parseAKIAuthCertSN = parseTLV _ Here.AKIAuthCertSN _ parseIntValue

  parseAKIFieldsSeqFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.AKIFieldsSeqFields n)
  runParser (parseAKIFieldsSeqFields n) xs = do
    x₁ ← runParser parseAKIKeyId xs
    x₂ ← runParser parseAKIAuthCertIssuer (suffixDecSuccess _ x₁)
    x₃ ← runParser parseAKIAuthCertSN (suffixDecSuccess _ x₂)
    {!!}
    where
    check : (x₁ : Dec (Success _ X509.AKIKeyId xs))
            (x₂ : Dec (Success _ X509.AKIAuthCertIssuer (suffixDecSuccess Dig x₁)))
            (x₃ : Dec (Success _ X509.AKIAuthCertSN (suffixDecSuccess Dig x₂)))
            → Dec (Success _ (ExactLength _ X509.AKIFieldsSeqFields n) xs)
    check x₁ x₂ x₃
      with readDecSuccess _ x₁ + readDecSuccess _ x₂ + readDecSuccess _ x₃ in eq
    ... | r
      with x₁ | x₂ | x₃ | n ≟ r
    ... | no  ¬1 | no  ¬2 | no  ¬3 | no  ¬4 =
      no λ where
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none none none refl) refl refl) suffix ps≡) →
          contradiction eq ¬4
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none none (some x) refl) sndₚ₁ bs≡) suffix ps≡) → {!!}
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none (some x) none refl) sndₚ₁ bs≡) suffix ps≡) → {!!}
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none (some x) (some x₁) refl) sndₚ₁ bs≡) suffix ps≡) → {!!}
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some x) none none refl) sndₚ₁ bs≡) suffix ps≡) → {!!}
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some x) none (some x₁) refl) sndₚ₁ bs≡) suffix ps≡) → {!!}
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some x) (some x₁) none refl) sndₚ₁ bs≡) suffix ps≡) → {!!}
        (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some x) (some x₁) (some x₂) refl) sndₚ₁ bs≡) suffix ps≡) → {!!}
    ... | no  ¬1 | no  ¬2 | no  ¬3 | yes ✓4 =
      yes (success [] _ refl (mk×ₚ (X509.mkAKIFieldsSeqFields none none none refl) (trans eq (sym ✓4)) refl) xs refl)
    ... | no  ¬1 | no  ¬2 | yes ✓3 | no  ¬4 = {!!}
    ... | no  ¬1 | no  ¬2 | yes ✓3 | yes ✓4 = {!!}
    ... | no  ¬1 | yes ✓2 | no  ¬3 | no  ¬4 = {!!}
    ... | no  ¬1 | yes ✓2 | no  ¬3 | yes ✓4 = {!!}
    ... | no  ¬1 | yes ✓2 | yes ✓3 | no  ¬4 = {!!}
    ... | no  ¬1 | yes ✓2 | yes ✓3 | yes ✓4 = {!!}
    ... | yes ✓1 | no  ¬2 | no  ¬3 | no  ¬4 = {!!}
    ... | yes ✓1 | no  ¬2 | no  ¬3 | yes ✓4 = {!!}
    ... | yes ✓1 | no  ¬2 | yes ✓3 | no  ¬4 = {!!}
    ... | yes ✓1 | no  ¬2 | yes ✓3 | yes ✓4 = {!!}
    ... | yes ✓1 | yes ✓2 | no  ¬3 | no  ¬4 = {!!}
    ... | yes ✓1 | yes ✓2 | no  ¬3 | yes ✓4 = {!!}
    ... | yes ✓1 | yes ✓2 | yes ✓3 | no  ¬4 = {!!}
    ... | yes ✓1 | yes ✓2 | yes ✓3 | yes ✓4 = {!!}


--   parseAKIFields = parseTLV Tag.Integer "Int" Generic.IntegerValue p
--     where
--     p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.IntegerValue n)
--     runParser (p n) xs = do
--       yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton v₀ refl) v₀Len refl) suf₀ ps≡₀)
--         ← runParser (parseN Dig n (tell $ here' String.++ ": underflow reading it")) xs
--         where no ¬parse → do
--           return ∘ no $ λ where
--             (success prefix read read≡ (mk×ₚ (Generic.mkIntegerValue val bs≡₁) sndₚ refl) suffix ps≡) →
--               contradiction
--                 (success prefix _ read≡
--                   (mk×ₚ (singleton prefix refl) sndₚ refl)
--                   suffix ps≡)
--                 ¬parse
--       return (yes
--         (success pre₀ _ r₀≡
--           (mk×ₚ (Generic.mkIntegerValue (twosComplement v₀) refl) v₀Len refl)
--           suf₀ ps≡₀))

-- open parseAKIFields public using (parseAKIFields)
