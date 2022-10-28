{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.Properties
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.SignAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

module parseSignAlg where

  open ≡-Reasoning

  here' = "parseSignAlg"

  parseSignAlgFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength SignAlgFields n)
  runParser (parseSignAlgFields n) xs = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (─ v₀Len) refl) suf₀ ps≡₀) ←
      runParser (parse≤ n parseOID TLV.nonnesting (tell $ here' String.++ ": underflow" )) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success ._ read read≡ (mk×ₚ (mkSignAlgFields{o = o}{p} signOID param refl) sndₚ₁ refl) suffix ps≡) →
            contradiction
              (success o _ refl (mk×ₚ signOID (─ ≤-trans (Lemmas.length-++-≤₁ o p) (Lemmas.≡⇒≤ $ ̂‼ sndₚ₁)) refl) (p ++ suffix)
                (trans (o ++ p ++ suffix ≡ (o ++ p) ++ suffix ∋ solve (++-monoid UInt8)) ps≡))
              ¬parse
    case <-cmp r₀ n of λ where
      (tri> r≮n r≢n n<r) → contradiction (≤-trans (Lemmas.≡⇒≤ r₀≡) v₀Len) (<⇒≱ n<r)
      (tri≈ _ r≡n _) →
        return (yes
          (success pre₀ _ r₀≡
            (mk×ₚ (mkSignAlgFields v₀ none (pre₀ ≡ pre₀ ++ [] ∋ solve (++-monoid UInt8))) (─ trans₀ (sym r₀≡) r≡n) refl)
            suf₀ ps≡₀))
      (tri< r<n _ _) → do
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ (─ v₁Len) refl) suf₁ ps≡₁) ← runParser (parseOctetStringValue (n - r₀)) suf₀
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix@._ read read≡ (mk×ₚ (mkSignAlgFields{o = o}{p} signOID none refl) signAlgLen refl) suffix ps≡) →
                contradiction
                  (begin (r₀ ≡⟨ r₀≡ ⟩
                         length pre₀ ≡⟨ cong length (TLV.nonnesting (trans₀ ps≡₀ (trans₀ (sym ps≡) ((o ++ []) ++ suffix ≡ o ++ [] ++ suffix ∋ solve (++-monoid UInt8)))) v₀ signOID) ⟩
                         length o ≡⟨ cong length (o ≡ o ++ [] ∋ solve (++-monoid UInt8)) ⟩
                         length prefix ≡⟨ ̂‼ signAlgLen ⟩
                         n ∎))
                  (<⇒≢ r<n)
              (success prefix@._ read read≡ (mk×ₚ (mkSignAlgFields{o = o}{p} signOID (some (mk×ₚ param _ refl)) refl) signAlgLen refl) suffix ps≡) → ‼
                let @0 ps≡' : o ++ p ++ suffix ≡ pre₀ ++ suf₀
                    ps≡' = trans₀ (o ++ p ++ suffix ≡ (o ++ p) ++ suffix ∋ solve (++-monoid UInt8)) (trans₀ ps≡ (sym ps≡₀))

                    @0 pre₀≡ : pre₀ ≡ o
                    pre₀≡ = (sym $ TLV.nonnesting ps≡' signOID v₀)
                in
                contradiction
                  (success _ _ refl
                    (mk×ₚ param
                      (─ (begin
                             length p ≡⟨ (sym $ m+n∸n≡m (length p) (length o)) ⟩
                             (length p + length o) - length o ≡⟨ cong (_- length o) (+-comm (length p) (length o)) ⟩
                             length o + length p - length o ≡⟨ cong (_- length o) (sym (length-++ o)) ⟩
                             length (o ++ p) - length o ≡⟨ cong (_- length o) $ ̂‼ signAlgLen ⟩
                             n - length o ≡⟨ cong ((n -_) ∘ length) (sym pre₀≡) ⟩
                             n - length pre₀ ≡⟨ cong (n -_) (sym r₀≡) ⟩
                             n - r₀ ∎))
                      refl)
                    suffix
                    (Lemmas.++-cancel≡ˡ o _ (sym pre₀≡) ps≡'))
                 ¬parse
        return (yes
          (success (pre₀ ++ pre₁) (r₀ + r₁)
            (begin (r₀ + r₁ ≡⟨ cong₂ _+_ r₀≡ r₁≡ ⟩
                   length pre₀ + length pre₁ ≡⟨ sym (length-++ pre₀) ⟩
                   length (pre₀ ++ pre₁) ∎))
            (mk×ₚ
              (mkSignAlgFields
                v₀
                (some
                  (mk×ₚ v₁
                    (─ subst₀ (0 <_) (sym v₁Len) (m<n⇒0<n∸m r<n))
                    refl))
                refl)
              (─ (begin length (pre₀ ++ pre₁) ≡⟨ length-++ pre₀ ⟩
                        length pre₀ + length pre₁ ≡⟨ cong (_+ length pre₁) (sym r₀≡) ⟩
                        r₀ + length pre₁ ≡⟨ cong (r₀ +_) $ ̂‼ (─ v₁Len) ⟩
                        r₀ + (n - r₀) ≡⟨ Lemmas.m+n-m≡n (<⇒≤ r<n) ⟩
                        n ∎))
              refl)
            suf₁
            (begin (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid UInt8) ⟩
                   pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                   pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
                   xs ∎)))

  parseSignAlg : Parser (Logging ∘ Dec) SignAlg
  parseSignAlg =
    parseTLV _ "signature algorithm" _ parseSignAlgFields

open parseSignAlg public using (parseSignAlg)

-- private
--   module Test where

--     Sa₁ : List UInt8
--     Sa₁ = Tag.Sequence ∷ # 13 ∷ # Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ [ # 0 ]

--     Sa₂ : List UInt8
--     Sa₂ = Tag.Sequence ∷ # 11 ∷ # Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ]

--     Sa₃ : List UInt8
--     Sa₃ = Tag.Sequence ∷ # 13 ∷ # Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 11 ∷ # 5 ∷ [ # 0 ]

--     --- this is a test case for non-RSA signature algorithm (ex: ECDSA)
--     Sa₄ : List UInt8
--     Sa₄ = Tag.Sequence ∷ # 19 ∷ # 6 ∷ # 7 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 2 ∷ # 1 ∷ # 6 ∷ # 8 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 3 ∷ # 1 ∷ [ # 7 ]

--     test₁ : X509.SignAlg Sa₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₁)} tt)

--     test₂ : X509.SignAlg Sa₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₂)} tt)

--     test₃ : X509.SignAlg Sa₃
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₃)} tt)

--     test₄ : X509.SignAlg Sa₄
--     test₄ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₄)} tt)