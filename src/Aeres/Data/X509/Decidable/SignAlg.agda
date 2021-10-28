{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Null
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Aeres.Grammar.Sum
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)


module Aeres.Data.X509.Decidable.SignAlg where

open Base256

module parseSignAlg where

  open ≡-Reasoning

  here' = "parseSignAlg"

  parseSignAlgFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.SignAlgFields n)
  runParser (parseSignAlgFields n) xs = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ v₀Len refl) suf₀ ps≡₀) ←
      runParser (parse≤ _ n parseOID Props.TLV.nonnesting (tell $ here' String.++ ": underflow" )) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success ._ read read≡ (mk×ₚ (X509.mkSignAlgFields{o = o}{p} signOID param refl) sndₚ₁ refl) suffix ps≡) →
            contradiction
              (success o _ refl (mk×ₚ signOID (≤-trans (Lemmas.length-++-≤₁ o p) (Lemmas.≡⇒≤ sndₚ₁)) refl) (p ++ suffix)
                (trans (o ++ p ++ suffix ≡ (o ++ p) ++ suffix ∋ solve (++-monoid Dig)) ps≡))
              ¬parse
    case <-cmp r₀ n of λ where
      (tri> r≮n r≢n n<r) → contradiction (≤-trans (Lemmas.≡⇒≤ r₀≡) v₀Len) (<⇒≱ n<r)
      (tri≈ _ r≡n _) →
        return (yes
          (success pre₀ _ r₀≡
            (mk×ₚ (X509.mkSignAlgFields v₀ none (pre₀ ≡ pre₀ ++ [] ∋ solve (++-monoid Dig))) (trans₀ (sym r₀≡) r≡n) refl)
            suf₀ ps≡₀))
      (tri< r<n _ _) → do
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ v₁Len refl) suf₁ ps≡₁) ← runParser (parseOctetstringValue (n - r₀)) suf₀
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix@._ read read≡ (mk×ₚ (X509.mkSignAlgFields{o = o}{p} signOID none refl) signAlgLen refl) suffix ps≡) →
                contradiction
                  (begin (r₀ ≡⟨ r₀≡ ⟩
                         length pre₀ ≡⟨ cong length (TLV.nonnesting (trans₀ ps≡₀ (trans₀ (sym ps≡) ((o ++ []) ++ suffix ≡ o ++ [] ++ suffix ∋ solve (++-monoid Dig)))) v₀ signOID) ⟩
                         length o ≡⟨ cong length (o ≡ o ++ [] ∋ solve (++-monoid Dig)) ⟩
                         length prefix ≡⟨ signAlgLen ⟩
                         n ∎))
                  (<⇒≢ r<n)
              (success prefix@._ read read≡ (mk×ₚ (X509.mkSignAlgFields{o = o}{p} signOID (some param) refl) signAlgLen refl) suffix ps≡) → ‼
                let @0 ps≡' : o ++ p ++ suffix ≡ pre₀ ++ suf₀
                    ps≡' = trans₀ (o ++ p ++ suffix ≡ (o ++ p) ++ suffix ∋ solve (++-monoid Dig)) (trans₀ ps≡ (sym ps≡₀))

                    @0 pre₀≡ : pre₀ ≡ o
                    pre₀≡ = (sym $ TLV.nonnesting ps≡' signOID v₀)
                in
                contradiction
                  (success _ _ refl
                    (mk×ₚ param
                      (begin (length p ≡⟨ (sym $ m+n∸n≡m (length p) (length o)) ⟩
                             (length p + length o) - length o ≡⟨ cong (_- length o) (+-comm (length p) (length o)) ⟩
                             length o + length p - length o ≡⟨ cong (_- length o) (sym (length-++ o)) ⟩
                             length (o ++ p) - length o ≡⟨ cong (_- length o) signAlgLen ⟩
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
              (X509.mkSignAlgFields v₀ (some v₁) refl)
              (‼ (begin length (pre₀ ++ pre₁) ≡⟨ length-++ pre₀ ⟩
                        length pre₀ + length pre₁ ≡⟨ cong (_+ length pre₁) (sym r₀≡) ⟩
                        r₀ + length pre₁ ≡⟨ cong (r₀ +_) v₁Len ⟩
                        r₀ + (n - r₀) ≡⟨ Lemmas.m+n-m≡n (<⇒≤ r<n) ⟩
                        n ∎))
              refl)
            suf₁
            (begin (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
                   pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                   pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
                   xs ∎)))

  parseSignAlg : Parser Dig (Logging ∘ Dec) X509.SignAlg
  parseSignAlg =
    parseTLV _ "signature algorithm" _ parseSignAlgFields

open parseSignAlg public using (parseSignAlg)

private
  module Test where

    Sa₁ : List Dig
    Sa₁ = Tag.Sequence ∷ # 13 ∷ # Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ [ # 0 ]

    Sa₂ : List Dig
    Sa₂ = Tag.Sequence ∷ # 11 ∷ # Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ]

    Sa₃ : List Dig
    Sa₃ = Tag.Sequence ∷ # 13 ∷ # Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 11 ∷ # 5 ∷ [ # 0 ]

    test₁ : X509.SignAlg Sa₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₁)} tt)

    test₂ : X509.SignAlg Sa₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₂)} tt)

    test₃ : X509.SignAlg Sa₃
    test₃ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₃)} tt)

