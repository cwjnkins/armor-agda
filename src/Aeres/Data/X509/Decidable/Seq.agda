{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.Seq where

open Base256

module parseSeq
  (eName : String) (A : List Dig → Set) (ne : NonEmpty Dig A) (nn : NonNesting Dig A)
  (p : Parser Dig (Logging ∘ Dec) A) where

  here' = "parseSeq"

  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  parseSeqElemsWF : ∀ n → ParserWF Dig (Logging ∘ Dec) (ExactLength Dig (Generic.SeqElems A) n)
  runParser (parseSeqElemsWF n) xs (WellFounded.acc rs) = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ r₀≤len refl) suf₀ ps≡₀)
      ← runParser (parse≤ _ n p nn (tell $ here' String.++ ": overflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (v Generic.∷[]) bsLen refl) suffix ps≡) →
            contradiction
              (success prefix _ read≡
                (mk×ₚ v (Lemmas.≡⇒≤ bsLen) refl)
                suffix ps≡)
              ¬parse
          (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (Generic.cons (Generic.mkSeqElems{bs₁}{bs₂} h t refl)) bsLen refl) suffix ps≡) →
            contradiction
              (success bs₁ _ refl
                (mk×ₚ h
                  (m+n≤o⇒m≤o _ {length bs₂} (Lemmas.≡⇒≤ (trans (sym $ length-++ bs₁) bsLen)))
                  refl)
                (bs₂ ++ suffix)
                (begin (bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs ∎)))
              ¬parse
    case <-cmp r₀ n of λ where
      (tri> _ _ r₀>n) →
        contradiction (≤-trans (Lemmas.≡⇒≤ r₀≡) r₀≤len) (<⇒≱ r₀>n)
      (tri≈ _ r₀≡n _) →
        return (yes
          (success pre₀ _ r₀≡
            (mk×ₚ (v₀ Generic.∷[]) (trans₀ (sym r₀≡) r₀≡n) refl) suf₀ ps≡₀))
      (tri< r₀<n _ _) → do
        let @0 suf₀<xs : length suf₀ < length xs
            suf₀<xs = subst (λ i → length suf₀ < length i) ps≡₀ (Lemmas.length-++-< pre₀ suf₀ (ne v₀))
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ r₁≡len-pre₁ refl) suf₁ ps≡₁)
          ← runParser (parseSeqElemsWF (n ∸ r₀)) suf₀ (rs _ suf₀<xs)
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (v Generic.∷[]) bsLen refl) suffix ps≡) →
                contradiction
                  (begin (r₀            ≡⟨ r₀≡ ⟩
                          length pre₀   ≡⟨ cong length (nn (trans ps≡₀ (sym ps≡)) v₀ v) ⟩
                          length prefix ≡⟨ bsLen ⟩
                          n             ∎))
                  (<⇒≢ r₀<n)
              (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (Generic.cons (Generic.mkSeqElems{bs₁}{bs₂} h t refl)) bsLen refl) suffix ps≡) → ‼
                let @0 xs≡ : pre₀ ++ suf₀ ≡ bs₁ ++ bs₂ ++ suffix
                    xs≡ = begin pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
                                 xs                     ≡⟨ sym ps≡ ⟩
                                 (bs₁ ++ bs₂) ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                                 bs₁ ++ bs₂ ++ suffix   ∎

                    @0 pre₀≡bs₁ : pre₀ ≡ bs₁
                    pre₀≡bs₁ = nn xs≡ v₀ h
                in
                contradiction
                  (success bs₂ _ refl
                    (mk×ₚ t
                      (+-cancelˡ-≡ r₀
                         (begin (r₀ + length bs₂         ≡⟨ cong (_+ length bs₂) r₀≡ ⟩
                                length pre₀ + length bs₂ ≡⟨ cong (λ x → length x + length bs₂) pre₀≡bs₁ ⟩
                                length bs₁ + length bs₂  ≡⟨ sym (length-++ bs₁) ⟩
                                length (bs₁ ++ bs₂)      ≡⟨ bsLen ⟩
                                n                        ≡⟨ sym (+-identityʳ _) ⟩
                                n + 0                    ≡⟨ cong (n +_) (sym (n∸n≡0 r₀)) ⟩
                                n + (r₀ - r₀)            ≡⟨ sym (+-∸-assoc n {r₀} ≤-refl) ⟩
                                (n + r₀) - r₀            ≡⟨ cong (_∸ r₀) (+-comm n _) ⟩
                                (r₀ + n) - r₀            ≡⟨ +-∸-assoc r₀ {n} (<⇒≤ r₀<n) ⟩
                                r₀ + (n - r₀)            ∎)))
                      refl) suffix
                    (++-cancelˡ bs₁ (trans (sym xs≡) (cong (_++ suf₀) pre₀≡bs₁))))
                  ¬parse
        return (yes
          (success (pre₀ ++ pre₁) (r₀ + r₁)
            (begin (r₀ + r₁                   ≡⟨ cong (_+ r₁) r₀≡ ⟩
                    length pre₀ + r₁          ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
                    length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
                    length (pre₀ ++ pre₁)     ∎))
            (mk×ₚ (Generic.cons (Generic.mkSeqElems v₀ v₁ refl))
              (‼ (begin (length (pre₀ ++ pre₁)     ≡⟨ length-++ pre₀ ⟩
                         length pre₀ + length pre₁ ≡⟨ cong (_+ _) (sym r₀≡) ⟩
                         r₀ + length pre₁          ≡⟨ cong (r₀ +_) r₁≡len-pre₁ ⟩
                         r₀ + (n - r₀)             ≡⟨ sym (+-∸-assoc r₀ (<⇒≤ r₀<n)) ⟩
                         r₀ + n - r₀               ≡⟨ cong (_∸ r₀) (+-comm r₀ n) ⟩
                         n + r₀ - r₀               ≡⟨ +-∸-assoc n {n = r₀} ≤-refl ⟩
                         n + (r₀ - r₀)             ≡⟨ cong (n +_) (n∸n≡0 r₀) ⟩
                         n + 0                     ≡⟨ +-identityʳ n ⟩
                         n                         ∎)))
              refl)
            suf₁
            (begin ((pre₀ ++ pre₁) ++ suf₁  ≡⟨ solve (++-monoid Dig) ⟩
                    pre₀ ++ pre₁ ++ suf₁    ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                    pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
                    xs                      ∎))))

  parseSeqElems : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig (Generic.SeqElems A) n)
  parseSeqElems n = parseWF Dig (parseSeqElemsWF n)

  parseSeq : Parser Dig (Logging ∘ Dec) (Generic.Seq A)
  parseSeq = parseTLV Tag.Sequence "seq" (Generic.SeqElems A) parseSeqElems

open parseSeq public using (parseSeqElems ; parseSeq)

parseIntegerSeq : Parser Dig (Logging ∘ Dec) Generic.IntegerSeq
parseIntegerSeq = parseSeq "int" Generic.Int NonEmpty.Int NonNesting.Int parseInt
