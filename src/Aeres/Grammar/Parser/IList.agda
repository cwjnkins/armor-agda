{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.IList.Properties as IList
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Parser.Bounded
import      Aeres.Grammar.Parser.Core
import      Aeres.Grammar.Parser.Maximal
import      Aeres.Grammar.Parser.Sigma
import      Aeres.Grammar.Parser.WellFounded
import      Aeres.Grammar.Relation.Definitions
open import Aeres.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser.IList (Σ : Set) where

open Aeres.Grammar.Definitions          Σ
open Aeres.Grammar.IList                Σ
open Aeres.Grammar.Properties           Σ
open Aeres.Grammar.Parser.Bounded       Σ
open Aeres.Grammar.Parser.Core          Σ
open Aeres.Grammar.Parser.Maximal       Σ
open Aeres.Grammar.Parser.Sigma         Σ
open Aeres.Grammar.Parser.WellFounded   Σ
open Aeres.Grammar.Relation.Definitions Σ

module StrictBounday
  {M : Set → Set} ⦃ _ : Monad M ⦄ (underflow : M (Level.Lift _ ⊤))
  (A : List Σ → Set) (@0 ne : NonEmpty A) (@0 sb : StrictBounday A (IList A))
  (p : Parser (M ∘ Dec) A)
  where

  parseListWF : Parserᵢ (λ xs _ → @0 Acc _<_ (length xs) → M (Dec (Success (ExactLength (IList A) (length xs)) xs))) (const ⊤)
  runParser parseListWF [] _ =
    return (yes (success [] _ refl (mk×ₚ nil (─ refl) refl) [] refl))
  runParser parseListWF xs@(x₁ ∷ xs') (WellFounded.acc rs) = do
    yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser p xs
      where no ¬p → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (cons (mkIListCons{bs₁ = bs₁}{bs₂} head₁ tail₁ refl)) (─ len≡) refl) suffix ps≡) →
            contradiction
              (success bs₁ _ refl head₁ (bs₂ ++ suffix) {!!})
              ¬p
    case <-cmp r₁ (length xs) of λ where
      (tri> _ _ r₁<len) →
        contradiction
          (begin (r₁ ≡⟨ r₁≡ ⟩
                 length pre₁ ≤⟨ m≤m+n (length pre₁) (length suf₁) ⟩
                 length pre₁ + length suf₁ ≡⟨ (sym $ length-++ pre₁) ⟩
                 length (pre₁ ++ suf₁) ≡⟨ cong length ps≡₁ ⟩
                 length xs ∎))
          (<⇒≱ r₁<len)
      (tri≈ _ r₁≡len _) →
        return (yes
          (success xs _ refl
            (mk×ₚ (consIList v₁ nil refl)
              (─ (≡-Reasoning.begin
                   length (pre₁ ++ []) ≡-Reasoning.≡⟨ cong length (++-identityʳ pre₁) ⟩
                   length pre₁         ≡-Reasoning.≡⟨ sym r₁≡ ⟩
                   r₁                  ≡-Reasoning.≡⟨ r₁≡len ⟩
                   length xs           ≡-Reasoning.∎))
              {!!})
            [] (++-identityʳ xs)))
      (tri< r₁<len ¬r₁≡len ¬r₁>len) → do
        yes (success pre₂ r₂ r₂≡ (mk×ₚ v₂ (─ v₂Len) refl) suf₂ ps≡₂) ← runParser parseListWF suf₁ {!!}
          where no ¬p → do
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (cons (mkIListCons{bs₁}{bs₂} head₁ tail₁ refl)) (─ len≡) refl) suffix ps≡) → ‼
                let
                    @0 ps≡' : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                    ps≡' = ≡-Reasoning.begin
                             pre₁ ++ suf₁           ≡-Reasoning.≡⟨ ps≡₁ ⟩
                             xs                     ≡-Reasoning.≡⟨ sym ps≡ ⟩
                             (bs₁ ++ bs₂) ++ suffix ≡-Reasoning.≡⟨ solve (++-monoid Σ) ⟩
                             bs₁ ++ bs₂ ++ suffix   ≡-Reasoning.∎

                    @0 ps≡“ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ × [] ≡ suffix
                    ps≡“ = Lemmas.length-++-≡ (pre₁ ++ suf₁) _ _ _
                             (≡-Reasoning.begin
                               (pre₁ ++ suf₁)++ []    ≡-Reasoning.≡⟨ ++-identityʳ _ ⟩
                               pre₁ ++ suf₁           ≡-Reasoning.≡⟨ ps≡' ⟩
                               bs₁ ++ bs₂ ++ suffix   ≡-Reasoning.≡⟨ solve (++-monoid Σ) ⟩
                               (bs₁ ++ bs₂) ++ suffix ≡-Reasoning.∎)
                             (≡-Reasoning.begin
                               length (pre₁ ++ suf₁)  ≡-Reasoning.≡⟨ cong length ps≡₁ ⟩
                               length xs              ≡-Reasoning.≡⟨ sym len≡ ⟩
                               length (bs₁ ++ bs₂)    ≡-Reasoning.∎)

                    @0 bs₁≡ : pre₁ ≡ bs₁
                    bs₁≡ = sym $
                      sb xs bs₁ (bs₂ ++ suffix) pre₁ suf₁
                        (trans (sym ps≡) (solve (++-monoid Σ))) (sym ps≡₁)
                        head₁ v₁ (subst (IList A) (trans (sym $ ++-identityʳ bs₂) (cong (bs₂ ++_) (proj₂ ps≡“))) tail₁)

                    @0 bs₂≡ : suf₁ ≡ bs₂
                    bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ (proj₁ ps≡“)
                in
                contradiction
                  (success _ _ refl (mk×ₚ tail₁ (─ (cong length (sym bs₂≡))) refl) [] (trans (++-identityʳ bs₂) (sym bs₂≡)))
                  ¬p
        let suf₂≡ : Erased ([] ≡ suf₂)
            suf₂≡ = ─ (proj₂
                      (Lemmas.length-++-≡ suf₁ _ pre₂ _ (trans (++-identityʳ _) (sym ps≡₂)) (sym v₂Len)))

            xs≡ : Erased (pre₁ ++ pre₂ ≡ xs)
            xs≡ = ─ (≡-Reasoning.begin
                    pre₁ ++ pre₂           ≡-Reasoning.≡⟨ sym (++-identityʳ _) ⟩
                    (pre₁ ++ pre₂) ++ []   ≡-Reasoning.≡⟨ cong ((pre₁ ++ pre₂) ++_) (Erased.x suf₂≡) ⟩
                    (pre₁ ++ pre₂) ++ suf₂ ≡-Reasoning.≡⟨ ++-assoc pre₁ _ _ ⟩
                    pre₁ ++ pre₂ ++ suf₂   ≡-Reasoning.≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                    pre₁ ++ suf₁           ≡-Reasoning.≡⟨ ps≡₁ ⟩
                    xs                     ≡-Reasoning.∎)
        return (yes
          (success xs (r₁ + r₂)
            (≡-Reasoning.begin
              r₁ + r₂                   ≡-Reasoning.≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
              length pre₁ + length pre₂ ≡-Reasoning.≡⟨ (sym $ length-++ pre₁) ⟩
              length (pre₁ ++ pre₂)     ≡-Reasoning.≡⟨ cong length (Erased.x xs≡) ⟩
              length xs                 ≡-Reasoning.∎)
            (mk×ₚ (consIList v₁ v₂ refl)
              (─ cong length (Erased.x xs≡)) (Erased.x xs≡))
            [] (++-identityʳ xs)))
    where
    open ≤-Reasoning
    open import Tactic.MonoidSolver using (solve ; solve-macro)

  -- runParser parseListWF [] _ =
  -- runParser parseListWF xs@(x₁ ∷ xs') (WellFounded.acc rs) = do
  --   yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser p xs
  --     where no ¬p → do
  --       return ∘ no $ λ where
  --         x → {!!}
  --   {!!}
  -- runParser (parseListWF zero) xs _ =
  --   return (yes (success [] _ refl (mk×ₚ nil (─ refl) refl) xs refl))
  -- runParser (parseListWF n'@(suc n)) xs (WellFounded.acc rs) = do
  --   yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)
  --     ← runParser (parse≤ n p {!!} underflow) xs
  --     where no ¬p → do
  --       return ∘ no $ λ where
  --         (success prefix read read≡ value suffix ps≡) → {!!}
  --   case <-cmp r₁ n of λ where
  --     (tri> ¬r₁<n ¬r₁≡n r₁>n) →
  --       contradiction {!≤-trans ? !} (<⇒≱ r₁>n)
  --     (tri< a ¬b ¬c) → {!!}
  --     (tri≈ ¬a b ¬c) → {!!}

-- module parseIList
--   {M : Set → Set} ⦃ _ : Monad M ⦄
--   (underflow : M (Level.Lift _ ⊤))
--   (A : List Σ → Set) (@0 ne : NonEmpty A) (@0 nn : NonNesting A)
--   (p : Parser (M ∘ Dec) A) where

--   open ≡-Reasoning
--   open import Tactic.MonoidSolver using (solve ; solve-macro)

--   here' = "parseIList"

--   parseIListWF : ∀ n → ParserWF (M ∘ Dec) (ExactLength (IList A) n)
--   runParser (parseIListWF zero) xs _ = 
--     return (yes
--       (success [] 0 refl (mk×ₚ nil (─ refl) refl) xs refl))
--   runParser (parseIListWF n@(suc _)) xs (WellFounded.acc rs) = do
--     yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (─ r₀≤len) refl) suf₀ ps≡₀)
--       ← runParser (parse≤ n p nn underflow) xs
--       where no ¬parse → do
--         return ∘ no $ λ where
--           (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (cons (mkIListCons{bs₁}{bs₂} head₁ tail₁ refl)) (─ bsLen) refl) suffix ps≡) →
--             contradiction
--               (success bs₁ _ refl
--                 (mk×ₚ head₁
--                   (─ (m+n≤o⇒m≤o _{length bs₂} (Lemmas.≡⇒≤ (trans (sym $ length-++ bs₁) bsLen))))
--                   refl)
--                 (bs₂ ++ suffix)
--                 (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
--                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
--                         xs ∎))
--               ¬parse
--     case <-cmp r₀ n of λ where
--       (tri> _ _  r₀>n) →
--         contradiction (≤-trans (Lemmas.≡⇒≤ r₀≡) r₀≤len) (<⇒≱ r₀>n)
--       (tri≈ _ r₀≡n _)  →
--         return (yes
--           (success pre₀ _ r₀≡
--             (mk×ₚ (cons (mkIListCons{bs₁ = pre₀} v₀ nil refl))
--                (─ trans (trans (cong length (++-identityʳ pre₀)) (sym r₀≡)) r₀≡n) (++-identityʳ _))
--                suf₀ ps≡₀))
--       (tri< r₀<n _ _)  → do
--         let @0 suf₀<xs : length suf₀ < length xs
--             suf₀<xs = subst (λ i → length suf₀ < length i) ps≡₀ (Lemmas.length-++-< pre₀ suf₀ (ne v₀))
--         yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ (─ r₁≡len-pre₁) refl) suf₁ ps≡₁)
--           ← runParser (parseIListWF (n ∸ r₀)) suf₀ (rs _ suf₀<xs)
--           where no ¬parse → do
--             return ∘ no $ λ where
--               (success prefix read read≡ (mk×ₚ nil (─ ()) refl) suffix ps≡)
--               (success .(bs₁ ++ bs₂) read read≡ (mk×ₚ (cons (mkIListCons{bs₁}{bs₂} h t refl)) (─ bsLen) refl) suffix ps≡) → ‼
--                 let @0 xs≡ : pre₀ ++ suf₀ ≡ bs₁ ++ bs₂ ++ suffix
--                     xs≡ = begin pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
--                                  xs                     ≡⟨ sym ps≡ ⟩
--                                  (bs₁ ++ bs₂) ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
--                                  bs₁ ++ bs₂ ++ suffix   ∎

--                     @0 pre₀≡bs₁ : pre₀ ≡ bs₁
--                     pre₀≡bs₁ = nn xs≡ v₀ h
--                 in
--                 contradiction
--                   (success bs₂ _ refl
--                     (mk×ₚ t
--                       (─ +-cancelˡ-≡ r₀
--                          (begin (r₀ + length bs₂         ≡⟨ cong (_+ length bs₂) r₀≡ ⟩
--                                 length pre₀ + length bs₂ ≡⟨ cong (λ x → length x + length bs₂) pre₀≡bs₁ ⟩
--                                 length bs₁ + length bs₂  ≡⟨ sym (length-++ bs₁) ⟩
--                                 length (bs₁ ++ bs₂)      ≡⟨ bsLen ⟩
--                                 n                        ≡⟨ sym (+-identityʳ _) ⟩
--                                 n + 0                    ≡⟨ cong (n +_) (sym (n∸n≡0 r₀)) ⟩
--                                 n + (r₀ - r₀)            ≡⟨ sym (+-∸-assoc n {r₀} ≤-refl) ⟩
--                                 (n + r₀) - r₀            ≡⟨ cong (_∸ r₀) (+-comm n _) ⟩
--                                 (r₀ + n) - r₀            ≡⟨ +-∸-assoc r₀ {n} (<⇒≤ r₀<n) ⟩
--                                 r₀ + (n - r₀)            ∎)))
--                       refl) suffix
--                     (++-cancelˡ bs₁ (trans (sym xs≡) (cong (_++ suf₀) pre₀≡bs₁))))
--                   ¬parse
--         return (yes
--           (success (pre₀ ++ pre₁) (r₀ + r₁)
--             (begin (r₀ + r₁                   ≡⟨ cong (_+ r₁) r₀≡ ⟩
--                     length pre₀ + r₁          ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
--                     length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
--                     length (pre₀ ++ pre₁)     ∎))
--             (mk×ₚ (cons (mkIListCons v₀ v₁ refl))
--               (─(begin (length (pre₀ ++ pre₁)     ≡⟨ length-++ pre₀ ⟩
--                          length pre₀ + length pre₁ ≡⟨ cong (_+ _) (sym r₀≡) ⟩
--                          r₀ + length pre₁          ≡⟨ cong (r₀ +_) r₁≡len-pre₁ ⟩
--                          r₀ + (n - r₀)             ≡⟨ sym (+-∸-assoc r₀ (<⇒≤ r₀<n)) ⟩
--                          r₀ + n - r₀               ≡⟨ cong (_∸ r₀) (+-comm r₀ n) ⟩
--                          n + r₀ - r₀               ≡⟨ +-∸-assoc n {n = r₀} ≤-refl ⟩
--                          n + (r₀ - r₀)             ≡⟨ cong (n +_) (n∸n≡0 r₀) ⟩
--                          n + 0                     ≡⟨ +-identityʳ n ⟩
--                          n                         ∎)))
--               refl)
--             suf₁
--             (begin ((pre₀ ++ pre₁) ++ suf₁  ≡⟨ solve (++-monoid Σ) ⟩
--                     pre₀ ++ pre₁ ++ suf₁    ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
--                     pre₀ ++ suf₀            ≡⟨ ps≡₀ ⟩
--                     xs                      ∎))))

--   parseIList : ∀ n → Parser (M ∘ Dec) (ExactLength (IList A) n)
--   parseIList n = parseWF (parseIListWF n)

--   parseIListNonEmpty : ∀ n → Parser (M ∘ Dec) (ExactLength (IListNonEmpty A) n)
--   parseIListNonEmpty n =
--     parseEquivalent{A = Σₚ (ExactLength (IList A) n) (λ _ xs → lengthIList (fstₚ xs) ≥ 1)}
--       (symEquivalent (proj₁ Distribute.×ₚ-Σₚ-iso))
--       (parseSigma' exactLength-nonnesting (λ _ → _ ≥? 1)
--         (λ where
--            (mk×ₚ l₁ sndₚ₁ refl) (mk×ₚ l₂ sndₚ₂ refl) ≥1 →
--              subst₀ (_≥ 1) (IList.lengthIList≡ _ ne nn l₁ l₂) ≥1)
--         (parseIList n))

-- open parseIList public using (parseIList ; parseIListNonEmpty)
