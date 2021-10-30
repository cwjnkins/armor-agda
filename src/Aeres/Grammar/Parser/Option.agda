{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Parser.Option (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open import Aeres.Grammar.Parser.Core Σ
open import Aeres.Grammar.Parser.Bounded Σ

@0 prefixDecSuccess : ∀ {A xs} → Dec (Success A xs) → List Σ
prefixDecSuccess (no _) = []
prefixDecSuccess (yes (success prefix _ _ _ _ _ )) = prefix

readDecSuccess : ∀ {A xs} → Dec (Success A xs) → ℕ
readDecSuccess (yes s) = Success.read s
readDecSuccess (no  _) = 0

@0 read≡DecSuccess : ∀ {A xs} → (x : Dec (Success A xs)) → readDecSuccess x ≡ length (prefixDecSuccess x)
read≡DecSuccess (no _) = refl
read≡DecSuccess (yes (success prefix read read≡ _ _ _)) = read≡

valueDecSuccess : ∀ {A xs} → (x : Dec (Success A xs)) → Option A (prefixDecSuccess x)
valueDecSuccess (no _) = none
valueDecSuccess (yes (success prefix read read≡ value suffix ps≡)) = some value

suffixDecSuccess : ∀ {A xs} → Dec (Success A xs) → List Σ
suffixDecSuccess (yes s) = Success.suffix s
suffixDecSuccess{xs = xs} (no _) = xs

@0 ps≡DecSuccess : ∀ {A xs} → (x : Dec (Success A xs)) → prefixDecSuccess x ++ suffixDecSuccess x ≡ xs
ps≡DecSuccess (no _) = refl
ps≡DecSuccess (yes (success _ _ _ _ _ ps≡)) = ps≡

@0 yesPrefixDecSuccess : ∀ {A xs ys zs} → NonNesting A
                         → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → A ys → prefixDecSuccess x ≡ ys
yesPrefixDecSuccess nn (no ¬v) ++≡ v = ‼ (⊥-elim $ contradiction (success _ _ refl v _ ++≡) ¬v)
yesPrefixDecSuccess nn (yes (success prefix read read≡ value suffix ps≡)) ++≡ v =
  ‼ nn (trans₀ ps≡ (sym ++≡)) value v

@0 noPrefixDecSuccess : ∀ {A B xs ys zs} → NoConfusion A B
                        → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → B ys → prefixDecSuccess x ≡ []
noPrefixDecSuccess nc (no ¬parse) ++≡ v = refl
noPrefixDecSuccess nc (yes (success prefix read read≡ v' suffix ps≡)) ++≡ v =
  ⊥-elim (contradiction v (nc (trans₀ ps≡ (sym ++≡)) v'))

@0 noReadDecSuccess : ∀ {A B xs ys zs} → NoConfusion A B
                        → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → B ys → readDecSuccess x ≡ 0
noReadDecSuccess nc (no ¬parse) ++≡ v = refl
noReadDecSuccess nc (yes (success prefix read read≡ v' suffix ps≡)) ++≡ v =
  ⊥-elim (contradiction v (nc (trans₀ ps≡ (sym ++≡)) v'))


module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where

  open ≡-Reasoning

  parseOption₂ : {A B : List Σ → Set} → NonNesting A → NonNesting B → NoConfusion A B
                 → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
                 → M (Level.Lift _ ⊤)
                 → ∀ n → Parser (M ∘ Dec) (ExactLength (&ₚ (Option A) (Option B)) n)
  runParser (parseOption₂ nn₁ nn₂ nc p₁ p₂ underflow 0) xs =
    return (yes (success [] _ refl (mk×ₚ (mk&ₚ none none refl) refl refl) xs refl))
  runParser (parseOption₂{B = B} nn₁ nn₂ nc p₁ p₂ underflow n'@(suc n)) xs = do
    x₁ ← runParser (parse≤ n' p₁ nn₁ (return (Level.lift tt))) xs
    case <-cmp n' (readDecSuccess x₁) of λ where
      (tri< n'<r₁ _ _) →
        let @0 n'≮r₁ : n' ≮ readDecSuccess x₁
            n'≮r₁ = case x₁ ret (λ x → n' ≮ readDecSuccess x) of λ where
              (no _) ()
              (yes (success prefix read read≡ (mk×ₚ value valueLen refl) suffix ps≡)) → ‼
                ≤⇒≯ (≤-trans (Lemmas.≡⇒≤ read≡) valueLen)
        in
        contradiction n'<r₁ n'≮r₁
      (tri≈ _ n'≡r₁ _) →
        return (yes
          (success (prefixDecSuccess x₁) _ (read≡DecSuccess x₁)
            (mk×ₚ
              (mk&ₚ{bs₁ = prefixDecSuccess x₁}
                (mapOption (λ where (mk×ₚ v vLen refl) → v) (valueDecSuccess x₁))
                none (solve (++-monoid Σ)))
              (‼ sym (trans₀ (n'≡r₁) (read≡DecSuccess x₁))) refl)
            (suffixDecSuccess x₁)
            (ps≡DecSuccess x₁)))
      (tri> _ _ n'>r₁) → do
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ v₁Len refl) suf₁ ps≡₁)
          ← runParser (parseExactLength nn₂ underflow p₂
                        (n' - readDecSuccess x₁)) (suffixDecSuccess x₁)
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} none none refl) () refl) suffix ps≡)
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} (some v₁) none refl) vLen refl) suffix ps≡) →
                contradiction
                  (begin readDecSuccess x₁ ≡⟨ read≡DecSuccess x₁ ⟩
                         length (prefixDecSuccess x₁)
                           ≡⟨ cong length
                                (yesPrefixDecSuccess{zs = suffix} (withinLength-nonnesting nn₁)
                                  x₁ (trans₀ (bs₁ ++ suffix ≡ (bs₁ ++ []) ++ suffix ∋ solve (++-monoid Σ)) ps≡)
                                  (mk×ₚ v₁
                                    (Lemmas.≡⇒≤ (trans₀ (cong length (bs₁ ≡ bs₁ ++ [] ∋ solve (++-monoid Σ))) vLen))
                                    refl)) ⟩
                         length bs₁ ≡⟨ cong length (bs₁ ≡ bs₁ ++ [] ∋ solve (++-monoid Σ))  ⟩
                         length (bs₁ ++ []) ≡⟨ vLen ⟩
                         n' ∎)
                  (<⇒≢ n'>r₁)
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₂ = bs₂} none (some v₂) refl) vLen refl) suffix ps≡) →
                contradiction
                  (success bs₂ _ refl
                    (mk×ₚ v₂
                      (begin (length prefix ≡⟨ vLen ⟩
                             n' ≡⟨ refl ⟩
                             n' - 0 ≡⟨ cong (n' -_)
                                         (sym (‼ noReadDecSuccess{B = B} (withinLength-noconfusion₁ λ {xs₁}{ys₁}{xs₂}{ys₂} → nc {xs₁}{ys₁}{xs₂}{ys₂}) x₁ ps≡ v₂)) ⟩
                             n' - readDecSuccess x₁ ∎))
                      refl)
                    suffix
                    (begin (prefix ++ suffix ≡⟨ ps≡ ⟩
                           xs ≡⟨ (sym $ ps≡DecSuccess x₁) ⟩
                           prefixDecSuccess x₁ ++ suffixDecSuccess x₁
                             ≡⟨ cong (_++ suffixDecSuccess x₁)
                                  (noPrefixDecSuccess{B = B}
                                    (withinLength-noconfusion₁ λ {xs₁}{ys₁}{xs₂}{ys₂} → nc {xs₁}{ys₁}{xs₂}{ys₂})
                                    x₁ ps≡ v₂) ⟩
                           suffixDecSuccess x₁ ∎)))
                  ¬parse
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} (some v₁) (some v₂) refl) vLen refl) suffix ps≡) → ‼
                let @0 ps≡' : bs₁ ++ bs₂ ++ suffix ≡ prefixDecSuccess x₁ ++ suffixDecSuccess x₁
                    ps≡' = trans₀ ((trans₀ (bs₁ ++ bs₂ ++ suffix ≡ (bs₁ ++ bs₂) ++ suffix ∋ solve (++-monoid Σ)) ps≡)) (sym (ps≡DecSuccess x₁))
                in
                contradiction
                  (success bs₂ _ refl
                    (mk×ₚ v₂
                      (begin (length bs₂ ≡⟨ sym (m+n∸m≡n (length bs₁) _) ⟩
                             length bs₁ + length bs₂ - length bs₁ ≡⟨ cong (_- length bs₁) (sym (length-++ bs₁)) ⟩
                             length (bs₁ ++ bs₂) - length bs₁ ≡⟨ cong (_- length bs₁) vLen ⟩
                             n' - length bs₁ ≡⟨ cong ((n' -_) ∘ length)
                                                  (bs₁ ≡ prefixDecSuccess x₁ ∋
                                                   sym (yesPrefixDecSuccess (withinLength-nonnesting nn₁) x₁
                                                          (trans₀ (bs₁ ++ bs₂ ++ suffix ≡ (bs₁ ++ bs₂) ++ suffix ∋
                                                                   solve (++-monoid Σ)) ps≡)
                                                          (mk×ₚ v₁ (≤-trans (Lemmas.length-++-≤₁ bs₁ bs₂) (Lemmas.≡⇒≤ vLen)) refl))) ⟩
                             n' - length (prefixDecSuccess x₁) ≡⟨ cong (n' -_) (sym (read≡DecSuccess x₁)) ⟩
                             n' - readDecSuccess x₁ ∎))
                      refl)
                    suffix
                    (Lemmas.++-cancel≡ˡ bs₁ (prefixDecSuccess x₁)
                      (sym (yesPrefixDecSuccess ((withinLength-nonnesting nn₁)) x₁
                              (trans₀ ps≡' (ps≡DecSuccess x₁))
                              (mk×ₚ v₁ ((≤-trans (Lemmas.length-++-≤₁ bs₁ bs₂) (Lemmas.≡⇒≤ vLen))) refl)))
                      ps≡'))
                  ¬parse
        return (yes
          (success
            (prefixDecSuccess x₁ ++ pre₁) (readDecSuccess x₁ + r₁)
            (begin (readDecSuccess x₁ + r₁ ≡⟨ cong₂ _+_ (read≡DecSuccess x₁) r₁≡ ⟩
                   length (prefixDecSuccess x₁) + length pre₁ ≡⟨ (sym $ length-++ (prefixDecSuccess x₁)) ⟩
                   length (prefixDecSuccess x₁ ++ pre₁) ∎))
            (mk×ₚ
              (mk&ₚ (mapOption (λ where (mk×ₚ v _ refl) → v) (valueDecSuccess x₁)) (some v₁) refl)
              (‼ (begin length (prefixDecSuccess x₁ ++ pre₁) ≡⟨ length-++ (prefixDecSuccess x₁) ⟩
                        length (prefixDecSuccess x₁) + length pre₁ ≡⟨ cong₂ _+_ (sym (read≡DecSuccess x₁)) v₁Len ⟩
                        readDecSuccess x₁ + (n' - readDecSuccess x₁) ≡⟨ Lemmas.m+n-m≡n (<⇒≤ n'>r₁) ⟩
                        n' ∎))
              refl)
            suf₁
            (begin (prefixDecSuccess x₁ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
                   prefixDecSuccess x₁ ++ pre₁ ++ suf₁ ≡⟨ cong (prefixDecSuccess x₁ ++_) ps≡₁ ⟩
                   prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ≡⟨ ps≡DecSuccess x₁ ⟩
                   xs ∎)))
