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

@0 noPrefixDecSuccess : ∀ {@0 A B xs ys zs} → NoConfusion A B
                        → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → B ys → prefixDecSuccess x ≡ []
noPrefixDecSuccess nc (no ¬parse) ++≡ v = refl
noPrefixDecSuccess nc (yes (success prefix read read≡ v' suffix ps≡)) ++≡ v =
  ⊥-elim (contradiction v (nc (trans₀ ps≡ (sym ++≡)) v'))

ynPrefixDecSuccess : ∀ {@0 A B ws xs ys zs} → NonNesting A → NoConfusion A B
                     → (x : Dec (Success A xs)) → ws ++ ys ++ zs ≡ xs → Option A ws → B ys → prefixDecSuccess x ≡ ws
ynPrefixDecSuccess{B = B}{ys = ys} nn nc (no _) ++≡  none v₂     = refl
ynPrefixDecSuccess{B = B}{ys = ys} nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡  none v₂     =
  ‼ ⊥-elim (contradiction
    v₂
    (nc (trans₀ ps≡ (sym ++≡)) value))
ynPrefixDecSuccess nn nc (no ¬parse) ++≡ (some x₁) v₂ =
  ‼ (⊥-elim (contradiction (success _ _ refl x₁ _ ++≡) ¬parse))
ynPrefixDecSuccess nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡ (some x₁) v₂ =
  ‼ nn (trans₀ ps≡ (sym ++≡)) value x₁

-- ynPrefixDecSuccess nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡  none v₂ =
--   ‼ ⊥-elim (nc (trans₀ ps≡ (trans₀ (sym ++≡) (sym (++-identityʳ _)))) value v₂)
-- ynPrefixDecSuccess nn nc (yes (success prefix read read≡ value suffix ps≡)) ++≡ (some x) v₂ =
--   ‼ nn (trans₀ ps≡ (sym ++≡)) value x
-- ynPrefixDecSuccess nn nc (no ¬success) ++≡ v₁ v₂ = {!noPrefixDecSuccess nc !}

@0 noReadDecSuccess : ∀ {A B xs ys zs} → NoConfusion A B
                        → (x : Dec (Success A xs)) → ys ++ zs ≡ xs → B ys → readDecSuccess x ≡ 0
noReadDecSuccess nc (no ¬parse) ++≡ v = refl
noReadDecSuccess nc (yes (success prefix read read≡ v' suffix ps≡)) ++≡ v =
  ⊥-elim (contradiction v (nc (trans₀ ps≡ (sym ++≡)) v'))

@0 withinLengthDecSuccess : ∀ {A xs n} → (x : Dec (Success (WithinLength A n) xs)) → readDecSuccess x ≤ n
withinLengthDecSuccess (no _) = z≤n
withinLengthDecSuccess {n = n} (yes (success prefix read read≡ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) suffix ps≡)) =
  subst₀ (λ x → x ≤ n) (sym read≡) sndₚ₁

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where

  parseOption₁ExactLength
    : {@0 A : List Σ → Set}
      → @0 NonEmpty A → @0 NonNesting A
      → (underflow : M (Level.Lift _ ⊤))
      → Parser (M ∘ Dec) A
      → ∀ n → Parser (M ∘ Dec) (ExactLength (Option A) n)
  runParser (parseOption₁ExactLength ne nn u p zero) xs =
    return (yes (success [] 0 refl (mk×ₚ none (─ refl) refl) xs refl))
  runParser (parseOption₁ExactLength ne nn u p n'@(suc n)) xs = do
    yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ v₁Len bs≡) suf₁ ps≡₁) ← runParser (parseExactLength nn u p n') xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (some x) (─ v₁Len) refl) suffix ps≡) →
            contradiction
              (success prefix _ read≡ (mk×ₚ x (─ v₁Len) refl) suffix ps≡)
              ¬parse
    return (yes
      (success pre₁ _ r₁≡ (mk×ₚ (some v₁) v₁Len bs≡) suf₁ ps≡₁))


  parseOption₁&₁≤ : {@0 A B : List Σ → Set}
                    → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
                    → @0 NonNesting A → @0 NonNesting B
                    → @0 NoConfusion A B
                    → (mismatch : M (Level.Lift _ ⊤))
                    → ∀ n → Parser (M ∘ Dec) (WithinLength (&ₚ (Option A) B) n)
  runParser (parseOption₁&₁≤{A}{B} p₁ p₂ nn₁ nn₂ nc mismatch n) xs = do
    x₁ ← runParser (parse≤ n p₁ nn₁ mismatch) xs
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (─ v₀Len) refl) suf₀ ps≡)
      ← runParser (parse≤ (n - readDecSuccess x₁) p₂ nn₂ mismatch) (suffixDecSuccess x₁)
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} v₀ v₁ refl) (─ vLen) refl) suffix ps≡) → ‼
            let @0 ps≡' : prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ≡ bs₁ ++ bs₂ ++ suffix
                ps≡' = trans₀ (trans₀ (ps≡DecSuccess x₁) (sym ps≡)) ((bs₁ ++ bs₂) ++ suffix ≡ bs₁ ++ bs₂ ++ suffix ∋ solve (++-monoid Σ))

                @0 v₀' : Option (WithinLength A n) bs₁
                v₀' = mapOptionK (λ x → mk×ₚ x (─ ≤-trans (Lemmas.length-++-≤₁ bs₁ _) vLen) refl) v₀

                nc' : NoConfusion (WithinLength A n) B
                nc' = noconfusion×ₚ₁ (λ {xs₁'}{ys₁'}{xs₂'}{ys₂'} → nc{xs₁'}{ys₁'}{xs₂'}{ys₂'})

                @0 pre₀≡ : prefixDecSuccess x₁ ≡ bs₁
                pre₀≡ =
                  ynPrefixDecSuccess{A = WithinLength A n}{B = B}
                    (withinLength-nonnesting nn₁)
                    nc' x₁
                    (trans₀ (sym ps≡') (ps≡DecSuccess x₁))
                    v₀' v₁
            in
            contradiction
              (success bs₂ _ refl
                (mk×ₚ v₁
                  (─ (begin length bs₂ ≡⟨ sym (m+n∸m≡n (length bs₁) (length bs₂)) ⟩
                            length bs₁ + length bs₂ - length bs₁ ≡⟨ cong (_- length bs₁) (sym (length-++ bs₁)) ⟩
                            length (bs₁ ++ bs₂) - length bs₁ ≤⟨ ∸-monoˡ-≤ (length bs₁) vLen ⟩
                            n - length bs₁ ≡⟨ cong ((n -_) ∘ length) (sym pre₀≡) ⟩
                            n - length (prefixDecSuccess x₁) ≡⟨ cong (n -_) (sym (read≡DecSuccess x₁)) ⟩
                            n - readDecSuccess x₁ ∎))
                  refl) suffix (Lemmas.++-cancel≡ˡ _ _ (sym pre₀≡) (sym ps≡')))
              ¬parse
    return (yes
      (success (prefixDecSuccess x₁ ++ pre₀) (readDecSuccess x₁ + r₀)
        (≡R.begin (readDecSuccess x₁ + r₀ ≡R.≡⟨ cong₂ _+_ (read≡DecSuccess x₁) r₀≡ ⟩
               length (prefixDecSuccess x₁) + length pre₀ ≡R.≡⟨ sym (length-++ (prefixDecSuccess x₁)) ⟩
               length (prefixDecSuccess x₁ ++ pre₀) ≡R.∎))
        (mk×ₚ
          (mk&ₚ
            (mapOption (λ where {xs} (mk×ₚ v (─ vLen) refl) → v) (valueDecSuccess x₁))
            v₀ refl) (
          (─ (begin length (prefixDecSuccess x₁ ++ pre₀) ≡⟨ length-++ (prefixDecSuccess x₁) ⟩
                    length (prefixDecSuccess x₁) + length pre₀ ≡⟨ cong (_+ length pre₀) (sym (read≡DecSuccess x₁)) ⟩
                    readDecSuccess x₁ + length pre₀ ≤⟨ +-monoʳ-≤ (readDecSuccess x₁) v₀Len ⟩
                    readDecSuccess x₁ + (n - readDecSuccess x₁) ≡⟨ m+[n∸m]≡n (withinLengthDecSuccess x₁) ⟩
                    n ∎))) refl)
        suf₀
        (≡R.begin (prefixDecSuccess x₁ ++ pre₀) ++ suf₀ ≡R.≡⟨ solve (++-monoid Σ) ⟩
               prefixDecSuccess x₁ ++ pre₀ ++ suf₀ ≡R.≡⟨ cong (prefixDecSuccess x₁ ++_) ps≡ ⟩
               prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ≡R.≡⟨ ps≡DecSuccess x₁ ⟩
               xs ≡R.∎)))
    where
    open ≤-Reasoning
    module ≡R = ≡-Reasoning



  open ≡-Reasoning

  parseOption₁&₁ : {@0 A B : List Σ → Set}
                   → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
                   → @0 NonNesting A → @0 NonNesting B
                   → @0 NoConfusion A B
                   → (mismatch : M (Level.Lift _ ⊤))
                   → ∀ n → Parser (M ∘ Dec) (ExactLength (&ₚ (Option A) B) n)
  runParser (parseOption₁&₁{A}{B} p₁ p₂ nn₁ nn₂ nc mismatch n) xs = do
    x₁ ← runParser (parse≤ n p₁ nn₁ mismatch) xs
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (─ v₀Len) refl) suf₀ ps≡)
      ← runParser (parseExactLength nn₂ mismatch p₂ (n - readDecSuccess x₁)) (suffixDecSuccess x₁)
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} v₀ v₁ refl) (─ vLen) refl) suffix ps≡) → ‼
            let @0 ps≡' : prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ≡ bs₁ ++ bs₂ ++ suffix
                ps≡' = trans₀ (trans₀ (ps≡DecSuccess x₁) (sym ps≡)) ((bs₁ ++ bs₂) ++ suffix ≡ bs₁ ++ bs₂ ++ suffix ∋ solve (++-monoid Σ))

                @0 v₀' : Option (WithinLength A n) bs₁
                v₀' = mapOptionK (λ x → mk×ₚ x (─ subst (length bs₁ ≤_) vLen (Lemmas.length-++-≤₁ bs₁ _)) refl) v₀

                nc' : NoConfusion (WithinLength A n) B
                nc' = noconfusion×ₚ₁ (λ {xs₁'}{ys₁'}{xs₂'}{ys₂'} → nc{xs₁'}{ys₁'}{xs₂'}{ys₂'})

                @0 pre₀≡ : prefixDecSuccess x₁ ≡ bs₁
                pre₀≡ =
                  ynPrefixDecSuccess{A = WithinLength A n}{B = B}
                    (withinLength-nonnesting nn₁)
                    nc' x₁
                    (trans₀ (sym ps≡') (ps≡DecSuccess x₁))
                    v₀' v₁
            in
            contradiction
              (success bs₂ _ refl
                (mk×ₚ v₁
                  (─ (begin (length bs₂ ≡⟨ sym (m+n∸m≡n (length bs₁) (length bs₂)) ⟩
                         length bs₁ + length bs₂ - length bs₁ ≡⟨ cong (_- length bs₁) (sym (length-++ bs₁)) ⟩
                         length (bs₁ ++ bs₂) - length bs₁ ≡⟨ cong (_- length bs₁) vLen ⟩
                         n - length bs₁ ≡⟨ cong ((n -_) ∘ length) (sym pre₀≡) ⟩
                         n - length (prefixDecSuccess x₁) ≡⟨ cong (n -_) (sym (read≡DecSuccess x₁)) ⟩
                         n - readDecSuccess x₁ ∎))) refl)
                suffix
                (Lemmas.++-cancel≡ˡ _ _ (sym pre₀≡) (sym ps≡')))
              ¬parse
    return (yes
      (success (prefixDecSuccess x₁ ++ pre₀) (readDecSuccess x₁ + r₀)
        (begin (readDecSuccess x₁ + r₀ ≡⟨ cong₂ _+_ (read≡DecSuccess x₁) r₀≡ ⟩
               length (prefixDecSuccess x₁) + length pre₀ ≡⟨ sym (length-++ (prefixDecSuccess x₁)) ⟩
               length (prefixDecSuccess x₁ ++ pre₀) ∎))
        (mk×ₚ
          (mk&ₚ (mapOption (λ where {xs} (mk×ₚ v (─ vLen) refl) → v) (valueDecSuccess x₁)) v₀ refl)
          (─ (begin length (prefixDecSuccess x₁ ++ pre₀) ≡⟨ length-++ (prefixDecSuccess x₁) ⟩
                    length (prefixDecSuccess x₁) + length pre₀ ≡⟨ cong₂ _+_ (sym (read≡DecSuccess x₁)) v₀Len ⟩
                    readDecSuccess x₁ + (n - readDecSuccess x₁) ≡⟨ m+[n∸m]≡n (withinLengthDecSuccess x₁) ⟩
                    n ∎))
          refl)
        suf₀
        (begin (prefixDecSuccess x₁ ++ pre₀) ++ suf₀ ≡⟨ solve (++-monoid Σ) ⟩
               prefixDecSuccess x₁ ++ pre₀ ++ suf₀ ≡⟨ cong (prefixDecSuccess x₁ ++_) ps≡ ⟩
               prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ≡⟨ ps≡DecSuccess x₁ ⟩
               xs ∎)))

  parseOption₂ : {A B : List Σ → Set}
                 → (@0 _ : NonNesting A) → (@0 _ : NonNesting B) → (@0 _ : NoConfusion A B)
                 → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
                 → M (Level.Lift _ ⊤)
                 → ∀ n → Parser (M ∘ Dec) (ExactLength (&ₚ (Option A) (Option B)) n)
  runParser (parseOption₂ nn₁ nn₂ nc p₁ p₂ underflow 0) xs =
    return (yes (success [] _ refl (mk×ₚ (mk&ₚ none none refl) (─ refl) refl) xs refl))
  runParser (parseOption₂{B = B} nn₁ nn₂ nc p₁ p₂ underflow n'@(suc n)) xs = do
    x₁ ← runParser (parse≤ n' p₁ nn₁ (return (Level.lift tt))) xs
    case <-cmp n' (readDecSuccess x₁) of λ where
      (tri< n'<r₁ _ _) →
        let @0 n'≮r₁ : n' ≮ readDecSuccess x₁
            n'≮r₁ = case x₁ ret (λ x → n' ≮ readDecSuccess x) of λ where
              (no _) ()
              (yes (success prefix read read≡ (mk×ₚ value (─ valueLen) refl) suffix ps≡)) → ‼
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
              (─ sym (trans₀ (n'≡r₁) (read≡DecSuccess x₁))) refl)
            (suffixDecSuccess x₁)
            (ps≡DecSuccess x₁)))
      (tri> _ _ n'>r₁) → do
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ (─ v₁Len) refl) suf₁ ps≡₁)
          ← runParser (parseExactLength nn₂ underflow p₂
                        (n' - readDecSuccess x₁)) (suffixDecSuccess x₁)
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} none none refl) () refl) suffix ps≡)
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} (some v₁) none refl) (─ vLen) refl) suffix ps≡) →
                contradiction
                  (begin readDecSuccess x₁ ≡⟨ read≡DecSuccess x₁ ⟩
                         length (prefixDecSuccess x₁)
                           ≡⟨ cong length
                                (yesPrefixDecSuccess{zs = suffix} (withinLength-nonnesting nn₁)
                                  x₁ (trans₀ (bs₁ ++ suffix ≡ (bs₁ ++ []) ++ suffix ∋ solve (++-monoid Σ)) ps≡)
                                  (mk×ₚ v₁
                                    (─ Lemmas.≡⇒≤ (trans₀ (cong length (bs₁ ≡ bs₁ ++ [] ∋ solve (++-monoid Σ))) vLen))
                                    refl)) ⟩
                         length bs₁ ≡⟨ cong length (bs₁ ≡ bs₁ ++ [] ∋ solve (++-monoid Σ))  ⟩
                         length (bs₁ ++ []) ≡⟨ vLen ⟩
                         n' ∎)
                  (<⇒≢ n'>r₁)
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₂ = bs₂} none (some v₂) refl) (─ vLen) refl) suffix ps≡) →
                contradiction
                  (success bs₂ _ refl
                    (mk×ₚ v₂
                      (─ (begin
                             length prefix ≡⟨ vLen ⟩
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
              (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} (some v₁) (some v₂) refl) (─ vLen) refl) suffix ps≡) → ‼
                let @0 ps≡' : bs₁ ++ bs₂ ++ suffix ≡ prefixDecSuccess x₁ ++ suffixDecSuccess x₁
                    ps≡' = trans₀ ((trans₀ (bs₁ ++ bs₂ ++ suffix ≡ (bs₁ ++ bs₂) ++ suffix ∋ solve (++-monoid Σ)) ps≡)) (sym (ps≡DecSuccess x₁))
                in
                contradiction
                  (success bs₂ _ refl
                    (mk×ₚ v₂
                      (─ (begin
                             length bs₂ ≡⟨ sym (m+n∸m≡n (length bs₁) _) ⟩
                             length bs₁ + length bs₂ - length bs₁ ≡⟨ cong (_- length bs₁) (sym (length-++ bs₁)) ⟩
                             length (bs₁ ++ bs₂) - length bs₁ ≡⟨ cong (_- length bs₁) vLen ⟩
                             n' - length bs₁ ≡⟨ cong ((n' -_) ∘ length)
                                                  (bs₁ ≡ prefixDecSuccess x₁ ∋
                                                   sym (yesPrefixDecSuccess (withinLength-nonnesting nn₁) x₁
                                                          (trans₀ (bs₁ ++ bs₂ ++ suffix ≡ (bs₁ ++ bs₂) ++ suffix ∋
                                                                   solve (++-monoid Σ)) ps≡)
                                                          (mk×ₚ v₁ (─ ≤-trans (Lemmas.length-++-≤₁ bs₁ bs₂) (Lemmas.≡⇒≤ vLen)) refl))) ⟩
                             n' - length (prefixDecSuccess x₁) ≡⟨ cong (n' -_) (sym (read≡DecSuccess x₁)) ⟩
                             n' - readDecSuccess x₁ ∎))
                      refl)
                    suffix
                    (Lemmas.++-cancel≡ˡ bs₁ (prefixDecSuccess x₁)
                      (sym (yesPrefixDecSuccess ((withinLength-nonnesting nn₁)) x₁
                              (trans₀ ps≡' (ps≡DecSuccess x₁))
                              (mk×ₚ v₁ (─ (≤-trans (Lemmas.length-++-≤₁ bs₁ bs₂) (Lemmas.≡⇒≤ vLen))) refl)))
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
              (─ (begin length (prefixDecSuccess x₁ ++ pre₁) ≡⟨ length-++ (prefixDecSuccess x₁) ⟩
                        length (prefixDecSuccess x₁) + length pre₁ ≡⟨ cong₂ _+_ (sym (read≡DecSuccess x₁)) v₁Len ⟩
                        readDecSuccess x₁ + (n' - readDecSuccess x₁) ≡⟨ Lemmas.m+n-m≡n (<⇒≤ n'>r₁) ⟩
                        n' ∎))
              refl)
            suf₁
            (begin (prefixDecSuccess x₁ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
                   prefixDecSuccess x₁ ++ pre₁ ++ suf₁ ≡⟨ cong (prefixDecSuccess x₁ ++_) ps≡₁ ⟩
                   prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ≡⟨ ps≡DecSuccess x₁ ⟩
                   xs ∎)))

  parseOption₃ : {A B C : List Σ → Set}
                 → (@0 _ : NonNesting A) → (@0 _ : NonNesting B) → (@0 _ : NonNesting C)
                 → (@0 _ : NoConfusion A B) (@0 _ : NoConfusion A C) → (@0 _ : NoConfusion B C)
                 → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B → Parser (M ∘ Dec) C
                 → M (Level.Lift _ ⊤)
                 → ∀ n → Parser (M ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Option B) (Option C))) n)
  runParser (parseOption₃ nn₁ nn₂ nn₃ nc₁ nc₂ nc₃ p₁ p₂ p₃ underflow 0) xs =
    return (yes (success _ _ refl (mk×ₚ (mk&ₚ none (mk&ₚ none none refl) refl) (─ refl) refl) xs refl))
  runParser (parseOption₃{A}{B}{C} nn₁ nn₂ nn₃ nc₁ nc₂ nc₃ p₁ p₂ p₃ underflow n'@(suc n)) xs = do
    x₁ ← runParser (parse≤ n' p₁ nn₁ (return (Level.lift tt))) xs
    yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ (─ v₁Len) refl) suf₁ ps≡) ←
      runParser (parseOption₂ nn₂ nn₃ nc₃ p₂ p₃ underflow (n' - readDecSuccess x₁)) (suffixDecSuccess x₁)
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mk&ₚ none (mk&ₚ{bs₁ = bs₁}{bs₂} (some v₂) v₃ refl) refl) (─ valueLen) refl) suffix ps≡) → ‼
           let @0 ps≡' : bs₁ ++ bs₂ ++ suffix ≡ xs
               ps≡' = trans₀ (bs₁ ++ bs₂ ++ suffix ≡ (bs₁ ++ bs₂) ++ suffix ∋ solve (++-monoid Σ)) ps≡
           in
           contradiction
              (success _ _ refl
                (mk×ₚ (mk&ₚ (some v₂) v₃ refl)
                  (─ (begin
                         length (bs₁ ++ bs₂) ≡⟨ valueLen ⟩
                         n' ≡⟨ refl ⟩
                         n' - 0 ≡⟨ cong ((n' ∸_) ∘ length)
                                     (sym $ noPrefixDecSuccess{B = B}
                                       (λ {xs₁}{ys₁}{xs₂}{ys₂} → noconfusion×ₚ₁ (λ {xs₂ = xs₂}{ys₂} → nc₁{xs₂ = xs₂}{ys₂}){xs₁}{ys₁}{xs₂}{ys₂}) x₁ ps≡' v₂) ⟩
                         n' - length (prefixDecSuccess x₁) ≡⟨ cong (n' ∸_) (sym $ read≡DecSuccess x₁) ⟩
                         n' - readDecSuccess x₁ ∎))
                  refl)
                suffix
                (begin (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                       xs ≡⟨ (sym $ ps≡DecSuccess x₁) ⟩
                       prefixDecSuccess x₁ ++ suffixDecSuccess x₁
                         ≡⟨ cong (_++ suffixDecSuccess x₁)
                              (noPrefixDecSuccess{B = B} (λ {xs₁}{ys₁}{xs₂}{ys₂} → noconfusion×ₚ₁ (λ {xs₂ = xs₂}{ys₂} → nc₁{xs₂ = xs₂}{ys₂}){xs₁}{ys₁}{xs₂}{ys₂}) x₁
                                ps≡' v₂) ⟩
                       suffixDecSuccess x₁ ∎))
              ¬parse
          (success prefix read read≡ (mk×ₚ (mk&ₚ none (mk&ₚ{bs₁ = bs₁}{bs₂} none (some v₃) refl) refl) (─ valueLen) refl) suffix ps≡) →
            contradiction
              (success _ _ refl
                (mk×ₚ (mk&ₚ none (some v₃) refl)
                  (─ (begin
                         length bs₂ ≡⟨ valueLen ⟩
                         n' ≡⟨ refl ⟩
                         n' - 0 ≡⟨ cong ((n' -_) ∘ length)
                                     (sym $ noPrefixDecSuccess {B = C}
                                       ((λ {xs₁}{ys₁}{xs₂}{ys₂} → noconfusion×ₚ₁ (λ {xs₂ = xs₂}{ys₂} → nc₂{xs₂ = xs₂}{ys₂}){xs₁}{ys₁}{xs₂}{ys₂}))
                                       x₁ ps≡ v₃) ⟩
                         n' - length (prefixDecSuccess x₁) ≡⟨ cong (n' ∸_) (sym $ read≡DecSuccess x₁) ⟩
                         n' - readDecSuccess x₁ ∎))
                  refl)
                suffix
                (begin (prefix ++ suffix ≡⟨ ps≡ ⟩
                       xs ≡⟨ (sym $ ps≡DecSuccess x₁) ⟩
                       prefixDecSuccess x₁ ++ suffixDecSuccess x₁
                         ≡⟨ cong (_++ suffixDecSuccess x₁)
                              (noPrefixDecSuccess{B = C} ((λ {xs₁}{ys₁}{xs₂}{ys₂} → noconfusion×ₚ₁ (λ {xs₂ = xs₂}{ys₂} → nc₂{xs₂ = xs₂}{ys₂}){xs₁}{ys₁}{xs₂}{ys₂})) x₁ ps≡ v₃) ⟩
                       suffixDecSuccess x₁ ∎)))
              ¬parse
          (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁ = bs₁} (some v₁) (mk&ₚ{bs₁ = bs₂}{bs₃} v₂ v₃ refl) refl) (─ valueLen) refl) suffix ps≡) → ‼
            let @0 ps≡' : bs₁ ++ bs₂ ++ bs₃ ++ suffix ≡ xs
                ps≡' = trans₀ (bs₁ ++ bs₂ ++ bs₃ ++ suffix ≡ (bs₁ ++ bs₂ ++ bs₃) ++ suffix ∋ solve (++-monoid Σ)) ps≡

                @0 bs₁≡ : bs₁ ≡ prefixDecSuccess x₁
                bs₁≡ = (sym $ yesPrefixDecSuccess (withinLength-nonnesting nn₁) x₁ ps≡'
                                                (mk×ₚ v₁ (─ ≤-trans (Lemmas.length-++-≤₁ bs₁ (bs₂ ++ bs₃)) (Lemmas.≡⇒≤ valueLen)) refl))
            in
            contradiction
              (success (bs₂ ++ bs₃) _ refl
                (mk×ₚ (mk&ₚ v₂ v₃ refl)
                  (─ (begin
                         length (bs₂ ++ bs₃) ≡⟨ (sym $ m+n∸m≡n (length bs₁) _) ⟩
                         length bs₁ + length (bs₂ ++ bs₃) - length bs₁ ≡⟨ cong (_∸ length bs₁) (sym $ length-++ bs₁) ⟩
                         length (bs₁ ++ bs₂ ++ bs₃) - length bs₁ ≡⟨ cong (_∸ length bs₁) valueLen ⟩
                         n' - length bs₁ ≡⟨ cong ((n' ∸_) ∘ length)
                                              (sym $ yesPrefixDecSuccess (withinLength-nonnesting nn₁) x₁ ps≡'
                                                (mk×ₚ v₁ (─ ≤-trans (Lemmas.length-++-≤₁ bs₁ (bs₂ ++ bs₃)) (Lemmas.≡⇒≤ valueLen)) refl)) ⟩
                         n' - length (prefixDecSuccess x₁) ≡⟨ cong (n' ∸_) (sym $ read≡DecSuccess x₁) ⟩
                         n' - readDecSuccess x₁ ∎))
                  refl)
                suffix
                (Lemmas.++-cancel≡ˡ _ _ bs₁≡
                  (begin (bs₁ ++ (bs₂ ++ bs₃) ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                         bs₁ ++ bs₂ ++ bs₃ ++ suffix ≡⟨ ps≡' ⟩
                         xs ≡⟨ (sym $ ps≡DecSuccess x₁) ⟩
                         prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ∎))))
              ¬parse
    return (yes
      (success (prefixDecSuccess x₁ ++ pre₁) n'
        (begin (n' ≡⟨ (sym $ m+[n∸m]≡n (withinLengthDecSuccess x₁)) ⟩
               readDecSuccess x₁ + (n' - readDecSuccess x₁) ≡⟨ cong (readDecSuccess x₁ +_) (sym $ v₁Len) ⟩
               readDecSuccess x₁ + length pre₁ ≡⟨ cong (_+ length pre₁) (read≡DecSuccess x₁) ⟩
               length (prefixDecSuccess x₁) + length pre₁ ≡⟨ (sym $ length-++ (prefixDecSuccess x₁)) ⟩
               length (prefixDecSuccess x₁ ++ pre₁) ∎))
        (mk×ₚ
          (mk&ₚ
            (mapOption (λ {xs = xs} → projectWithinLength{xs = xs}) (valueDecSuccess x₁))
            v₁ refl)
          (─ (begin length (prefixDecSuccess x₁ ++ pre₁)
                      ≡⟨ length-++ (prefixDecSuccess x₁) ⟩
                    length (prefixDecSuccess x₁) + length pre₁
                      ≡⟨ cong₂ _+_ (sym (read≡DecSuccess x₁)) v₁Len ⟩
                    readDecSuccess x₁ + (n' - readDecSuccess x₁)
                      ≡⟨ m+[n∸m]≡n{m = readDecSuccess x₁} (withinLengthDecSuccess x₁) ⟩
                    n' ∎))
          refl) suf₁
          (begin (prefixDecSuccess x₁ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
                 prefixDecSuccess x₁ ++ pre₁ ++ suf₁ ≡⟨ cong (prefixDecSuccess x₁ ++_) ps≡ ⟩
                 prefixDecSuccess x₁ ++ suffixDecSuccess x₁ ≡⟨ ps≡DecSuccess x₁ ⟩
                 xs ∎)))
