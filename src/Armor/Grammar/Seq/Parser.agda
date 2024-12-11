import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq.Properties
import      Armor.Grammar.Seq.TCB
import      Armor.Grammar.Option.Properties
import      Armor.Grammar.Option.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude
open import Tactic.MonoidSolver
  using (solve ; solve-macro)

module Armor.Grammar.Seq.Parser (Σ : Set) where

open Armor.Grammar.Definitions    Σ
open Armor.Grammar.Option.TCB     Σ
  hiding (module Option)
private
  module Option where
    open Armor.Grammar.Option.Properties Σ
open Armor.Grammar.Parser         Σ
open Armor.Grammar.Seq.Properties Σ
open Armor.Grammar.Seq.TCB        Σ

open ≡-Reasoning

parse& : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : @0 List Σ → Set}
         → @0 NoSubstrings A
         → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
         → Parser (M ∘ Dec) (&ₚ A B)
runParser (parse& nn p₁ p₂) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser p₁ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) →
          contradiction
            (success bs₁ _ refl fstₚ (bs₂ ++ suffix)
              (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                     (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                     xs ∎))
            ¬parse
  yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser p₂ suf₀
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) → ‼
          let @0 xs≡ : bs₁ ++ bs₂ ++ suffix      ≡ pre₀ ++ suf₀
              xs≡ = begin bs₁ ++ bs₂ ++ suffix   ≡⟨ solve (++-monoid Σ) ⟩
                          (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                          xs                     ≡⟨ sym ps≡₀ ⟩
                          pre₀ ++ suf₀           ∎

              @0 bs₁≡ : bs₁ ≡ pre₀
              bs₁≡ = nn xs≡ fstₚ v₀
          in
          contradiction
            (success bs₂ _ refl sndₚ suffix
              (++-cancelˡ pre₀ (trans (cong (_++ bs₂ ++ suffix) (sym bs₁≡)) xs≡)))
            ¬parse
  return (yes
    (success (pre₀ ++ pre₁) (r₀ + r₁)
      (begin r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
             length pre₀ + r₁ ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
             length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
             length (pre₀ ++ pre₁) ∎)
      (mk&ₚ v₀ v₁ refl) suf₁
      (begin (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
             pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
             pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
             xs ∎)))

parse&ᵈ : {M : Set → Set} ⦃ _ : Monad M ⦄
          → {A : @0 List Σ → Set} {B : {@0 bs : List Σ} → A bs → @0 List Σ → Set}
          → (@0 _ : NoSubstrings A) (@0 _ : Unambiguous A)
          → Parser (M ∘ Dec) A
          → (∀ {@0 bs} → Singleton (length bs) → (a : A bs) → Parser (M ∘ Dec) (B a))
          → Parser (M ∘ Dec) (&ₚᵈ A B)
runParser (parse&ᵈ{A = A}{B} nn ua p₁ p₂) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser{A = A} p₁ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) →
          contradiction
            (success bs₁ _ refl fstₚ (bs₂ ++ suffix)
              (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                     (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                     xs ∎))
            ¬parse
  yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser (p₂ (singleton r₀ r₀≡) v₀) suf₀
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) → ‼
          let @0 xs≡ : bs₁ ++ bs₂ ++ suffix      ≡ pre₀ ++ suf₀
              xs≡ = begin bs₁ ++ bs₂ ++ suffix   ≡⟨ solve (++-monoid Σ) ⟩
                          (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                          xs                     ≡⟨ sym ps≡₀ ⟩
                          pre₀ ++ suf₀           ∎

              @0 bs₁≡ : bs₁ ≡ pre₀
              bs₁≡ = nn xs≡ fstₚ v₀

              @0 fstₚ≡ : subst₀! A bs₁≡ fstₚ ≡ v₀
              fstₚ≡ =
                ≡-elim (λ {bs} eq → ∀ v₀ → subst₀! A eq fstₚ ≡ v₀)
                  (ua fstₚ) bs₁≡ v₀
          in
          contradiction
            (success bs₂ _ refl
              (subst (λ x → B x bs₂) fstₚ≡
                (≡-elim (λ {pre₀} eq → B (subst₀! A eq fstₚ) bs₂)
                  sndₚ bs₁≡))
              suffix
              (++-cancelˡ pre₀ (trans (cong (_++ bs₂ ++ suffix) (sym bs₁≡)) xs≡)))
            ¬parse
  return (yes
    (success (pre₀ ++ pre₁) (r₀ + r₁)
      (begin r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
             length pre₀ + r₁ ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
             length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
             length (pre₀ ++ pre₁) ∎)
      (mk&ₚ v₀ v₁ refl) suf₁
      (begin (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
             pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
             pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
             xs ∎)))

parseOption₁
  : ∀ {A B} → String → @0 NoSubstrings A 
    → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B
    → Parser (Logging ∘ Dec) (&ₚ (Option A) B)
runParser (parseOption₁ loc ns₁ p₁ p₂) xs = do
  tell $ loc String.++ ": parseOption₁ (present)"
  (no ¬p₁₂) ← runParser (parse& ns₁ p₁ p₂) xs
    where (yes (success pre r r≡ (mk&ₚ v₁ v₂ bs≡) suf ps≡)) → do
      return (yes (success pre r r≡ (mk&ₚ (some v₁) v₂ bs≡) suf ps≡))
  tell $ loc String.++ ": parseOption₁ (absent)"
  (no ¬p₂) ← runParser p₂ xs
    where (yes (success pre r r≡ v₂ suf ps≡)) → do
      return (yes (success pre r r≡ (mk&ₚ none v₂ refl) suf ps≡))
  return ∘ no $ λ where
    (success prefix read read≡ (mk&ₚ none v₂ refl) suffix ps≡) →
      contradiction
        (success prefix read read≡ v₂ suffix ps≡)
        ¬p₂
    (success prefix read read≡ (mk&ₚ{pre₁}{pre₂} (some v₁) v₂ refl) suffix ps≡) →
      contradiction
        (success prefix read read≡ (mk&ₚ v₁ v₂ refl) suffix ps≡)
        ¬p₁₂

module _ where
  open import Armor.Grammar.Parallel      Σ
  open import Armor.Grammar.Option.Parser Σ

  parseOption₂
    : ∀ {A B} → String
      → @0 NoSubstrings A
      → @0 NoSubstrings B
      → @0 NoConfusion A B
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (Option B)) n)
  runParser (parseOption₂{A}{B} loc ns₁ ns₂ nc p₁ p₂ 0) xs =
    return (yes (success [] _ refl (mk×ₚ (mk&ₚ none none refl) (─ refl)) xs refl))
  parseOption₂{A}{B} loc ns₁ ns₂ nc p₁ p₂ n@(suc _) =
    parseEquivalent (ExactLength.equivalent{A = Option A}{B = Option B}) p
    where
    p₁' : Parser (Logging ∘ Dec) (Length≤ A n)
    p₁' = parse≤ n p₁ ns₁ (tell $ loc String.++ ": overlfow (1st)")

    p₂' : {@0 bs : List Σ} → Singleton (length bs) → Parser (Logging ∘ Dec) (ExactLength (Option B) (n - length bs))
    p₂' (singleton r r≡) =
      subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (Option B) (n ∸ x)))
        r≡
        (parseOption₁ExactLength ns₂ silent p₂ _)

    p : Parser (Logging ∘ Dec) (&ₚᵈ (Length≤ (Option A) n) (λ {bs} _ → ExactLength (Option B) (n - length bs)))
    runParser p xs = do
      (yes (success pre₁ r₁ r₁≡ v₁@(mk×ₚ a aLen) suf₁ ps≡₁)) ← runParser p₁' xs
        where (no ¬p₁) → do
        (yes (success pre₁ r₁ r₁≡ (mk×ₚ ob obLen) suf₁ ps≡₁)) ← runParser (parseOption₁ExactLength ns₂ silent p₂ n) xs
          where no ¬op₂ → do
            tell $ loc String.++ ": failed to parse (1st and 2nd)"
            return ∘ no $ λ where
              (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ ob obLen) refl) suffix ps≡) →
                contradiction
                  (success prefix _ read≡ (mk×ₚ ob obLen) suffix ps≡)
                  ¬op₂
              (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a') oaLen) (mk×ₚ ob obLen) refl) suffix ps≡) →
                contradiction
                  (success _ _ refl (mk×ₚ a' oaLen) (bs₂ ++ suffix)
                    (begin
                      bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                      (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                      xs ∎))
                  ¬p₁
        return (yes
          (success pre₁ r₁ r₁≡ (mk&ₚ (mk×ₚ none (─ z≤n)) (mk×ₚ ob obLen) refl) suf₁ ps≡₁))
      (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) ← runParser (p₂'{pre₁} (singleton r₁ r₁≡)) suf₁
        where (no ¬op₂) → do
          tell $ loc String.++ ": failed to parse (2nd)"
          return ∘ no $ λ where
            (success .[] .0 refl (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ none (─ ())) refl) suffix ps≡)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (some b') (─ obLen)) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ prefix ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  prefix ++ suffix ∎
              in
              contradiction
                b'
                (nc ++≡ a)
            (success ._ read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a') oaLen) (mk×ₚ ob obLen) refl) suffix ps≡) →
              let
                @0 ++≡ : bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁
                ++≡ = begin
                  bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                  xs ≡⟨ sym ps≡₁ ⟩
                  pre₁ ++ suf₁ ∎

                @0 pre₁≡ : bs₁ ≡ pre₁
                pre₁≡ = ns₁ ++≡ a' a

                @0 obLen' : length bs₂ ≡ n - length pre₁
                obLen' = subst₀ (λ x → length bs₂ ≡ n ∸ length x) {bs₁} {pre₁} pre₁≡ (¡ obLen)
              in
              contradiction
                (success bs₂ _ refl (mk×ₚ ob (─ obLen')) suffix (Lemmas.++-cancel≡ˡ _ _ pre₁≡ ++≡))
                ¬op₂
      return (yes
        (success (pre₁ ++ pre₂) (r₁ + r₂)
          (begin
            r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
            length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
            length (pre₁ ++ pre₂) ∎)
          (mk&ₚ (mk×ₚ (some a) aLen) v₂ refl)
          suf₂
          (begin
            (pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ pre₂ suf₂ ⟩
            pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
            pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
            xs ∎)))

  parse₂Option₃
    : ∀ {A B C : @0 List Σ → Set} → String
      → @0 NoSubstrings A
      → @0 NoSubstrings B
      → @0 NoSubstrings C
      → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion B C
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Option B) (Option C))) n)
  runParser (parse₂Option₃ loc ns₁ ns₂ ns₃ nc₁₂ nc₁₃ nc₂₃ p₁ p₂ p₃ 0) xs =
    return (yes
      (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ none none refl) refl) (─ refl)) xs refl))
  parse₂Option₃{A}{B}{C} loc ns₁ ns₂ ns₃ nc₁₂ nc₁₃ nc₂₃ p₁ p₂ p₃ n@(suc _) =
    parseEquivalent (ExactLength.equivalent{A = Option A}{B = &ₚ (Option B) (Option C)}) p
    where
    open ≡-Reasoning

    p₁' : Parser (Logging ∘ Dec) (Length≤ A n)
    p₁' = parse≤ n p₁ ns₁ (tell $ loc String.++ ": overlfow (1st)")

    D : {@0 bs₁ : List Σ} → @0 List Σ → Set
    D {bs'} = ExactLength (&ₚ (Option B) (Option C)) (n - length bs') 

    p₂₃' : ∀ {@0 bs₁ : List Σ} → Singleton (length bs₁) → Parser (Logging ∘ Dec) (D{bs₁})
    p₂₃' {bs₁} (singleton r r≡) =
      subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option B) (Option C)) (n - x)))
        {r}{length bs₁}
        r≡
        (parseOption₂ (loc String.++ " (2nd,3rd)") ns₂ ns₃ nc₂₃ p₂ p₃ (n - r))

    p : Parser (Logging ∘ Dec) (&ₚᵈ (Length≤ (Option A) n) λ {bs₁} _ → D{bs₁})
    runParser p xs = do
      (yes (success pre₁ r₁ r₁≡ v₁@(mk×ₚ a₁ aLen) suf₁ ps≡₁)) ← runParser p₁' xs
        where no ¬p₁ → do
          (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) ← runParser (parseOption₂ (loc String.++ " (2nd,3rd)") ns₂ ns₃ nc₂₃ p₂ p₃ n) xs
            where no ¬op₂₃ → do
              tell $ loc String.++ ": failed to parse"
              return ∘ no $ λ where
                (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a) aLen) oaob refl) suffix ps≡) →
                  contradiction
                    (success bs₁ _ refl (mk×ₚ a aLen) (bs₂ ++ suffix)
                      (begin
                        bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs ∎))
                    ¬p₁
                (success prefix read read≡ (mk&ₚ{bs₂ = bs₂} (mk×ₚ none _) oaob refl) suffix ps≡) →
                  contradiction
                    (success prefix _ read≡ oaob suffix ps≡)
                    ¬op₂₃
          return (yes
            (success _ _ r₁≡ (mk&ₚ (mk×ₚ none (─ z≤n)) v₁ refl) suf₁ ps≡₁))
      (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) ← runParser (p₂₃'{pre₁} (singleton r₁ r₁≡)) suf₁
        where no ¬op₂₃ → do
          tell $ loc String.++ ": failed to parse"
          return ∘ no $ λ where
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ{bs₁}{bs₂} (some b') _ refl) oaobLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                b'
                (nc₁₂ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (some c') refl) oaobLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ prefix ++ suffix
                ++≡ = trans ps≡₁ (sym ps≡)
              in
              contradiction
                c'
                (nc₁₃ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none none refl) (─ ())) refl) .xs refl)
            (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a') oaLen) oaob' bs≡) suffix ps≡) →
              let
                @0 ++≡ : bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁
                ++≡ = begin
                  bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
                  prefix ++ suffix ≡⟨ ps≡ ⟩
                  xs ≡⟨ sym ps≡₁ ⟩
                  pre₁ ++ suf₁ ∎

                @0 pre₁≡ : bs₁ ≡ pre₁
                pre₁≡ = ns₁ ++≡ a' a₁
              in
              contradiction
                (success bs₂ _ refl (D {pre₁} bs₂ ∋ subst₀ (λ x → D {x} bs₂) pre₁≡ oaob')
                  suffix
                  (Lemmas.++-cancel≡ˡ _ _ pre₁≡ ++≡))
                ¬op₂₃
      return (yes
        (success (pre₁ ++ pre₂) (r₁ + r₂)
          (begin
            (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
            length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
            length (pre₁ ++ pre₂) ∎))
          (mk&ₚ (mk×ₚ (some a₁) aLen) v₂ refl) suf₂
            (begin
              (pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ pre₂ suf₂ ⟩
              pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
              pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
              xs ∎)))

  parse₂Option₄ : ∀ {A B C D : @0 List Σ → Set} → String
      → @0 NoSubstrings A
      → @0 NoSubstrings B
      → @0 NoSubstrings C
      → @0 NoSubstrings D
      → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D 
      → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion C D
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C → Parser (Logging ∘ Dec) D
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ(Option A) (&ₚ (Option B) (&ₚ (Option C) (Option D)))) n)
  runParser (parse₂Option₄ loc ns₁ ns₂ ns₃ ns₄ nc₁₂ nc₁₃ nc₁₄ nc₂₃ nc₂₄ nc₃₄ p₁ p₂ p₃ p₄ 0) xs =
    return (yes
      (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ none none refl) refl) refl) (─ refl)) xs refl))
  parse₂Option₄{A}{B}{C}{D} loc ns₁ ns₂ ns₃ ns₄ nc₁₂ nc₁₃ nc₁₄ nc₂₃ nc₂₄ nc₃₄ p₁ p₂ p₃ p₄ n@(suc _) =
    parseEquivalent (ExactLength.equivalent{A = Option A}{B = &ₚ (Option B) (&ₚ (Option C) (Option D))}) p
    where
    open ≡-Reasoning

    p₁' : Parser (Logging ∘ Dec) (Length≤ A n)
    p₁' = parse≤ n p₁ ns₁ (tell $ loc String.++ ": overlfow (1st)")

    DD : {@0 bs₁ : List Σ} → @0 List Σ → Set
    DD {bs'} = ExactLength (&ₚ (Option B) (&ₚ (Option C) (Option D))) (n - length bs')

    p₂₃₄' : ∀ {@0 bs₁ : List Σ} → Singleton (length bs₁) → Parser (Logging ∘ Dec) (DD{bs₁})
    p₂₃₄' {bs₁} (singleton r r≡) =
      subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option B) (&ₚ (Option C) (Option D))) (n - x)))
        {r}{length bs₁}
        r≡
        (parse₂Option₃ (loc String.++ " (2nd,3rd,4th)") ns₂ ns₃ ns₄ nc₂₃ nc₂₄ nc₃₄ p₂ p₃ p₄ (n - r))

    p : Parser (Logging ∘ Dec) (&ₚᵈ (Length≤ (Option A) n) λ {bs₁} _ → DD{bs₁})
    runParser p xs = do
      (yes (success pre₁ r₁ r₁≡ v₁@(mk×ₚ a₁ aLen) suf₁ ps≡₁)) ← runParser p₁' xs
        where no ¬p₁ → do
          (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) ← runParser (parse₂Option₃ (loc String.++ " (2nd,3rd,4th)") ns₂ ns₃ ns₄ nc₂₃ nc₂₄ nc₃₄ p₂ p₃ p₄ n) xs
            where no ¬op₂₃₄ → do
              tell $ loc String.++ ": failed to parse"
              return ∘ no $ λ where
                (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a) aLen) oaob refl) suffix ps≡) →
                  contradiction
                    (success bs₁ _ refl (mk×ₚ a aLen) (bs₂ ++ suffix)
                      (begin
                        bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs ∎))
                    ¬p₁
                (success prefix read read≡ (mk&ₚ{bs₂ = bs₂} (mk×ₚ none _) oaob refl) suffix ps≡) →
                  contradiction
                    (success prefix _ read≡ oaob suffix ps≡)
                    ¬op₂₃₄
          return (yes
            (success _ _ r₁≡ (mk&ₚ (mk×ₚ none (─ z≤n)) v₁ refl) suf₁ ps≡₁))
      (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) ← runParser (p₂₃₄'{pre₁} (singleton r₁ r₁≡)) suf₁
        where no ¬op₂₃₄ → do
          tell $ loc String.++ ": failed to parse"
          return ∘ no $ λ where
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ {bs₁}{bs₂} (some b') _ refl) obocodLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                b'
                (nc₁₂ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ {bs₁}{bs₂} (some c') _ refl) refl) obocodLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                c'
                (nc₁₃ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none (some d') refl) refl) obocodLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ prefix ++ suffix
                ++≡ = trans ps≡₁ (sym ps≡)
              in
              contradiction
                d'
                (nc₁₄ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none none refl) refl) (─ ())) refl) .xs refl)
            (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a') oaLen) oaob' bs≡) suffix ps≡) →
              let
                @0 ++≡ : bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁
                ++≡ = begin
                  bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
                  prefix ++ suffix ≡⟨ ps≡ ⟩
                  xs ≡⟨ sym ps≡₁ ⟩
                  pre₁ ++ suf₁ ∎

                @0 pre₁≡ : bs₁ ≡ pre₁
                pre₁≡ = ns₁ ++≡ a' a₁
              in
              contradiction
                (success bs₂ _ refl (DD {pre₁} bs₂ ∋ subst₀ (λ x → DD {x} bs₂) pre₁≡ oaob')
                  suffix
                  (Lemmas.++-cancel≡ˡ _ _ pre₁≡ ++≡))
                ¬op₂₃₄
      return (yes
        (success (pre₁ ++ pre₂) (r₁ + r₂)
          (begin
            (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
            length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
            length (pre₁ ++ pre₂) ∎))
          (mk&ₚ (mk×ₚ (some a₁) aLen) v₂ refl) suf₂
            (begin
              (pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ pre₂ suf₂ ⟩
              pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
              pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
              xs ∎)))

  parse₂Option₅ : ∀ {A B C D E : @0 List Σ → Set} → String
      → @0 NoSubstrings A
      → @0 NoSubstrings B
      → @0 NoSubstrings C
      → @0 NoSubstrings D
      → @0 NoSubstrings E
      → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D → @0 NoConfusion A E
      → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion B E
      → @0 NoConfusion C D → @0 NoConfusion C E
      → @0 NoConfusion D E
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C → Parser (Logging ∘ Dec) D → Parser (Logging ∘ Dec) E
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option A) (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (Option E))))) n)
  runParser (parse₂Option₅ loc ns₁ ns₂ ns₃ ns₄ ns₅ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₂₃ nc₂₄ nc₂₅ nc₃₄ nc₃₅ nc₄₅ p₁ p₂ p₃ p₄ p₅ 0) xs =
    return (yes
      (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ none (mk&ₚ none none refl) refl) refl) refl) (─ refl)) xs refl))
  parse₂Option₅{A}{B}{C}{D}{E} loc ns₁ ns₂ ns₃ ns₄ ns₅ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₂₃ nc₂₄ nc₂₅ nc₃₄ nc₃₅ nc₄₅ p₁ p₂ p₃ p₄ p₅ n@(suc _) =
    parseEquivalent (ExactLength.equivalent{A = Option A}{B = (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (Option E))))}) p
    where
    open ≡-Reasoning

    p₁' : Parser (Logging ∘ Dec) (Length≤ A n)
    p₁' = parse≤ n p₁ ns₁ (tell $ loc String.++ ": overlfow (1st)")

    DD : {@0 bs₁ : List Σ} → @0 List Σ → Set
    DD {bs'} = ExactLength (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (Option E)))) (n - length bs')

    p₂₃₄₅' : ∀ {@0 bs₁ : List Σ} → Singleton (length bs₁) → Parser (Logging ∘ Dec) (DD{bs₁})
    p₂₃₄₅' {bs₁} (singleton r r≡) =
      subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (Option E)))) (n - x)))
        {r}{length bs₁}
        r≡
        (parse₂Option₄ (loc String.++ " (2nd,3rd,4th,5th)") ns₂ ns₃ ns₄ ns₅ nc₂₃ nc₂₄ nc₂₅ nc₃₄ nc₃₅ nc₄₅ p₂ p₃ p₄ p₅ (n - r))

    p : Parser (Logging ∘ Dec) (&ₚᵈ (Length≤ (Option A) n) λ {bs₁} _ → DD{bs₁})
    runParser p xs = do
      (yes (success pre₁ r₁ r₁≡ v₁@(mk×ₚ a₁ aLen) suf₁ ps≡₁)) ← runParser p₁' xs
        where no ¬p₁ → do
          (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) ← runParser (parse₂Option₄ (loc String.++ " (2nd,3rd,4th,5th)") ns₂ ns₃ ns₄ ns₅ nc₂₃ nc₂₄ nc₂₅ nc₃₄ nc₃₅ nc₄₅ p₂ p₃ p₄ p₅ n) xs
            where no ¬op₂₃₄₅ → do
              tell $ loc String.++ ": failed to parse"
              return ∘ no $ λ where
                (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a) aLen) oaob refl) suffix ps≡) →
                  contradiction
                    (success bs₁ _ refl (mk×ₚ a aLen) (bs₂ ++ suffix)
                      (begin
                        bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs ∎))
                    ¬p₁
                (success prefix read read≡ (mk&ₚ{bs₂ = bs₂} (mk×ₚ none _) oaob refl) suffix ps≡) →
                  contradiction
                    (success prefix _ read≡ oaob suffix ps≡)
                    ¬op₂₃₄₅
          return (yes
            (success _ _ r₁≡ (mk&ₚ (mk×ₚ none (─ z≤n)) v₁ refl) suf₁ ps≡₁))
      (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) ← runParser (p₂₃₄₅'{pre₁} (singleton r₁ r₁≡)) suf₁
        where no ¬op₂₃₄₅ → do
          tell $ loc String.++ ": failed to parse"
          return ∘ no $ λ where
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ {bs₁}{bs₂} (some b') _ refl) obocodoeLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                b'
                (nc₁₂ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ {bs₁}{bs₂} (some c') _ refl) refl) obocodoeLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                c'
                (nc₁₃ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ {bs₁}{bs₂} (some d') _ refl) refl) refl) obocodoeLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                d'
                (nc₁₄ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none  (mk&ₚ {bs₁}{bs₂} none (some e') refl) refl) refl) obocodoeLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ prefix ++ suffix
                ++≡ = trans ps≡₁ (sym ps≡)
              in
              contradiction
                e'
                (nc₁₅ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ none none refl) refl) refl) (─ ())) refl) .xs refl)
            (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a') oaLen) oaob' bs≡) suffix ps≡) →
              let
                @0 ++≡ : bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁
                ++≡ = begin
                  bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
                  prefix ++ suffix ≡⟨ ps≡ ⟩
                  xs ≡⟨ sym ps≡₁ ⟩
                  pre₁ ++ suf₁ ∎

                @0 pre₁≡ : bs₁ ≡ pre₁
                pre₁≡ = ns₁ ++≡ a' a₁
              in
              contradiction
                (success bs₂ _ refl (DD {pre₁} bs₂ ∋ subst₀ (λ x → DD {x} bs₂) pre₁≡ oaob')
                  suffix
                  (Lemmas.++-cancel≡ˡ _ _ pre₁≡ ++≡))
                ¬op₂₃₄₅
      return (yes
        (success (pre₁ ++ pre₂) (r₁ + r₂)
          (begin
            (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
            length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
            length (pre₁ ++ pre₂) ∎))
          (mk&ₚ (mk×ₚ (some a₁) aLen) v₂ refl) suf₂
            (begin
              (pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ pre₂ suf₂ ⟩
              pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
              pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
              xs ∎)))

  parse₂Option₆ : ∀ {A B C D E F : @0 List Σ → Set} → String
      → @0 NoSubstrings A
      → @0 NoSubstrings B
      → @0 NoSubstrings C
      → @0 NoSubstrings D
      → @0 NoSubstrings E
      → @0 NoSubstrings F
      → @0 NoConfusion A B → @0 NoConfusion A C → @0 NoConfusion A D → @0 NoConfusion A E → @0 NoConfusion A F
      → @0 NoConfusion B C → @0 NoConfusion B D → @0 NoConfusion B E → @0 NoConfusion B F
      → @0 NoConfusion C D → @0 NoConfusion C E → @0 NoConfusion C F
      → @0 NoConfusion D E → @0 NoConfusion D F
      → @0 NoConfusion E F
      → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B → Parser (Logging ∘ Dec) C → Parser (Logging ∘ Dec) D → Parser (Logging ∘ Dec) E → Parser (Logging ∘ Dec) F
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (&ₚ(Option A) (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F)))))) n)
  runParser (parse₂Option₆ loc ns₁ ns₂ ns₃ ns₄ ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ p₁ p₂ p₃ p₄ p₅ p₆ 0) xs =
    return (yes
      (success [] _ refl (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ none (mk&ₚ none (mk&ₚ none none refl) refl) refl) refl) refl) (─ refl)) xs refl))
  parse₂Option₆{A}{B}{C}{D}{E}{F} loc ns₁ ns₂ ns₃ ns₄ ns₅ ns₆ nc₁₂ nc₁₃ nc₁₄ nc₁₅ nc₁₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ p₁ p₂ p₃ p₄ p₅ p₆ n@(suc _) =
    parseEquivalent (ExactLength.equivalent{A = Option A}{B = (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F)))))}) p
    where
    open ≡-Reasoning

    p₁' : Parser (Logging ∘ Dec) (Length≤ A n)
    p₁' = parse≤ n p₁ ns₁ (tell $ loc String.++ ": overlfow (1st)")

    DD : {@0 bs₁ : List Σ} → @0 List Σ → Set
    DD {bs'} = ExactLength (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F))))) (n - length bs')

    p₂₃₄₅' : ∀ {@0 bs₁ : List Σ} → Singleton (length bs₁) → Parser (Logging ∘ Dec) (DD{bs₁})
    p₂₃₄₅' {bs₁} (singleton r r≡) =
      subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option B) (&ₚ(Option C) (&ₚ (Option D) (&ₚ (Option E) (Option F))))) (n - x)))
        {r}{length bs₁}
        r≡
        (parse₂Option₅ (loc String.++ " (2nd,3rd,4th,5th,6th)") ns₂ ns₃ ns₄ ns₅ ns₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ p₂ p₃ p₄ p₅ p₆ (n - r))

    p : Parser (Logging ∘ Dec) (&ₚᵈ (Length≤ (Option A) n) λ {bs₁} _ → DD{bs₁})
    runParser p xs = do
      (yes (success pre₁ r₁ r₁≡ v₁@(mk×ₚ a₁ aLen) suf₁ ps≡₁)) ← runParser p₁' xs
        where no ¬p₁ → do
          (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) ← runParser (parse₂Option₅ (loc String.++ " (2nd,3rd,4th,5th,6th)") ns₂ ns₃ ns₄ ns₅ ns₆ nc₂₃ nc₂₄ nc₂₅ nc₂₆ nc₃₄ nc₃₅ nc₃₆ nc₄₅ nc₄₆ nc₅₆ p₂ p₃ p₄ p₅ p₆ n) xs
            where no ¬op₂₃₄₅₆ → do
              tell $ loc String.++ ": failed to parse"
              return ∘ no $ λ where
                (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a) aLen) oaob refl) suffix ps≡) →
                  contradiction
                    (success bs₁ _ refl (mk×ₚ a aLen) (bs₂ ++ suffix)
                      (begin
                        bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                        (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                        xs ∎))
                    ¬p₁
                (success prefix read read≡ (mk&ₚ{bs₂ = bs₂} (mk×ₚ none _) oaob refl) suffix ps≡) →
                  contradiction
                    (success prefix _ read≡ oaob suffix ps≡)
                    ¬op₂₃₄₅₆
          return (yes
            (success _ _ r₁≡ (mk&ₚ (mk×ₚ none (─ z≤n)) v₁ refl) suf₁ ps≡₁))
      (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) ← runParser (p₂₃₄₅'{pre₁} (singleton r₁ r₁≡)) suf₁
        where no ¬op₂₃₄₅₆ → do
          tell $ loc String.++ ": failed to parse"
          return ∘ no $ λ where
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ {bs₁}{bs₂} (some b') _ refl) obocodoeofLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                b'
                (nc₁₂ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ {bs₁}{bs₂} (some c') _ refl) refl) obocodoeofLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                c'
                (nc₁₃ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ {bs₁}{bs₂} (some d') _ refl) refl) refl) obocodoeofLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                d'
                (nc₁₄ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ none (mk&ₚ {bs₁}{bs₂} (some e') _ refl) refl) refl) refl) obocodoeofLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ bs₁ ++ bs₂ ++ suffix
                ++≡ = begin
                  pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
                  xs ≡⟨ sym ps≡ ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ ++-assoc bs₁ bs₂ suffix ⟩
                  bs₁ ++ bs₂ ++ suffix ∎
              in
              contradiction
                e'
                (nc₁₅ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ none (mk&ₚ {bs₁}{bs₂} none (some f') refl) refl) refl) refl) obocodoeofLen) refl) suffix ps≡) →
              let
                @0 ++≡ : pre₁ ++ suf₁ ≡ prefix ++ suffix
                ++≡ = trans ps≡₁ (sym ps≡)
              in
              contradiction
                f'
                (nc₁₆ ++≡ a₁)
            (success prefix read read≡ (mk&ₚ (mk×ₚ none oaLen) (mk×ₚ (mk&ₚ none (mk&ₚ none (mk&ₚ none (mk&ₚ none none refl) refl) refl) refl) (─ ())) refl) .xs refl)
            (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} (mk×ₚ (some a') oaLen) oaob' bs≡) suffix ps≡) →
              let
                @0 ++≡ : bs₁ ++ bs₂ ++ suffix ≡ pre₁ ++ suf₁
                ++≡ = begin
                  bs₁ ++ bs₂ ++ suffix ≡⟨ sym (++-assoc bs₁ bs₂ suffix) ⟩
                  (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
                  prefix ++ suffix ≡⟨ ps≡ ⟩
                  xs ≡⟨ sym ps≡₁ ⟩
                  pre₁ ++ suf₁ ∎

                @0 pre₁≡ : bs₁ ≡ pre₁
                pre₁≡ = ns₁ ++≡ a' a₁
              in
              contradiction
                (success bs₂ _ refl (DD {pre₁} bs₂ ∋ subst₀ (λ x → DD {x} bs₂) pre₁≡ oaob')
                  suffix
                  (Lemmas.++-cancel≡ˡ _ _ pre₁≡ ++≡))
                ¬op₂₃₄₅₆
      return (yes
        (success (pre₁ ++ pre₂) (r₁ + r₂)
          (begin
            (r₁ + r₂ ≡⟨ cong₂ _+_ r₁≡ r₂≡ ⟩
            length pre₁ + length pre₂ ≡⟨ sym (length-++ pre₁) ⟩
            length (pre₁ ++ pre₂) ∎))
          (mk&ₚ (mk×ₚ (some a₁) aLen) v₂ refl) suf₂
            (begin
              (pre₁ ++ pre₂) ++ suf₂ ≡⟨ ++-assoc pre₁ pre₂ suf₂ ⟩
              pre₁ ++ pre₂ ++ suf₂ ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
              pre₁ ++ suf₁ ≡⟨ ps≡₁ ⟩
              xs ∎)))
