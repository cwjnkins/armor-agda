{-# OPTIONS --subtyping #-}

open import Aeres.Binary renaming (module Base64 to B64)
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude
import      Aeres.Data.Base64.TCB as Base64
import      Data.Nat.DivMod       as Nat
import      Data.Nat.Properties   as Nat

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Sum         Char
open ≡-Reasoning

module Aeres.Data.Base64.Properties where

module Base64Char where
  Rep : @0 List Char → Set
  Rep =
    Σₚ (Erased ∘ (ExactLengthString 1))
       λ where
         ._ (─ xs) →
           let @0 c : Char
               c = lookupELS xs (# 0)
           in Exists─ (c ∈ B64.charset) (λ c∈ → Singleton (Any.index c∈))

  equiv : Equivalent Rep Base64.Base64Char
  proj₁ equiv {xs“} (mk×ₚ (─ xs'@(mk×ₚ self (─ xsLen) refl)) (─ c∈ , i) refl) =
    Base64.mk64 (lookupELS xs' (# 0)) c∈ i (‼ lem xsLen)
    where
    @0 lem : ∀ {xs“} (xsLen : length xs“ ≡ 1)
             → xs“ ≡ [ lookupELS (mk×ₚ (singleton xs“ refl) (─ xsLen) refl) (# 0) ]
    lem {x ∷ []} refl = refl
  proj₂ equiv (Base64.mk64 c c∈ i refl) =
    mk×ₚ (─ (mk×ₚ (singleton (c ∷ []) refl) (─ refl) refl)) ((─ c∈) , i) refl

  all2IList : ∀ {bs} → All (_∈ B64.charset) bs → IList Base64.Base64Char bs
  all2IList All.[] = nil
  all2IList{c ∷ cs} (c∈ All.∷ a) =
    cons (mkIListCons (Base64.mk64 c c∈ self refl) (all2IList a) refl)

module Base64Pad where

  @0 p%4≡0 : ∀ {@0 p} → Base64.Base64Pad p → length p % 4 ≡ 0
  p%4≡0 (Base64.pad0 refl) = refl
  p%4≡0 (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) = refl
  p%4≡0 (Base64.pad2 (Base64.mk64P1 c₁ c₂ pad refl)) = refl

module Base64Str where
  -- Rep : @0 List Char → Set
  -- Rep = &ₚ ((IList Base64.Base64Char) ×ₚ ((_≡ 0) ∘ (_% 4) ∘ length)) Base64.Base64Pad

--   equiv : Equivalent Rep Base64.Base64Str
--   proj₁ equiv (mk×ₚ (mk&ₚ{bs₁}{bs₂} cs p refl) %4 refl) =
--     Base64.mk64Str bs₁ bs₂ cs p %4 refl
--   proj₂ equiv (Base64.mk64Str s p str pad mult refl) =
--     mk×ₚ (mk&ₚ str pad refl) (‼ mult) refl

   dec : Decidable Base64.Base64Str
   dec bs =
     case length bs % 4 ≟ 0 of λ where
       (no ¬≡0) →
         no λ where
           (Base64.mk64Str{s = s}{p} str strLen pad bs≡) →
             contradiction
               (subst ((_≡ 0) ∘ (_% 4) ∘ length) (sym bs≡)
                 (begin length (s ++ p) % 4               ≡⟨ cong (_% 4) (length-++ s) ⟩
                        (length s + length p) % 4         ≡⟨ Nat.%-distribˡ-+ (length s) _ 4 ⟩
                        (length s % 4 + length p % 4) % 4 ≡⟨ cong (λ x → (length s % 4 + x) % 4) (Base64Pad.p%4≡0 pad) ⟩
                        (length s % 4 + 0) % 4            ≡⟨ cong (_% 4) (Nat.+-identityʳ (length s % 4)) ⟩
                        (length s % 4) % 4                ≡⟨ m%n%n≡m%n (length s) _ ⟩
                        length s % 4                      ≡⟨ strLen ⟩
                        0                                 ∎))
               ¬≡0
       (yes ≡0) → helper bs ≡0
     where
     helper : ∀ bs → @0 length bs % 4 ≡ 0 → Dec (Base64.Base64Str bs)
     helper [] %4 = yes (Base64.mk64Str nil refl (Base64.pad0 refl) refl)
     helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ []) refl
       with c₁ ∈? B64.charset
       |    c₂ ∈? B64.charset
     ... | no c₁∉ | _ =
       no λ where
         (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
         (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) c₂' c₃' pad refl)) refl) →
           contradiction c∈ c₁∉
         (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) c₂ pad refl)) refl) →
           contradiction c∈ c₁∉
         (Base64.mk64Str (cons (mkIListCons (Base64.mk64 c c∈ i refl) tail₁ refl)) strLen pad bs≡) →
           contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (sym bs≡)) c∈) c₁∉
     ... | yes _  | no c₂∉ =
       no λ where
         (Base64.mk64Str nil strLen (Base64.pad0 ()) refl)
         (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 _ _ _ refl) (Base64.mk64 c₂' c₂∈' i₂' refl) c₃ pad refl)) bs≡) →
           contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (sym bs≡))) c₂∈') c₂∉
         (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P1 (Base64.mk64 ._ _ _ refl) (Base64.mk64 .c₂ c₂∈' i₁ refl) pad refl)) refl) →
           contradiction c₂∈' c₂∉
         (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₂' c₂∈' _ refl) tail₁ refl) refl) strLen pad bs≡) →
           contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (sym bs≡))) c₂∈') c₂∉
     ... | yes c₁∈ | yes c₂∈
       with c₃ ∈? B64.charset
     ... | no ¬c₃∈ =
       case (c₃ ≟ '=') ,′ (c₄ ≟ '=') of λ where
         (no ¬c₃≡= , _) →
           no λ where
             (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
             (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c₁∈' _ refl) (Base64.mk64 .c₂ c₂∈' _ refl) (Base64.mk64 .c₃ c₃∈' _ refl) pad refl)) refl) →
               contradiction c₃∈' ¬c₃∈
             (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
               contradiction (erefl '=') ¬c₃≡=
             (Base64.mk64Str (consIList (Base64.mk64 c₁' _ _ refl) (consIList (Base64.mk64 c₂' _ _ refl) (consIList (Base64.mk64 c₃' c₃'∈ _ refl) _ refl) refl) refl) strLen pad bs≡) →
               contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡)))) c₃'∈) ¬c₃∈
         (yes refl , no ¬c₄≡=) →
           no λ where
             (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
             (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .'=' c∈₂ i₂ refl) pad refl)) refl) →
               contradiction (erefl '=') ¬c₄≡=
             (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
               contradiction (erefl '=') ¬c₄≡=
             (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₃' c₃∈' _ refl) (consIList (Base64.mk64 c₄' c₄∈' _ refl) _ refl) refl) refl) refl) strLen pad bs≡) →
               contradiction c₃∈' (subst (¬_ ∘ (_∈ B64.charset)) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡))) (toWitnessFalse {Q = _ ∈? _} tt))
         (yes refl , yes refl) →
           let i = Any.index c₂∈ in
           case toℕ i % (2 ^ 4) ≟ 0 of λ where
             (no ¬c₂0s) →
               no λ where
                 (Base64.mk64Str Aeres.Grammar.IList.nil strLen (Base64.pad0 refl) ())
                 (Base64.mk64Str Aeres.Grammar.IList.nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .'=' c₃∈' _ refl) pad refl)) refl) →
                   contradiction c₃∈' (toWitnessFalse{Q = _ ∈? _} tt)
                 (Base64.mk64Str Aeres.Grammar.IList.nil strLen (Base64.pad2 (Base64.mk64P1 (Base64.mk64 .c₁ _ _ refl) (Base64.mk64 .c₂ c₂∈' (singleton i' i≡') refl) pad refl)) refl) →
                   contradiction
                     (begin toℕ (Any.index c₂∈)  % (2 ^ 4) ≡⟨ cong (λ x → toℕ (Any.index x) % (2 ^ 4)) (B64.∈charsetUnique c₂∈ c₂∈') ⟩
                            toℕ (Any.index c₂∈') % (2 ^ 4) ≡⟨ cong (λ x → toℕ x % (2 ^ 4)) (sym i≡') ⟩
                            toℕ i' % (2 ^ 4)               ≡⟨ pad ⟩
                            0 ∎)
                     ¬c₂0s
                 (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (cons (mkIListCons (Base64.mk64 c₃' c₃∈' _ refl) _ refl)) refl) refl) strLen pad bs≡) →
                   contradiction c₃∈' (subst (¬_ ∘ (_∈ B64.charset)) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡))) (toWitnessFalse{Q = _ ∈? _} tt))
             (yes c₂0s) →
               yes (Base64.mk64Str nil refl (Base64.pad2 (Base64.mk64P1 (Base64.mk64 c₁ c₁∈ self refl) (Base64.mk64 c₂ c₂∈ self refl) c₂0s refl)) refl)
     ... | yes c₃∈
       with c₄ ∈? B64.charset
     ... | no ¬c₄∈ =
       case c₄ ≟ '=' of λ where
         (no ¬c₄≡=) →
           no λ where
             (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
             (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .c₃ c∈₂ i₂ refl) pad refl)) refl) →
               contradiction refl ¬c₄≡=
             (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
               contradiction refl ¬c₄≡=
             (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₄' c₄∈' _ refl) _ refl) refl) refl) refl) strLen pad bs≡) →
               contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡))))) c₄∈') ¬c₄∈
         (yes refl) →
           let i = Any.index c₃∈ in
           case toℕ i % (2 ^ 2) ≟ 0 of λ where
             (no ¬c₃0s) →
               no λ where
                 (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
                 (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 _ _ _ refl) (Base64.mk64 _ _ _ refl) (Base64.mk64 _ c₃∈' (singleton i' i≡') refl) pad refl)) refl) →
                   contradiction
                     (begin toℕ (Any.index c₃∈)  % (2 ^ 2) ≡⟨ cong (λ x → toℕ (Any.index x) % (2 ^ 2)) (B64.∈charsetUnique c₃∈ c₃∈') ⟩
                            toℕ (Any.index c₃∈') % (2 ^ 2) ≡⟨ cong (λ x → toℕ x % (2 ^ 2)) (sym i≡') ⟩
                            toℕ i' % (2 ^ 2) ≡⟨ pad ⟩
                            0 ∎)
                     ¬c₃0s
                 (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
                   contradiction c₃∈ (toWitnessFalse{Q = _ ∈? _} tt)
                 (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₄' c₄∈' _ refl) tail₁ refl) refl) refl) refl) strLen pad bs≡) →
                   contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡))))) c₄∈') ¬c₄∈
             (yes c₃0s) →
               yes (Base64.mk64Str nil refl (Base64.pad1 (Base64.mk64P1 (Base64.mk64 c₁ c₁∈ self refl) (Base64.mk64 c₂ c₂∈ self refl) (Base64.mk64 c₃ c₃∈ self refl) c₃0s refl)) refl)
     ... | yes c₄∈ =
       yes (Base64.mk64Str (consIList (Base64.mk64 c₁ c₁∈ self refl) (consIList (Base64.mk64 c₂ c₂∈ self refl) (consIList (Base64.mk64 c₃ c₃∈ self refl) (consIList (Base64.mk64 c₄ c₄∈ self refl) nil refl) refl) refl) refl) refl (Base64.pad0 refl) (sym (++-identityʳ _)))
     helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs@(_ ∷ _)) %4
       with helper bs %4
     ... | no ¬p =
       no λ where
         (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
         (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) ())
         (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P1 c₁ c₂ pad refl)) ())
         (Base64.mk64Str (consIList (Base64.mk64 c₁' c₁∈' i₁' refl) (consIList (Base64.mk64 c₂' c₂∈' i₂' refl) (consIList (Base64.mk64 c₃' c₃∈' i₃' refl) (consIList (Base64.mk64 c₄' c₄∈' i₄' refl) tail₁ refl) refl) refl) refl) strLen pad bs≡) →
           contradiction
             (Base64.mk64Str tail₁ strLen pad (proj₂ $ Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ [ _ ]) bs (_ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡ (erefl 4)))
             ¬p
     helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs@(_ ∷ _)) %4 | yes (Base64.mk64Str str₀ strLen₀ pad₀ bs≡₀)
       with All.all? (_∈? B64.charset) (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ])
     ... | no ¬all∈ =
       no λ where
         (Base64.mk64Str Aeres.Grammar.IList.nil strLen (Base64.pad0 refl) ())
         (Base64.mk64Str Aeres.Grammar.IList.nil strLen (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad ())) refl)
         (Base64.mk64Str Aeres.Grammar.IList.nil strLen (Base64.pad2 (Base64.mk64P1 c₁ c₂ pad refl)) ())
         (Base64.mk64Str (consIList (Base64.mk64 c₁' c₁∈' i₁' refl) (consIList (Base64.mk64 c₂' c₂∈' i₂' refl) (consIList (Base64.mk64 c₃' c₃∈' i₃' refl) (consIList (Base64.mk64 c₄' c₄∈' i₄' refl) tail₁ refl) refl) refl) refl) strLen pad bs≡) →
           contradiction
             (subst (All (_∈ B64.charset))
               (proj₁ $ Lemmas.length-++-≡ _ _ _ _ (sym bs≡) refl)
               (c₁∈' All.∷ c₂∈' All.∷ c₃∈' All.∷ c₄∈' All.∷ All.[]))
             ¬all∈
     ... | yes (c₁∈ All.∷ c₂∈ All.∷ c₃∈ All.∷ c₄∈ All.∷ All.[]) = yes $
       Base64.mk64Str
         (consIList (Base64.mk64 c₁ c₁∈ self refl)
           (consIList (Base64.mk64 c₂ c₂∈ self refl)
             (consIList (Base64.mk64 c₃ c₃∈ self refl)
               (consIList (Base64.mk64 c₄ c₄∈ self refl) str₀ refl) refl) refl) refl)
         strLen₀ pad₀
         (cong (λ x → c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ x) bs≡₀)