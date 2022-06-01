{-# OPTIONS --subtyping #-}

open import Aeres.Binary renaming (module Base64 to B64)
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude
import      Aeres.Data.Base64.TCB as Base64

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Sum         Char

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

module Base64Str where
  Rep : @0 List Char → Set
  Rep = (&ₚ (IList Base64.Base64Char) Base64.Pad) ×ₚ λ bs → length bs % 4 ≡ 0

  equiv : Equivalent Rep Base64.Base64Str
  proj₁ equiv (mk×ₚ (mk&ₚ{bs₁}{bs₂} cs p refl) %4 refl) =
    Base64.mk64Str bs₁ bs₂ cs p %4 refl
  proj₂ equiv (Base64.mk64Str s p str pad mult refl) =
    mk×ₚ (mk&ₚ str pad refl) (‼ mult) refl

  dec : Decidable Base64.Base64Str
  dec bs =
    case length bs % 4 ≟ 0 of λ where
      (no ¬%4) → no λ where
        (Base64.mk64Str s p str pad mult bs≡) →
          contradiction mult
            (subst (λ x → ¬ length x % 4 ≡ 0) bs≡ ¬%4)
      (yes %4) → helper bs %4
    where
    helper : ∀ bs → @0 length bs % 4 ≡ 0 → Dec (Base64.Base64Str bs)
    helper [] %4 =
      yes (Base64.mk64Str [] [] nil Base64.pad0 refl refl)
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs) %4
      with helper bs %4
    ... | no ¬p =
      no λ where
        (Base64.mk64Str .[] .[] nil Base64.pad0 mult ())
        (Base64.mk64Str .[] ._ nil Base64.pad1 mult ())
        (Base64.mk64Str .[] ._ nil Base64.pad2 mult ())
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c∈ i refl) nil refl)) () mult refl)
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c∈₁ i₁ refl) nil refl)) refl)) Base64.pad2 refl refl) →
          contradiction (Base64.mk64Str [] [] nil Base64.pad0 refl refl) ¬p
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c∈₁ i₁ refl) (cons (mkIListCons (Base64.mk64 .c₃ c∈₂ i₂ refl) nil refl)) refl)) refl)) Base64.pad1 refl refl) →
          contradiction (Base64.mk64Str [] [] nil Base64.pad0 refl refl) ¬p
        (Base64.mk64Str ._ p (cons (mkIListCons (Base64.mk64 c c∈ i refl) (cons (mkIListCons (Base64.mk64 c₁ c∈₁ i₁ refl) (cons (mkIListCons (Base64.mk64 c₂ c∈₂ i₂ refl) (cons (mkIListCons{bs₂ = bs₂} (Base64.mk64 c₃ c∈₃ i₃ refl) tail₁ refl)) refl)) refl)) refl)) pad mult bs≡) → ‼
          let @0 bs≡' : bs ≡ bs₂ ++ p
              bs≡' = proj₂ (Lemmas.length-++-≡ _ _ (_ ∷ _ ∷ _ ∷ _ ∷ []) _ bs≡ refl)
          in
          contradiction
            (Base64.mk64Str bs₂ p tail₁ pad mult bs≡')
            ¬p
    ... | yes (Base64.mk64Str .[] .[] nil Base64.pad0 refl refl)
      with c₁ ∈? B64.charset
      |    c₂ ∈? B64.charset
    ... | no ¬p | _ =
      no λ where
        (Base64.mk64Str .[] .[] nil Base64.pad0 mult ())
        (Base64.mk64Str .[] ._ nil Base64.pad1 mult ())
        (Base64.mk64Str .[] ._ nil Base64.pad2 mult ())
        (Base64.mk64Str ._ p (cons (mkIListCons (Base64.mk64 c c∈ i refl) tail₁ refl)) pad mult bs≡) →
          contradiction c∈ (subst (λ x → ¬ x ∈ B64.charset) (∷-injectiveˡ bs≡) ¬p)
    ... | yes _ | no ¬p =
      no λ where
        (Base64.mk64Str .[] .[] nil Base64.pad0 mult ())
        (Base64.mk64Str .[] ._ nil Base64.pad1 mult ())
        (Base64.mk64Str .[] ._ nil Base64.pad2 mult ())
        (Base64.mk64Str ._ .[] (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad0 mult ())
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad1 mult ())
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad2 mult ())
        (Base64.mk64Str s p (cons (mkIListCons (Base64.mk64 c c∈ i refl) (cons (mkIListCons (Base64.mk64 c' c∈' i' refl) tail refl)) refl)) pad mult bs≡) →
          contradiction c∈' (subst (λ x → ¬ x ∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ bs≡)) ¬p)
    ... | yes c₁∈ | yes c₂∈
      with c₃ ∈? B64.charset
    ... | no ¬c₃∈ =
      case (c₃ ≟ '=') ,′ (c₄ ≟ '=') of λ where
        (no ¬p , _) →
          no λ where
            (Base64.mk64Str .[] .[] nil Base64.pad0 mult ())
            (Base64.mk64Str .[] ._ nil Base64.pad1 () bs≡)
            (Base64.mk64Str .[] ._ nil Base64.pad2 () bs≡)
            (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad0 () bs≡)
            (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad1 () bs≡)
            (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad2 () bs≡)
            (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c∈₁ i₁ refl) nil refl)) refl)) Base64.pad2 refl refl) →
              contradiction refl ¬p
            (Base64.mk64Str .([ c ] ++ [ c₁ ] ++ [ c₂ ] ++ _) p (cons (mkIListCons (Base64.mk64 c c∈ i refl) (cons (mkIListCons (Base64.mk64 c₁ c∈₁ i₁ refl) (cons (mkIListCons (Base64.mk64 c₂ c∈₂ i₂ refl) tail₁ refl)) refl)) refl)) pad mult bs≡) →
              contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡)))) c∈₂) ¬c₃∈
        (yes refl , no ¬p) →
          no λ where
            (Base64.mk64Str .[] .[] Aeres.Grammar.IList.nil Base64.pad0 mult ())
            (Base64.mk64Str .[] .(String.toList "=") Aeres.Grammar.IList.nil Base64.pad1 () bs≡)
            (Base64.mk64Str .[] .(String.toList "==") Aeres.Grammar.IList.nil Base64.pad2 () bs≡)
            (Base64.mk64Str .([ c ] ++ []) .[] (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 c c∈ i refl) Aeres.Grammar.IList.nil refl)) Base64.pad0 () bs≡)
            (Base64.mk64Str .([ c ] ++ []) .(String.toList "=") (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 c c∈ i refl) Aeres.Grammar.IList.nil refl)) Base64.pad1 mult ())
            (Base64.mk64Str .([ c ] ++ []) .(String.toList "==") (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 c c∈ i refl) Aeres.Grammar.IList.nil refl)) Base64.pad2 mult ())
            (Base64.mk64Str .([ c₁ ] ++ [ c₂ ] ++ []) .(String.toList "==") (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 .c₁ c∈ i refl) (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 .c₂ c∈₁ i₁ refl) Aeres.Grammar.IList.nil refl)) refl)) Base64.pad2 refl refl) →
              contradiction refl ¬p
            (Base64.mk64Str .([ c₁ ] ++ [ c₂ ] ++ [ '=' ] ++ []) .(String.toList "=") (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 .c₁ c∈ i refl) (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 .c₂ c∈₁ i₁ refl) (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 .'=' c∈₂ i₂ refl) Aeres.Grammar.IList.nil refl)) refl)) refl)) Base64.pad1 mult refl) →
              contradiction refl ¬p
            (Base64.mk64Str ._ p (cons (mkIListCons (Base64.mk64 c c∈ i refl) (cons (mkIListCons (Base64.mk64 c₁ c∈₁ i₁ refl) (cons (mkIListCons (Base64.mk64 c₂ c∈₂ i₂ refl) (cons (mkIListCons (Base64.mk64 c₃ c∈₃ i₃ refl) tail₁ refl)) refl)) refl)) refl)) pad mult bs≡) →
              case (‼ proj₁ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ [ _ ]) (_ ++ p) (‼ bs≡) (erefl 4))) ret (λ _ → _) of λ where
                refl → contradiction c∈₂ ¬c₃∈
        (yes refl , yes refl) →
          yes (Base64.mk64Str (c₁ ∷ [ c₂ ]) _ (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 c₁ c₁∈ self refl) (Aeres.Grammar.IList.cons (Aeres.Grammar.IList.mkIListCons (Base64.mk64 c₂ c₂∈ self refl) nil refl)) refl)) Base64.pad2 refl refl)
    ... | yes c₃∈
      with c₄ ∈? B64.charset
    ... | yes c₄∈ = {!!}
    ... | no ¬c₄∈
      with c₄ ≟ '='
    ... | yes refl = {!!}
    ... | no ¬c₄≡= = {!!}
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs) %4 | yes (Base64.mk64Str ._ .[] str@(cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad0 () bs≡)
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs) %4 | yes (Base64.mk64Str ._ ._ str@(cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad1 () bs≡)
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs) %4 | yes (Base64.mk64Str ._ ._ str@(cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad2 () bs≡)
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs) %4 | yes (Base64.mk64Str s@._ p str@(cons (mkIListCons (Base64.mk64 c₅ c₅∈ i₅ refl) (cons (mkIListCons (Base64.mk64 c₆ c₆∈ i₆ refl) tail₁ refl)) refl)) pad mult bs≡)
      with All.all? (_∈? B64.charset) (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ])
    ... | no ¬p =
      no λ where
        (Base64.mk64Str .[] .(c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs) nil () mult refl)
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c∈ i refl) nil refl)) () mult refl)
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c₁∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c₂∈ i₁ refl) nil refl)) refl)) Base64.pad2 refl refl) →
          contradiction bs≡ (λ ())
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c∈₁ i₁ refl) (cons (mkIListCons (Base64.mk64 .c₃ c∈₂ i₂ refl) nil refl)) refl)) refl)) Base64.pad1 refl refl) →
          contradiction bs≡ λ ()
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c∈₁ i₁ refl) (cons (mkIListCons (Base64.mk64 .c₃ c∈₂ i₂ refl) nil refl)) refl)) refl)) Base64.pad2 mult' refl) →
          contradiction bs≡ λ ()
        (Base64.mk64Str ._ .[] (cons (mkIListCons (Base64.mk64 .c₁ c₁∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c₂∈ i₁ refl) (cons (mkIListCons (Base64.mk64 .c₃ c₃∈ i₂ refl) (cons (mkIListCons (Base64.mk64 .c₄ c₄∈ i₃ refl) nil refl)) refl)) refl)) refl)) Base64.pad0 refl refl) →
          contradiction bs≡ λ ()
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c₁∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c₂∈ i₁ refl) (cons (mkIListCons (Base64.mk64 .c₃ c₃∈ i₂ refl) (cons (mkIListCons (Base64.mk64 .c₄ c₄∈ i₃ refl) nil refl)) refl)) refl)) refl)) Base64.pad1 () refl)
        (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 .c₁ c₁∈ i refl) (cons (mkIListCons (Base64.mk64 .c₂ c₂∈ i₁ refl) (cons (mkIListCons (Base64.mk64 .c₃ c₃∈ i₂ refl) (cons (mkIListCons (Base64.mk64 .c₄ c₄∈ i₃ refl) nil refl)) refl)) refl)) refl)) Base64.pad2 () refl)
        (Base64.mk64Str ._ p' (cons (mkIListCons (Base64.mk64 c c∈ i refl) (cons (mkIListCons (Base64.mk64 c₁ c₁∈ i₁ refl) (cons (mkIListCons (Base64.mk64 c₂ c₂∈ i₂ refl) (cons (mkIListCons (Base64.mk64 c₃ c₃∈ i₃ refl) (cons (mkIListCons (Base64.mk64 c₄ c₄∈ i₄ refl) _ refl)) refl)) refl)) refl)) refl)) pad' mult' bs≡) →
          contradiction
            (subst (All (_∈ B64.charset)) (proj₁ $ Lemmas.length-++-≡ _ (c₄ ∷ _ ++ p') _ bs (sym bs≡) (erefl 4)) (c∈ All.∷ c₁∈ All.∷ (c₂∈ All.∷ (c₃∈ All.∷ All.[]))))
            ¬p
    ... | yes p₁ =
      yes (Base64.mk64Str (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ s) p
             (appendIList (Base64Char.all2IList p₁) str) pad
             mult (cong ((c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) ++_) bs≡))

    --   with c₁ ∈? B64.charset
    --   |    c₂ ∈? B64.charset
    -- ... | no ¬p | _ =
    --   no λ where
    --     (Base64.mk64Str .[] .[] nil Base64.pad0 mult ())
    --     (Base64.mk64Str .[] ._ nil Base64.pad1 mult ())
    --     (Base64.mk64Str .[] ._ nil Base64.pad2 mult ())
    --     (Base64.mk64Str ._ p (cons (mkIListCons (Base64.mk64 c c∈ i refl) tail₁ refl)) pad mult bs≡) →
    --       contradiction c∈ (subst (λ x → ¬ x ∈ B64.charset) (∷-injectiveˡ bs≡) ¬p)
    -- ... | yes _ | no ¬p = no λ where
    --   (Base64.mk64Str .[] .[] nil Base64.pad0 mult ())
    --   (Base64.mk64Str .[] ._ nil Base64.pad1 mult ())
    --   (Base64.mk64Str .[] ._ nil Base64.pad2 mult ())
    --   (Base64.mk64Str ._ .[] (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad0 mult ())
    --   (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad1 mult ())
    --   (Base64.mk64Str ._ ._ (cons (mkIListCons (Base64.mk64 c c∈ i refl) nil refl)) Base64.pad2 mult ())
    --   (Base64.mk64Str s p (cons (mkIListCons (Base64.mk64 c c∈ i refl) (cons (mkIListCons (Base64.mk64 c' c∈' i' refl) tail refl)) refl)) pad mult bs≡) →
    --     contradiction c∈' (subst (λ x → ¬ x ∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ bs≡)) ¬p)
    -- ... | yes p | yes p₁ = {!!}
    -- helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs'@(_ ∷ _)) %4
    --   with All.all? (_∈? B64.charset) (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ])
    -- ... | no ¬p = {!!}
    -- ... | yes p
    --   with helper bs' (begin
    --          (4 + length bs') % 4 ≡⟨ {!!} ⟩
    --          {!!})
    --   where open ≡-Reasoning
    -- ... | xxx = {!!}
