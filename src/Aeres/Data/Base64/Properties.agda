{-# OPTIONS --subtyping #-}

open import Aeres.Binary renaming (module Base64 to B64)
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
import      Aeres.Grammar.Relation.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
import      Aeres.Data.Base64.TCB as Base64
import      Data.Nat.DivMod       as Nat
import      Data.Nat.Properties   as Nat

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Option               Char
open Aeres.Grammar.Relation.Definitions Char
open Aeres.Grammar.Sum                  Char
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

  @0 iList2All : ∀ {@0 bs} → IList Base64.Base64Char bs → All (Base64.Base64Char ∘ [_]) bs
  iList2All nil = All.[]
  iList2All{bs = .(c ∷ bs₂)} (consIList{bs₂ = bs₂} (Base64.mk64 c c∈ i refl) tail₁ refl) =
    All._∷_ (Base64.mk64 c c∈ i refl) (iList2All{bs₂} tail₁)

  @0 nonnesting : NonNesting Base64.Base64Char
  nonnesting{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (Base64.mk64 c c∈ i bs≡) (Base64.mk64 c₁ c∈₁ i₁ bs≡₁) =
    begin xs₁ ≡⟨ bs≡ ⟩
          [ c ] ≡⟨ cong [_] c≡ ⟩
          [ c₁ ] ≡⟨ sym bs≡₁ ⟩
          xs₂ ∎
    where
    @0 c≡ : c ≡ c₁
    c≡ =
      ∷-injectiveˡ (begin [ c ] ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                          xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                          xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                          [ c₁ ] ++ ys₂ ∎)

  @0 nonempty : NonEmpty Base64.Base64Char
  nonempty () refl

  unambiguous : Unambiguous Base64.Base64Char
  unambiguous = ua
    where
    ua : ∀ {@0 xs} → (a₁ a₂ : Base64.Base64Char xs) → a₁ ≡ a₂
    ua (Base64.mk64 c c∈ i@(singleton x x≡) refl) (Base64.mk64 .c c∈₁ i₁@(singleton x₁ x₁≡) refl) =
      subst₀ (λ c∈' → ∀ i' → Base64.mk64 c c∈ i refl ≡ Base64.mk64 c c∈' i' refl)
        c∈≡
        (λ where
          (singleton x' x'≡) → ‼
            let @0 x≡x' : x ≡ x'
                x≡x' = trans₀ x≡ (sym x'≡)
            in
            subst₀
              (λ y →
                 ∀ (y≡ : y ≡ Any.index c∈) →
                 Base64.mk64 _ _ (singleton x x≡) _ ≡
                 Base64.mk64 _ _ (singleton y y≡) _)
              x≡x'
              (λ y≡ →
                subst₀ (λ y≡ → _ ≡ Base64.mk64 c c∈ (singleton x y≡) refl)
                  (≡-unique x≡ _) refl)
              x'≡)
        i₁
      where
      @0 c∈≡ : c∈ ≡ c∈₁
      c∈≡ = ∈-unique (toWitness{Q = unique? _} tt) c∈ c∈₁

module Base64Pad where
  Rep₁ : @0 List Char → Set
  Rep₁ =  &ₚ (&ₚ Base64.Base64Char Base64.Base64Char)
         (&ₚ (Σₚ Base64.Base64Char (λ xs c → toℕ (↑ Base64.Base64Char.i c) % 2 ^ 2 ≡ 0))
             (_≡ [ '=' ]))
  
  equiv₁ : Equivalent Rep₁ Base64.Base64Pad1
  proj₁ equiv₁ (mk&ₚ (mk&ₚ (Base64.mk64 c c∈ i refl) (Base64.mk64 c₁ c∈₁ i₁ refl) refl) (mk&ₚ (mk×ₚ (Base64.mk64 c₂ c∈₂ i₂ refl) sndₚ₃ refl) refl refl) refl) = Base64.mk64P1 (Base64.mk64 c c∈ i refl) (Base64.mk64 c₁ c∈₁ i₁ refl) (Base64.mk64 c₂ c∈₂ i₂ refl) sndₚ₃ refl
  proj₂ equiv₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl) = mk&ₚ (mk&ₚ c₁ c₂ refl) (mk&ₚ (mk×ₚ c₃ (‼ pad) refl) refl refl) refl

  Rep₂ : @0 List Char → Set
  Rep₂ =  &ₚ Base64.Base64Char
         (&ₚ (Σₚ Base64.Base64Char (λ xs c → toℕ (↑ Base64.Base64Char.i c) % 2 ^ 4 ≡ 0))
             (_≡ '=' ∷ [ '=' ]))

  equiv₂ : Equivalent Rep₂ Base64.Base64Pad2
  proj₁ equiv₂ (mk&ₚ (Base64.mk64 c c∈ i refl) (mk&ₚ (mk×ₚ (Base64.mk64 c₁ c∈₁ i₁ refl) sndₚ₂ refl) refl refl) refl) = Base64.mk64P2 (Base64.mk64 c c∈ i refl) (Base64.mk64 c₁ c∈₁ i₁ refl) sndₚ₂ refl
  proj₂ equiv₂ (Base64.mk64P2 c₁ c₂ pad refl) = mk&ₚ c₁ (mk&ₚ (mk×ₚ c₂ (‼ pad) refl) refl refl) refl

  Rep : @0 List Char → Set
  Rep = Option (Sum Base64.Base64Pad1 Base64.Base64Pad2)

  equiv : Equivalent Rep Base64.Base64Pad
  proj₁ equiv none = Base64.pad0 refl
  proj₁ equiv (some (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl))) = Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)
  proj₁ equiv (some (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl))) = Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)
  proj₂ equiv (Base64.pad0 refl) = none
  proj₂ equiv (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) = some (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl))
  proj₂ equiv (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) = some (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl))

  @0 p%4≡0 : ∀ {@0 p} → Base64.Base64Pad p → length p % 4 ≡ 0
  p%4≡0 (Base64.pad0 refl) = refl
  p%4≡0 (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad refl)) = refl
  p%4≡0 (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) = refl

  forcebs : ∀ {@0 xs₁ bs₁ ys₁ xs₂ ys₂ c₁ c₂ c₃ c₄}
            → Sum Base64.Base64Pad1 Base64.Base64Pad2 xs₂
            → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
            → xs₁ ≡ c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₁
            → xs₂ ≡ c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]
  forcebs{bs₁ = bs₁}{ys₁} (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl)) ++≡ refl = ‼ proj₁ (Lemmas.length-++-≡ _ _ _ (bs₁ ++ ys₁) (sym ++≡) refl)
  forcebs (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl)) ++≡ refl = ‼ proj₁ (Lemmas.length-++-≡ _ _ _ _ (sym ++≡) refl)

  nonempty : NonEmpty (Sum Base64.Base64Pad1 Base64.Base64Pad2)
  nonempty (Sum.inj₁ ()) refl
  nonempty (Sum.inj₂ ()) refl

  c₄∉ : ∀ {@0 c₁ c₂ c₃ c₄} → Sum Base64.Base64Pad1 Base64.Base64Pad2 (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) → c₄ ∉ B64.charset
  c₄∉ (Sum.inj₁ (Base64.mk64P1 c₁ c₂ c₃ pad refl)) = toWitnessFalse {Q = _ ∈? _} tt
  c₄∉ (Sum.inj₂ (Base64.mk64P2 c₁ c₂ pad refl)) = toWitnessFalse{Q = _ ∈? _} tt

module Base64Str where
  Rep : @0 List Char → Set
  Rep = &ₚ (IList (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char Base64.Base64Char)))) Base64Pad.Rep

  Repₛ : @0 List Char → Set
  Repₛ = IList (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char (&ₚ Base64.Base64Char Base64.Base64Char)))

  {-# TERMINATING #-}
  equivₛ : Equivalent Repₛ ((IList Base64.Base64Char) ×ₚ ((_≡ 0) ∘ (_% 4) ∘ length))
  proj₁ equivₛ nil = mk×ₚ nil refl refl
  proj₁ equivₛ (consIList{bs₂ = bsₜ} (mk&ₚ fstₚ₁@(Base64.mk64 _ _ _ refl) (mk&ₚ fstₚ₂@(Base64.mk64 _ _ _ refl) (mk&ₚ fstₚ₃@(Base64.mk64 _ _ _ refl) sndₚ₂@(Base64.mk64 _ _ _ refl) refl) refl) refl) tail₁ refl) =
    case tail' of λ where
      (mk×ₚ{bs} fstₚ₁' sndₚ₁' bs≡') →
        mk×ₚ (consIList fstₚ₁ (consIList fstₚ₂ (consIList fstₚ₃ (consIList sndₚ₂ fstₚ₁' refl) refl) refl) refl) sndₚ₁' (‼ cong (λ x → _ ∷ _ ∷ _ ∷ _ ∷ x) bs≡')
    where
    tail' : ((IList Base64.Base64Char) ×ₚ ((_≡ 0) ∘ (_% 4) ∘ length)) bsₜ
    tail' = proj₁ equivₛ tail₁
  proj₂ equivₛ (mk×ₚ nil sndₚ₁ refl) = nil
  proj₂ equivₛ (mk×ₚ (consIList fstₚ₁@(Base64.mk64 _ _ _ refl) (consIList fstₚ₂@(Base64.mk64 _ _ _ refl) (consIList fstₚ₃@(Base64.mk64 _ _ _ refl) (consIList{bs₂ = bs₂} fstₚ₄@(Base64.mk64 _ _ _ refl) tail₁ refl) refl) refl) refl) sndₚ₁ bs≡) =
    consIList (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ fstₚ₄ refl) refl) refl) tail' (sym bs≡)
    where
    tail' : Repₛ bs₂
    tail' = proj₂ equivₛ (mk×ₚ tail₁ sndₚ₁ refl)

  equiv : Equivalent Rep Base64.Base64Str
  proj₁ equiv{xs} (mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₁ bs≡) =
    Base64.mk64Str (fstₚ l) (sndₚ l) (proj₁ Base64Pad.equiv sndₚ₁)
      (begin xs ≡⟨ bs≡ ⟩
             bs₁ ++ bs₂ ≡⟨ cong (_++ bs₂) (sym $ Σₚ.bs≡ l) ⟩
             Σₚ.bs l ++ bs₂ ∎)
    where
    l = proj₁ equivₛ fstₚ₁
  proj₂ equiv (Base64.mk64Str str strLen pad bs≡) =
    mk&ₚ l (proj₂ Base64Pad.equiv pad) bs≡
    where
    l = proj₂ equivₛ (mk×ₚ str (‼ strLen) refl)

  -- TODO: equality for List Char is decidable, so guard against ≡ [] first and then handle the negation case separately
  {-# TERMINATING #-}
  noOverlap : NoOverlap Repₛ (Sum Base64.Base64Pad1 Base64.Base64Pad2)
  noOverlap .[] .[] ys₁ xs₂ ys₂ ++≡ nil nil = inj₁ refl
  noOverlap .[] xs₁ ys₁ xs₂ ys₂ ++≡ (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) nil =
    inj₂ λ where
      p → contradiction c₄∈ (Base64Pad.c₄∉ (subst (Sum _ _) (Base64Pad.forcebs p ++≡ bs≡₁) p))
  noOverlap ws xs₁ ys₁ xs₂ ys₂ ++≡ r₁ (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) =
    case (subst₀ (Repₛ ∘ (_++ xs₁)) bs≡₁ r₁) ret (const _) of λ where
      (consIList{bs₂ = bs₂'} (mk&ₚ (Base64.mk64 c₁' c₁∈' _ refl) (mk&ₚ (Base64.mk64 c₂' c₂∈' _ refl) (mk&ₚ (Base64.mk64 c₃' c₃∈' _ refl) (Base64.mk64 c₄' c₄∈' _ refl)  refl) refl) refl) tail₁' bs≡₁') →
        let bs₂≡ : Erased (bs₂ ≡ drop 4 ws)
            bs₂≡ = ─ subst ((bs₂ ≡_) ∘ (drop 4)) (sym bs≡₁) refl

            bs₂'≡ : Erased (bs₂' ≡ drop 4 ws ++ xs₁)
            bs₂'≡ = ─ proj₂ (Lemmas.length-++-≡ _ _ (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) _
                              (begin ((c₁' ∷ c₂' ∷ c₃' ∷ [ c₄' ]) ++ bs₂' ≡⟨ sym bs≡₁' ⟩
                                     c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ] ++ bs₂ ++ xs₁ ≡⟨ cong (λ x → (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) ++ x ++ xs₁) (Erased.x bs₂≡) ⟩
                                     c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ] ++ (drop 4 ws) ++ xs₁ ∎))
                              refl)
        in
        noOverlap (drop 4 ws) xs₁ ys₁ xs₂ ys₂ ++≡
          (subst₀ Repₛ (Erased.x bs₂'≡) tail₁') (subst₀ Repₛ (Erased.x bs₂≡) tail₁)

  -- strictBoundary : StrictBoundary Repₛ (Sum Base64.Base64Pad1 Base64.Base64Pad2)
  -- strictBoundary xs .[] zs₁ ws₁ .[] zs₂ ws₂ xs≡₁ xs≡₂ nil nil _ _ = refl
  -- strictBoundary xs .[] zs₁ ws₁ ys₂ zs₂ ws₂ xs≡₁ xs≡₂ nil (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) (Sum.inj₁ (Base64.mk64P1{b₁'}{b₂'}{b₃'} c₁' c₂' c₃' _ bs'≡)) _ =
  --   contradiction {P = '=' ∈ B64.charset}
  --     (subst (_∈ B64.charset) c₄≡ c₄∈)
  --     (toWitnessFalse {Q = '=' ∈? B64.charset} tt)
  --   where
  --   @0 xs≡' : _≡_{A = List Char} (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂ ++ zs₂ ++ ws₂) (b₁' ∷ b₂' ∷ b₃' ∷ '=' ∷ ws₁)
  --   xs≡' = begin ((c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂) ++ zs₂ ++ ws₂ ≡⟨ cong (_++ zs₂ ++ ws₂) (sym bs≡₁) ⟩
  --                ys₂ ++ zs₂ ++ ws₂ ≡⟨ sym xs≡₂ ⟩
  --                xs ≡⟨ xs≡₁ ⟩
  --                zs₁ ++ ws₁ ≡⟨ cong (_++ ws₁) bs'≡ ⟩
  --                (b₁' ∷ b₂' ∷ b₃' ∷ [ '=' ]) ++ ws₁ ∎)
  --   @0 c₄≡ : c₄ ≡ '='
  --   c₄≡ = ∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ xs≡')))
  -- strictBoundary xs .[] zs₁ ws₁ ys₂ zs₂ ws₂ xs≡₁ xs≡₂ nil (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) (Sum.inj₂ (Base64.mk64P2{b₁'}{b₂'} c₁' c₂' _ bs'≡)) _ =
  --   contradiction{P = '=' ∈ B64.charset}
  --     (subst (_∈ B64.charset) c₄≡ c₄∈)
  --     (toWitnessFalse {Q = '=' ∈? B64.charset} tt)
  --   where
  --   @0 xs≡' : _≡_{A = List Char} (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂ ++ zs₂ ++ ws₂) (b₁' ∷ b₂' ∷ '=' ∷ '=' ∷ ws₁)
  --   xs≡' = begin ((c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂) ++ zs₂ ++ ws₂ ≡⟨ cong (_++ zs₂ ++ ws₂) (sym bs≡₁) ⟩
  --                ys₂ ++ zs₂ ++ ws₂ ≡⟨ sym xs≡₂ ⟩
  --                xs ≡⟨ xs≡₁ ⟩
  --                zs₁ ++ ws₁ ≡⟨ cong (_++ ws₁) bs'≡ ⟩
  --                (b₁' ∷ b₂' ∷ '=' ∷ [ '=' ]) ++ ws₁ ∎)
  --   @0 c₄≡ : c₄ ≡ '='
  --   c₄≡ = ∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ xs≡')))
  -- strictBoundary xs ys₁ zs₁ ws₁ .[] zs₂ ws₂ xs≡₁ xs≡₂ (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) nil _ (Sum.inj₁ (Base64.mk64P1{b₁'}{b₂'}{b₃'} c₁' c₂' c₃' _ bs'≡)) =
  --   contradiction{P = '=' ∈ B64.charset}
  --     (subst (_∈ B64.charset) c₄≡ c₄∈)
  --     (toWitnessFalse {Q = '=' ∈? B64.charset} tt)
  --   where
  --   @0 xs≡' : _≡_{A = List Char} (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂ ++ zs₁ ++ ws₁) (b₁' ∷ b₂' ∷ b₃' ∷ '=' ∷ ws₂)
  --   xs≡' = begin ((c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂) ++ zs₁ ++ ws₁ ≡⟨ cong (_++ zs₁ ++ ws₁) (sym bs≡₁) ⟩
  --                ys₁ ++ zs₁ ++ ws₁ ≡⟨ sym xs≡₁ ⟩
  --                xs ≡⟨ xs≡₂ ⟩
  --                zs₂ ++ ws₂ ≡⟨ cong (_++ ws₂) bs'≡ ⟩
  --                (b₁' ∷ b₂' ∷ b₃' ∷ [ '=' ]) ++ ws₂ ∎)
  --   @0 c₄≡ : c₄ ≡ '='
  --   c₄≡ = ∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ xs≡')))
  -- strictBoundary xs ys₁ zs₁ ws₁ .[] zs₂ ws₂ xs≡₁ xs≡₂ (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) nil _ (Sum.inj₂ (Base64.mk64P2{b₁'}{b₂'} c₁' c₂' _ bs'≡)) =
  --   contradiction{P = '=' ∈ B64.charset}
  --     (subst (_∈ B64.charset) c₄≡ c₄∈)
  --     (toWitnessFalse {Q = '=' ∈? B64.charset} tt)
  --   where
  --   @0 xs≡' : _≡_{A = List Char} (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂ ++ zs₁ ++ ws₁) (b₁' ∷ b₂' ∷ '=' ∷ '=' ∷ ws₂)
  --   xs≡' = begin ((c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂) ++ zs₁ ++ ws₁ ≡⟨ cong (_++ zs₁ ++ ws₁) (sym bs≡₁) ⟩
  --                ys₁ ++ zs₁ ++ ws₁ ≡⟨ sym xs≡₁ ⟩
  --                xs ≡⟨ xs≡₂ ⟩
  --                zs₂ ++ ws₂ ≡⟨ cong (_++ ws₂) bs'≡ ⟩
  --                (b₁' ∷ b₂' ∷ '=' ∷ [ '=' ]) ++ ws₂ ∎)
  --   @0 c₄≡ : c₄ ≡ '='
  --   c₄≡ = ∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (∷-injectiveʳ xs≡')))
  -- strictBoundary xs ys₁ zs₁ ws₁ ys₂ zs₂ ws₂ xs≡₁ xs≡₂ (consIList{bs₂ = bs₂} (mk&ₚ (Base64.mk64 c₁ c₁∈ _ refl) (mk&ₚ (Base64.mk64 c₂ c₂∈ _ refl) (mk&ₚ (Base64.mk64 c₃ c₃∈ _ refl) (Base64.mk64 c₄ c₄∈ _ refl)  refl) refl) refl) tail₁ bs≡₁) (consIList{bs₂ = bs₂'} (mk&ₚ (Base64.mk64 c₁' c₁∈' _ refl) (mk&ₚ (Base64.mk64 c₂' c₂∈' _ refl) (mk&ₚ (Base64.mk64 c₃' c₃∈' _ refl) (Base64.mk64 c₄' c₄∈' _ refl)  refl) refl) refl) tail₁' bs≡₁') p₁ p₂ =
  --   ‼ (begin ys₁ ≡⟨ bs≡₁ ⟩
  --         c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ] ++ bs₂
  --           ≡⟨ cong₂ _++_
  --                (proj₁ (Lemmas.length-++-≡ (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ]) (bs₂ ++ zs₁ ++ ws₁) _ (bs₂' ++ zs₂ ++ ws₂)
  --                         (begin (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs₂ ++ zs₁ ++ ws₁ ≡⟨ cong (_++ zs₁ ++ ws₁) (sym bs≡₁) ⟩
  --                                ys₁ ++ zs₁ ++ ws₁ ≡⟨ sym xs≡₁ ⟩
  --                                xs ≡⟨ xs≡₂ ⟩
  --                                ys₂ ++ zs₂ ++ ws₂ ≡⟨ cong (_++ zs₂ ++ ws₂) bs≡₁' ⟩
  --                                _ ∎))
  --                         refl))
  --                sb' ⟩
  --         c₁' ∷ c₂' ∷ c₃' ∷ [ c₄' ] ++ bs₂' ≡⟨ sym bs≡₁' ⟩
  --         ys₂ ∎)
  --   where
  --   @0 sb' : bs₂ ≡ bs₂'
  --   sb' = strictBoundary (drop 4 xs) bs₂ zs₁ ws₁ bs₂' zs₂ ws₂
  --           (begin drop 4 xs ≡⟨ cong (drop 4) xs≡₁ ⟩
  --                  drop 4 (ys₁ ++ zs₁ ++ ws₁) ≡⟨ cong (λ x → drop 4 (x ++ zs₁ ++ ws₁)) bs≡₁ ⟩
  --                  bs₂ ++ zs₁ ++ ws₁ ∎)
  --           (begin (drop 4 xs ≡⟨ cong (drop 4) xs≡₂ ⟩
  --                  drop 4 (ys₂ ++ zs₂ ++ ws₂) ≡⟨ cong (λ x → drop 4 (x ++ zs₂ ++ ws₂)) bs≡₁' ⟩
  --                  bs₂' ++ zs₂ ++ ws₂ ∎))
  --           tail₁ tail₁' p₁ p₂

  b64Str? : Decidable Base64.Base64Str
  b64Str? bs =
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
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) c₂ pad refl)) refl) →
          contradiction c∈ c₁∉
        (Base64.mk64Str (cons (mkIListCons (Base64.mk64 c c∈ i refl) tail₁ refl)) strLen pad bs≡) →
          contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (sym bs≡)) c∈) c₁∉
    ... | yes _  | no c₂∉ =
      no λ where
        (Base64.mk64Str nil strLen (Base64.pad0 ()) refl)
        (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 _ _ _ refl) (Base64.mk64 c₂' c₂∈' i₂' refl) c₃ pad refl)) bs≡) →
          contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (sym bs≡))) c₂∈') c₂∉
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 ._ _ _ refl) (Base64.mk64 .c₂ c₂∈' i₁ refl) pad refl)) refl) →
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
            (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
              contradiction (erefl '=') ¬c₃≡=
            (Base64.mk64Str (consIList (Base64.mk64 c₁' _ _ refl) (consIList (Base64.mk64 c₂' _ _ refl) (consIList (Base64.mk64 c₃' c₃'∈ _ refl) _ refl) refl) refl) strLen pad bs≡) →
              contradiction (subst (_∈ B64.charset) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ (sym bs≡)))) c₃'∈) ¬c₃∈
        (yes refl , no ¬c₄≡=) →
          no λ where
            (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
            (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .'=' c∈₂ i₂ refl) pad refl)) refl) →
              contradiction (erefl '=') ¬c₄≡=
            (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
              contradiction (erefl '=') ¬c₄≡=
            (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 c₃' c₃∈' _ refl) (consIList (Base64.mk64 c₄' c₄∈' _ refl) _ refl) refl) refl) refl) strLen pad bs≡) →
              contradiction c₃∈' (subst (¬_ ∘ (_∈ B64.charset)) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡))) (toWitnessFalse {Q = _ ∈? _} tt))
        (yes refl , yes refl) →
          let i = Any.index c₂∈ in
          case toℕ i % (2 ^ 4) ≟ 0 of λ where
            (no ¬c₂0s) →
              no λ where
                (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
                (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .'=' c₃∈' _ refl) pad refl)) refl) →
                  contradiction c₃∈' (toWitnessFalse{Q = _ ∈? _} tt)
                (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ _ _ refl) (Base64.mk64 .c₂ c₂∈' (singleton i' i≡') refl) pad refl)) refl) →
                  contradiction
                    (begin toℕ (Any.index c₂∈)  % (2 ^ 4) ≡⟨ cong (λ x → toℕ (Any.index x) % (2 ^ 4)) (B64.∈charsetUnique c₂∈ c₂∈') ⟩
                           toℕ (Any.index c₂∈') % (2 ^ 4) ≡⟨ cong (λ x → toℕ x % (2 ^ 4)) (sym i≡') ⟩
                           toℕ i' % (2 ^ 4)               ≡⟨ pad ⟩
                           0 ∎)
                    ¬c₂0s
                (Base64.mk64Str (consIList (Base64.mk64 _ _ _ refl) (consIList (Base64.mk64 _ _ _ refl) (cons (mkIListCons (Base64.mk64 c₃' c₃∈' _ refl) _ refl)) refl) refl) strLen pad bs≡) →
                  contradiction c₃∈' (subst (¬_ ∘ (_∈ B64.charset)) (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ bs≡))) (toWitnessFalse{Q = _ ∈? _} tt))
            (yes c₂0s) →
              yes (Base64.mk64Str nil refl (Base64.pad2 (Base64.mk64P2 (Base64.mk64 c₁ c₁∈ self refl) (Base64.mk64 c₂ c₂∈ self refl) c₂0s refl)) refl)
    ... | yes c₃∈
      with c₄ ∈? B64.charset
    ... | no ¬c₄∈ =
      case c₄ ≟ '=' of λ where
        (no ¬c₄≡=) →
          no λ where
            (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
            (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) (Base64.mk64 .c₃ c∈₂ i₂ refl) pad refl)) refl) →
              contradiction refl ¬c₄≡=
            (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
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
                (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 (Base64.mk64 .c₁ c∈ i refl) (Base64.mk64 .c₂ c∈₁ i₁ refl) pad refl)) refl) →
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
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) ())
        (Base64.mk64Str (consIList (Base64.mk64 c₁' c₁∈' i₁' refl) (consIList (Base64.mk64 c₂' c₂∈' i₂' refl) (consIList (Base64.mk64 c₃' c₃∈' i₃' refl) (consIList (Base64.mk64 c₄' c₄∈' i₄' refl) tail₁ refl) refl) refl) refl) strLen pad bs≡) →
          contradiction
            (Base64.mk64Str tail₁ strLen pad (proj₂ $ Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ [ _ ]) bs (_ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡ (erefl 4)))
            ¬p
    helper (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ bs@(_ ∷ _)) %4 | yes (Base64.mk64Str str₀ strLen₀ pad₀ bs≡₀)
      with All.all? (_∈? B64.charset) (c₁ ∷ c₂ ∷ c₃ ∷ [ c₄ ])
    ... | no ¬all∈ =
      no λ where
        (Base64.mk64Str nil strLen (Base64.pad0 refl) ())
        (Base64.mk64Str nil strLen (Base64.pad1 (Base64.mk64P1 c₁ c₂ c₃ pad ())) refl)
        (Base64.mk64Str nil strLen (Base64.pad2 (Base64.mk64P2 c₁ c₂ pad refl)) ())
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
