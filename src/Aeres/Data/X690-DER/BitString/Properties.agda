{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X690-DER.BitString.Properties where

open Aeres.Grammar.Definitions UInt8
open ≡-Reasoning

uniqueUnusedBits : ∀ {bₕ bₜ} → Unique (UnusedBits bₕ bₜ)
uniqueUnusedBits {bₜ = []} x y = ≡-unique x y
uniqueUnusedBits {bₜ = x₁ ∷ []} x y = ≡-unique x y
uniqueUnusedBits {bₜ = x₁ ∷ x₂ ∷ bₜ} x y = uniqueUnusedBits{bₜ = x₂ ∷ bₜ} x y

unusedBits? : ∀ b bs → Dec (UnusedBits b bs)
unusedBits? b [] = toℕ b ≟ 0
unusedBits? b (x ∷ []) = toℕ x %2^ (toℕ b) ≟ 0
unusedBits? b (x ∷ x₁ ∷ bs) = unusedBits? b (x₁ ∷ bs)

@0 toBitRep-injective
  : ∀ (@0 bₕ₁ bₕ₂ bₜ₁ bₜ₂)
    → @0 toℕ bₕ₁ < 8 → @0 toℕ bₕ₂ < 8
    → @0 UnusedBits bₕ₁ bₜ₁ → @0 UnusedBits bₕ₂ bₜ₂
    → toBitRep bₕ₁ bₜ₁ ≡ toBitRep bₕ₂ bₜ₂ → (bₕ₁ ,′ bₜ₁) ≡ (bₕ₂ ,′ bₜ₂)
toBitRep-injective bₕ₁ bₕ₂ [] [] bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡
  rewrite Fin.toℕ-injective{i = bₕ₁}{bₕ₂} (trans u₁ (sym u₂)) = refl
toBitRep-injective bₕ₁ bₕ₂ [] (b₂ ∷ []) bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
  contradiction{P = length xs ≡ 0}
    (cong length (sym rep≡))
    (>⇒≢ takeLen₄)
  where
  len₂ : length (Vec.toList (toBinary{8} b₂)) ≡ 8
  len₂ = Lemmas.toListLength (toBinary b₂)

  xs = take (8 - toℕ bₕ₂) (Vec.toList (toBinary{8} b₂))

  takeLen₂ : length xs ≡ (8 - toℕ bₕ₂) ⊓ 8
  takeLen₂ = trans (length-take (8 - toℕ bₕ₂) (Vec.toList (toBinary{8} b₂)))
               (cong ((8 - toℕ bₕ₂) ⊓_) len₂)

  takeLen₃ : length xs ≡ 8 - toℕ bₕ₂
  takeLen₃ = trans takeLen₂ (m≤n⇒m⊓n≡m (m∸n≤m 8 (toℕ bₕ₂)))

  takeLen₄ : length xs > 0
  takeLen₄ = ≤-trans (0 < 8 - toℕ bₕ₂ ∋ m<n⇒0<n∸m bₕ₂<8) (Lemmas.≡⇒≤ (sym takeLen₃))
toBitRep-injective bₕ₁ bₕ₂ [] (b₂₁ ∷ b₂₂ ∷ bₜ₂) bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ =
  contradiction{P = 0 ≥ 8} (≤-trans len≥ (Lemmas.≡⇒≤ (sym (cong length rep≡)))) λ ()
  where
  module ≤ = ≤-Reasoning

  xs = Vec.toList (toBinary{8} b₂₁) ++ toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)

  len≥ : length xs ≥ 8
  len≥ = ≤.begin
    8 ≤.≡⟨ (sym $ Lemmas.toListLength (toBinary{8} b₂₁)) ⟩
    length (Vec.toList $ toBinary{8} b₂₁) ≤.≤⟨ m≤m+n _ _ ⟩
    length (Vec.toList $ toBinary{8} b₂₁) + length (toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)) ≤.≡⟨ sym (length-++ (Vec.toList $ toBinary{8} b₂₁)) ⟩
    length (Vec.toList (toBinary{8} b₂₁) ++ toBitRep bₕ₂ (b₂₂ ∷ bₜ₂)) ≤.≡⟨⟩
    (length xs ≤.∎)
toBitRep-injective bₕ₁ bₕ₂ (x ∷ bₜ₁) bₜ₂ bₕ₁<8 bₕ₂<8 u₁ u₂ rep≡ = TODO
  where
  postulate
    TODO : _

instance
  eq : Eq (Exists─ (List UInt8) BitStringValue)
  Eq._≟_ eq (─ bs₁ , mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 (singleton bits₁ bits₁≡) unusedBits₁ bs≡₁) (─ bs₂ , mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ bs≡₂) =
    case bits₁ ≟ bits₂ ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes bits≡) →
        let @0 bₕₜ≡ : Erased _
            bₕₜ≡ = ─ toBitRep-injective bₕ₁ bₕ₂ bₜ₁ bₜ₂ bₕ₁<8 bₕ₂<8 unusedBits₁ unusedBits₂ (trans (sym bits₁≡) (trans bits≡ bits₂≡))

            @0 bₕ≡ : Erased (bₕ₁ ≡ bₕ₂)
            bₕ≡ = ─ cong proj₁ (Erased.x bₕₜ≡)

            @0 bₜ≡ : Erased (bₜ₁ ≡ bₜ₂)
            bₜ≡ = ─ cong proj₂ (Erased.x bₕₜ≡)

            @0 bs≡₁' : Erased (bs₁ ≡ bs₂)
            bs≡₁' = ─ (trans bs≡₁ (trans (cong₂ _∷_ (¡ bₕ≡) (¡ bₜ≡)) (sym bs≡₂)))
        in
        yes (begin (─ bs₁ , mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 (singleton bits₁ bits₁≡) unusedBits₁ bs≡₁
                     ≡⟨ ‼ subst₂
                          (λ h t →
                             (@0 h<8 : toℕ h < 8) (s : Singleton (toBitRep h t)) (@0 u : UnusedBits h t) (@0 eq₁ : bs₁ ≡ h ∷ t) →
                               _,e_{A = Erased (List UInt8)}{B = BitStringValue ∘ Erased.x}
                                   (─ bs₁)
                                   (mkBitStringValue h t h<8 s u eq₁)
                             ≡ (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ (trans (¡ bs≡₁') bs≡₂)))
                          (sym (¡ bₕ≡)) (sym (¡ bₜ≡))
                          (λ h<8 s u eq₁ →
                            let <8≡ : Erased (h<8 ≡ bₕ₂<8)
                                <8≡ = ─ ≤-unique _ _

                                s≡ : s ≡ singleton bits₂ bits₂≡
                                s≡ = uniqueSingleton _ _

                                u≡ : Erased (u ≡ unusedBits₂)
                                u≡ = ─ (uniqueUnusedBits{bₕ₂}{bₜ₂} u unusedBits₂)
                            in
                            subst₂
                              (λ x y → (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ x y u eq₁) ≡ (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ _))
                              (sym (¡ <8≡)) (sym s≡)
                              (subst₂
                                (λ x y → (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) x y) ≡ (─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ _) )
                                (sym (¡ u≡))
                                (≡-unique _ eq₁)
                                refl)
                            )
                          bₕ₁<8 (singleton bits₁ bits₁≡) unusedBits₁ bs≡₁ ⟩
                   ─ bs₁ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ (trans (¡ bs≡₁') bs≡₂)
                     ≡⟨ ‼ (subst
                             (λ bs → (@0 eq : bs ≡ bₕ₂ ∷ bₜ₂)
                                     → (─ bs ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ eq)
                                       ≡ (─ bs₂ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ bs≡₂) )
                             (sym (¡ bs≡₁'))
                             (λ eq₁ →
                               cong (λ eq₁' → (─ bs₂ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ eq₁')) (≡-unique eq₁ _))
                             (trans (¡ bs≡₁') bs≡₂)) ⟩
                   ─ bs₂ ,e mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 (singleton bits₂ bits₂≡) unusedBits₂ bs≡₂ ∎))
    where
    open ≡-Reasoning

@0 unambiguous : Unambiguous BitStringValue
unambiguous (mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁) (mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂) =
  ≡-elim (λ {bₕ₂} bₕ≡ → ∀ bₕ₂<8 bits₂ unusedBits₂ bs≡₂ → mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ ≡ mkBitStringValue bₕ₂ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂)
    (λ bₕ₂<8 bits₂ unusedBits₂ bs≡₂' →
      ≡-elim (λ {bₜ₂} bₜ≡ → ∀ (bits₂ : Singleton (toBitRep bₕ₁ bₜ₂)) unusedBits₂ bs≡₂ → mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ ≡ mkBitStringValue bₕ₁ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂)
        (λ bits₂ unusedBits₂ bs≡₂' →
          subst₂ (λ bits bs≡ → _ ≡ mkBitStringValue bₕ₁ bₜ₁ _ bits _ bs≡) (uniqueSingleton bits₁ bits₂) (≡-unique bs≡₁ bs≡₂')
            (subst₂ (λ x y → _ ≡ mkBitStringValue bₕ₁ bₜ₁ x _ y _) (≤-irrelevant bₕ₁<8 bₕ₂<8) (uniqueUnusedBits{bₜ = bₜ₁} unusedBits₁ unusedBits₂)
              refl))
        bₜ≡ bits₂ unusedBits₂ bs≡₂')
    bₕ≡ bₕ₂<8 bits₂ unusedBits₂ bs≡₂
  where
  @0 bs≡ : bₕ₁ ∷ bₜ₁ ≡ bₕ₂ ∷ bₜ₂
  bs≡ = trans₀ (sym bs≡₁) bs≡₂

  @0 bₕ≡ : bₕ₁ ≡ bₕ₂
  bₕ≡ = ∷-injectiveˡ bs≡

  @0 bₜ≡ : _
  bₜ≡ = ∷-injectiveʳ bs≡
