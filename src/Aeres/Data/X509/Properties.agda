open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties

module Aeres.Data.X509.Properties where

open Base256
open import Aeres.Grammar.Definitions Dig

module NonEmpty where

   OIDSub : NonEmpty Generic.OIDSub
   OIDSub (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
   OIDSub (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

   Time : NonEmpty X509.Time
   Time (X509.utctm ()) refl
   Time (X509.gentm ()) refl

   Validity : NonEmpty X509.Validity
   Validity () refl

   Cert : NonEmpty X509.Cert
   Cert () refl

module Unambiguous where
  postulate
    LengthUA : Unambiguous Length

module NonNesting where
  postulate
    OIDSub   : NonNesting Generic.OIDSub

  LengthNN : NonNesting Length
  LengthNN xs₁++ys₁≡xs₂++ys₂ (Length.short (Length.mkShort l l<128 refl)) (Length.short (Length.mkShort l₁ l<129 refl)) =
    cong [_] (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂)
  LengthNN xs₁++ys₁≡xs₂++ys₂ (Length.short (Length.mkShort l l<128 refl)) (Length.long (Length.mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) =
    contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i) (sym $ ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
  LengthNN xs₁++ys₁≡xs₂++ys₂ (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.short (Length.mkShort l₁ l<128 refl)) =
    contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i)  (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
  LengthNN xs₁++ys₁≡xs₂++ys₂ (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.long (Length.mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRep₁ refl)) =
    begin (l ∷ lₕ ∷ lₜ   ≡⟨ cong (_∷ lₕ ∷ lₜ) (‼ l≡) ⟩
          l₁ ∷ lₕ ∷ lₜ   ≡⟨ cong (λ x → l₁ ∷ x ∷ lₜ) (‼ lₕ≡) ⟩
          l₁ ∷ lₕ₁ ∷ lₜ  ≡⟨ cong (λ x → l₁ ∷ lₕ₁ ∷ x) (‼ lₜ≡) ⟩
          l₁ ∷ lₕ₁ ∷ lₜ₁ ∎)
    where
    open ≡-Reasoning

    @0 l≡ : l ≡ l₁
    l≡ = ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂

    @0 lₕ≡ : lₕ ≡ lₕ₁
    lₕ≡ = ∷-injectiveˡ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

    @0 lₜ++ys₁≡ : lₜ ++ _ ≡ lₜ₁ ++ _
    lₜ++ys₁≡ = ∷-injectiveʳ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

    @0 lₜ≡ : lₜ ≡ lₜ₁
    lₜ≡ =
      proj₁ $ Lemmas.length-++-≡ _ _ _ _ lₜ++ys₁≡
                (trans lₜLen (trans (cong (λ x → toℕ x ∸ 129) l≡) (sym lₜLen₁)))

-- -- corollary of `Unambiguous.LengthUA`
-- getLength≡ : ∀ {xs ys} → xs ≡ ys → (l₀ : Length xs) (l₁ : Length ys) → getLength l₀ ≡ getLength l₁
-- getLength≡{xs}{.xs} refl l₀ l₁ = cong getLength (Unambiguous.LengthUA l₀ l₁)

-- module NoNest where
--   postulate
--     OIDSub   : NoNest Generic.OIDSub
--     TBSCert  : NoNest X509.TBSCert
--     LengthNN : NoNest Length
--     SignAlg  : NoNest X509.SignAlg

--   -- TBSCert : NoNest X509.TBSCert
--   -- TBSCert{ys₁ = ys₀}{ys₂ = ys₁} eq (X509.mkTBSCert{len₀}{tbsbs₀} l₀ tbsf₀ len≡₀) (X509.mkTBSCert{len₁}{tbsbs₁} l₁ tbsf₁ len≡₁) =
--   --   cong (Tag.Sequence ∷_) (cong₂ _++_ eqₗ eq₃)
--   --   where
--   --   open ≡-Reasoning

--   --   eq₁ : len₀ ++ tbsbs₀ ++ ys₀ ≡ len₁ ++ tbsbs₁ ++ ys₁
--   --   eq₁ = ∷-injectiveʳ{x = Tag.Sequence}{y = Tag.Sequence} $ begin
--   --     Tag.Sequence ∷ len₀ ++ tbsbs₀ ++ ys₀
--   --       ≡⟨ Lemmas.++-assoc₄ [ Tag.Sequence ] len₀ tbsbs₀ ys₀ ⟩
--   --     (Tag.Sequence ∷ len₀ ++ tbsbs₀) ++ ys₀
--   --       ≡⟨ eq ⟩
--   --     (Tag.Sequence ∷ len₁ ++ tbsbs₁) ++ ys₁
--   --       ≡⟨ sym $ Lemmas.++-assoc₄ [ Tag.Sequence ] len₁ tbsbs₁ ys₁ ⟩
--   --     Tag.Sequence ∷ len₁ ++ tbsbs₁ ++ ys₁ ∎

--   --   eqₗ : len₀ ≡ len₁
--   --   eqₗ = LengthNN eq₁ l₀ l₁

--   --   eq₂ : tbsbs₀ ++ ys₀ ≡ tbsbs₁ ++ ys₁
--   --   eq₂ = ++-cancelˡ len₁ (subst (λ x → x ++ tbsbs₀ ++ ys₀ ≡ len₁ ++ tbsbs₁ ++ ys₁) eqₗ eq₁)

--   --   eq₃ : tbsbs₀ ≡ tbsbs₁
--   --   eq₃ = proj₁ ∘ Lemmas.length-++-≡ _ _ _ _ eq₂ $ begin
--   --     length tbsbs₀ ≡⟨ toWitness len≡₀ ⟩
--   --     getLength l₀  ≡⟨ getLength≡ eqₗ l₀ l₁ ⟩
--   --     getLength l₁  ≡⟨ sym $ toWitness len≡₁ ⟩
--   --     length tbsbs₁ ∎
