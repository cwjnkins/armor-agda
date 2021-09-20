open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509

module Aeres.Data.X509.Properties where

open Base256
open import Aeres.Grammar.Definitions Dig

module NonNesting where
  postulate
    LengthNN : NonNesting Length
    OIDSub   : NonNesting Generic.OIDSub

module NonEmpty where
 -- OIDSub : NonEmpty Generic.OIDSub
 -- OIDSub {.[]} (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
 --OIDSub {.[]} (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

 -- UtcTime : NonEmpty X509.UtcTime
 -- UtcTime {[]} = {![]!}
 -- UtcTime {x ∷ xs} = {!!}

 OIDSub : NonEmpty Generic.OIDSub
 OIDSub (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
 OIDSub (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

-- try other nodes from x.509 agda

-- open Base256

-- Unambiguous : (A : List Dig → Set) → Set
-- Unambiguous A = ∀ {xs} → (a₁ a₂ : A xs) → a₁ ≡ a₂

-- NoNest : (A : List Dig → Set) → Set
-- NoNest A = ∀ {xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ → A xs₁ → A xs₂ → xs₁ ≡ xs₂

-- NonEmpty : (A : List Dig → Set) → Set
-- NonEmpty A = ∀ {xs} → A xs → xs ≢ []

-- module NonEmpty where
--   postulate
--     OIDSub : NonEmpty Generic.OIDSub

-- -- TODO: Prove
-- module Unambiguous where
--   postulate
--     LengthUA : Unambiguous Length
--     Cert     : Unambiguous X509.Cert
--     TBSCert  : Unambiguous X509.TBSCert

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
