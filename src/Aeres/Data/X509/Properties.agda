{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties where

open Base256
open import Aeres.Grammar.Definitions Dig

module NonEmpty where

  BoolValue : NonEmpty Generic.BoolValue
  BoolValue () refl

  OIDSub : NonEmpty Generic.OIDSub
  OIDSub (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
  OIDSub (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

  Time : NonEmpty Generic.Time
  Time (Generic.utctm ()) refl
  Time (Generic.gentm ()) refl

  Validity : NonEmpty X509.Validity
  Validity () refl

  -- Cert : NonEmpty X509.Cert
  -- Cert (X509.mkCert len tbs signAlg signature len≡ ()) refl

  @0 TLV : ∀ {t} {@0 A} → NonEmpty (Generic.TLV t A)
  TLV (Generic.mkTLV len val len≡ ()) refl

module Unambiguous where
  MinRep-irrelevant : Irrelevant₂ Length.MinRep
  MinRep-irrelevant{lₕ}{lₜ} mr₁ mr₂
    with lₜ ≟ []
  ... | yes refl = ≤-irrelevant mr₁ mr₂
  MinRep-irrelevant {lₕ} {lₜ} tt tt | no lₜ≢[] = refl


  @0 LengthUA : Unambiguous Length
  LengthUA (Length.short (Length.mkShort l l<128 refl)) (Length.short (Length.mkShort .l l<129 refl))
    with <-irrelevant l<128 l<129
  ... | refl = refl
  LengthUA (Length.short (Length.mkShort l l<128 refl)) (Length.long (Length.mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep ()))
  LengthUA (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.short (Length.mkShort l₁ l<128 ()))
  LengthUA (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.long (Length.mkLong .l l>129 .lₕ lₕ≢1 .lₜ lₜLen₁ lₕₜMinRep₁ refl))
    with <-irrelevant l>128 l>129
    |    <-irrelevant lₕ≢0  lₕ≢1
    |    ≡-irrelevant lₜLen lₜLen₁
    |    MinRep-irrelevant lₕₜMinRep lₕₜMinRep₁
  ... | refl | refl | refl | refl = refl

  @0 getLengthUA : ∀ {xs ys} → xs ≡ ys → (l₁ : Length xs) (l₂ : Length ys) → getLength l₁ ≡ getLength l₂
  getLengthUA refl l₁ l₂ = cong getLength (LengthUA l₁ l₂)

module NonNesting where
  postulate
    ExactLengthNN : ∀ {A n} → NonNesting (ExactLength A n)
    OIDSub        : NonNesting Generic.OIDSub
    BoolValue     : NonNesting Generic.BoolValue
    MonthDayHourMinSecFields : NonNesting Generic.MonthDayHourMinSecFields
    UtcTimeFields : NonNesting Generic.UtcTimeFields
    @0 UtcTime       : NonNesting Generic.UtcTime

    DirectoryString : NonNesting X509.DirectoryString

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

  @0 TLV : ∀ {t} {@0 A} → NonNesting (Generic.TLV t A)
  TLV{t}{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (Generic.mkTLV{l}{v} len val len≡ bs≡) (Generic.mkTLV{l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) =
    ‼ (begin xs₁ ≡⟨ bs≡ ⟩
             t ∷ l ++ v ≡⟨ cong (t ∷_) (cong (_++ v) l≡) ⟩
             t ∷ l₁ ++ v ≡⟨ cong (t ∷_) (cong (l₁ ++_) v≡) ⟩
             t ∷ l₁ ++ v₁ ≡⟨ sym bs≡₁ ⟩
             xs₂ ∎)
    where
    open ≡-Reasoning
    @0 l++≡ : l ++ v ++ ys₁ ≡ l₁ ++ v₁ ++ ys₂
    l++≡ = ∷-injectiveʳ (begin (t ∷ l ++ v ++ ys₁     ≡⟨ cong (t ∷_) (solve (++-monoid Dig)) ⟩
                                t ∷ (l ++ v) ++ ys₁   ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                                xs₁ ++ ys₁            ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                                xs₂ ++ ys₂            ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                                t ∷ (l₁ ++ v₁) ++ ys₂ ≡⟨ cong (t ∷_) (solve (++-monoid Dig)) ⟩
                                t ∷ l₁ ++ v₁ ++ ys₂   ∎))

    @0 l≡ : l ≡ l₁
    l≡ = LengthNN l++≡ len len₁

    @0 v≡ : v ≡ v₁
    v≡ = proj₁ $ Lemmas.length-++-≡ _ _ _ _
                   (++-cancelˡ l (trans l++≡ (cong (_++ v₁ ++ ys₂) (sym l≡))))
                   (begin length v       ≡⟨ sym len≡ ⟩
                          getLength len  ≡⟨ Unambiguous.getLengthUA l≡ len len₁ ⟩
                          getLength len₁ ≡⟨ len≡₁ ⟩
                          length v₁      ∎)

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
