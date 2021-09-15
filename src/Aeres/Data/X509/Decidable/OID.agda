{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Parser
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.OID where

open Base256

module parseOIDSub where
  here' = "parseOIDSub"

  parseOIDSub : Parser Dig (Logging ∘ Dec) Generic.OIDSub
  runParser parseOIDSub xs
    with runParser (parseWhileₜ Dig ((_≥? 128) ∘ toℕ)) xs
  ... | no  ¬parse = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success Dig Generic.OIDSub xs
    go (success ._ read@._ refl (Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl) suffix refl) =
      contradiction (success (lₚ ∷ʳ lₑ) read refl (mkParseWhile lₚ lₑ lₚ≥128 (<⇒≱ lₑ<128) refl) suffix refl) ¬parse
  ... | yes (success ._ _ read≡ (mkParseWhile lₚ lₑ lₚ≥128 ¬lₑ≥128 refl) suffix refl)
    with lₚ
  ... | [] = return (yes (success [ lₑ ] _ read≡ (Generic.mkOIDSub [] All.[] lₑ (≰⇒> ¬lₑ≥128) tt refl) suffix refl))
  ... | lₚ'@(l ∷ lₚ)
    with toℕ l >? 128
  ... | no  l≯128 = do
    tell $ here' String.++ ": leading byte has value 0 (non-minimal repr.)"
    return ∘ no $ ‼ go
    where
    @0 go : ¬ Success Dig Generic.OIDSub (lₚ' ∷ʳ lₑ ++ suffix)
    go (success .([] ∷ʳ lₑ1) _ read≡ (Generic.mkOIDSub [] lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) .((lₚ ++ [ lₑ ]) ++ suffix) refl) =
      contradiction lₑ1<128 (≤⇒≯ (proj₁ (All.uncons lₚ≥128)))
    go (success .((x ∷ lₚ1) ∷ʳ lₑ1) _ read≡ (Generic.mkOIDSub (x ∷ lₚ1) lₚ1≥128 lₑ1 lₑ1<128 leastDigs1 refl) suffix1 ps≡1) =
      contradiction (subst (λ y → 128 < toℕ y) (∷-injectiveˡ ps≡1) leastDigs1) l≯128
  ... | yes l>128 =
    return (yes (success (lₚ' ∷ʳ lₑ) _ read≡ (Generic.mkOIDSub lₚ' lₚ≥128 lₑ (≰⇒> ¬lₑ≥128) l>128 refl) suffix refl))

open parseOIDSub public using (parseOIDSub)

module parseOIDField where
  here' = "parseOIDField"

  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  parseOIDFieldWF : ∀ n → ParserWF Dig (Logging ∘ Dec) (λ xs → Generic.OIDField xs × length xs ≡ n)
  runParser (parseOIDFieldWF n) xs (WellFounded.acc rs) = {!!}


  -- parseOIDField-wf  : ParserWF Dig (Logging ∘ Dec) Generic.OIDField
  -- parseOIDFieldₐ-wf : ParserWF Dig (Logging ∘ Dec) Generic.OIDFieldₐ

  -- runParser parseOIDField-wf xs (WellFounded.acc rs) = do
  --   yes (success pre₀ r₀ r₀≡ oidₛ suf₀ ps≡₀) ← runParser parseOIDSub xs
  --     where no ¬parse → do
  --       tell here'
  --       return ∘ no $ λ where
  --         (success prefix read read≡ Generic.[ sub ]OID suffix ps≡) →
  --           contradiction (success prefix _ read≡ sub suffix ps≡) ¬parse
  --         (success prefix read read≡ (Generic.cons (Generic.mkOIDFieldₐ{bs₁}{bs₂} sub rest bs≡)) suffix ps≡) →
  --           ‼ ¬parse (success bs₁ _ refl sub (bs₂ ++ suffix)
  --               (begin (bs₁ ++ bs₂ ++ suffix  ≡⟨ solve (++-monoid Dig) ⟩
  --                      (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
  --                      prefix ++ suffix       ≡⟨ ps≡ ⟩
  --                      xs                     ∎)))
  --   case suf₀ ≟ [] of λ where
  --     (yes suf₀≡[]) →
  --       return (yes (success pre₀ _ r₀≡ Generic.[ oidₛ ]OID {!!} {!!}))
  --     (no  suf₀≢[]) → {!!}

  -- runParser parseOIDFieldₐ-wf xs (WellFounded.acc rs) = do
  --   yes (success pre₀ r₀ r₀≡ oidₛ suf₀ ps≡₀) ← runParser parseOIDSub xs
  --     where no ¬parse → do
  --       tell here'
  --       return ∘ no $ λ where
  --         (success prefix read read≡ (Generic.mkOIDFieldₐ {bs₁}{bs₂} sub rest bs≡) suffix ps≡) →
  --           ‼ ¬parse (success bs₁ (length bs₁) refl sub (bs₂ ++ suffix)
  --               (begin (bs₁ ++ bs₂ ++ suffix  ≡⟨ solve (++-monoid Dig) ⟩
  --                      (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
  --                      prefix ++ suffix       ≡⟨ ps≡ ⟩
  --                      xs                     ∎)))
  --   yes (success pre₁ r₁ r₁≡ oidₑ suf₁ ps≡₁) ←
  --     let @0 wf : _
  --         wf = subst (λ i → length suf₀ < length i) ps≡₀ (Lemmas.length-++-< pre₀ suf₀ (NonEmpty.OIDSub oidₛ))
  --     in runParser parseOIDField-wf suf₀ (rs _ wf)
  --     where no ¬parse → do
  --       tell here'
  --       return ∘ no $ λ where
  --         (success prefix read read≡ (Generic.mkOIDFieldₐ{bs₁}{bs₂} sub rest bs≡) suffix ps≡) →
  --           ‼ ¬parse (success _ _ refl rest suffix
  --               (let @0 pf₁ : bs₁ ++ bs₂ ++ suffix ≡ pre₀ ++ suf₀
  --                    pf₁ = begin (bs₁ ++ bs₂ ++ suffix  ≡⟨ solve (++-monoid Dig) ⟩
  --                                (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
  --                                prefix ++ suffix       ≡⟨ ps≡ ⟩
  --                                xs                     ≡⟨ sym ps≡₀ ⟩
  --                                pre₀ ++ suf₀           ∎)
  --               in ++-cancelˡ bs₁ (trans pf₁ (cong (_++ suf₀) (NoNest.OIDSub (sym pf₁) oidₛ sub)))))
  --   return $ yes
  --     (success (pre₀ ++ pre₁) (r₀ + r₁)
  --       (begin
  --         (r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
  --         length pre₀ + r₁ ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
  --         length pre₀ + length pre₁ ≡⟨ sym (length-++ pre₀) ⟩
  --         length (pre₀ ++ pre₁) ∎))
  --       (Generic.mkOIDFieldₐ oidₛ oidₑ refl)
  --       suf₁
  --       (begin
  --         (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
  --         pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
  --         pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
  --         xs ∎))

  -- -- runParser parseOIDFieldₐ xs = do
  -- --   yes (success pre₀ r₀ r₀≡ oidₛ suf₀ ps≡₀) ← runParser parseOIDSub xs
  -- --     where no ¬parse → do
  -- --       tell here'
  -- --       return ∘ no $ ‼ λ where
  -- --         (success prefix read read≡ (Generic.cons {bs₁}{bs₂} sub rest bs≡) suffix ps≡₀) →
  -- --           contradiction
  -- --             (success _ (length bs₁) refl sub (bs₂ ++ suffix) (begin
  -- --               bs₁ ++ bs₂ ++ suffix   ≡⟨ solve (++-monoid Dig) ⟩
  -- --               (bs₁ ++ bs₂) ++ suffix ≡⟨ cong (_++ suffix) (sym bs≡) ⟩
  -- --               prefix ++ suffix       ≡⟨ ps≡₀ ⟩
  -- --               xs                     ∎))
  -- --             ¬parse
  -- --   -- yes (success pre₁ r₁ r₁≡ oidₑ suf₁ ps≡₁) ← runParser parseOIDField suf₀
  -- --   --   where no ¬parse → {!!}
  -- --   {!!}

