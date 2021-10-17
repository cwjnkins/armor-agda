{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.AKIFields where

open Base256

module parseAKIFields where
  module Here where
    AKIKeyId = "AKI key id"
    AKIAuthCertIssuer = "AKI auth. cert. issuer"
    AKIAuthCertSN = "AKI auth. cert. SN"
    AKI = "AKI"

  open ≡-Reasoning

  parseAKIKeyId : Parser Dig (Logging ∘ Dec) X509.AKIKeyId
  parseAKIKeyId = parseTLV _ Here.AKIKeyId _ parseOctetstringValue

  parseAKIAuthCertIssuer : Parser Dig (Logging ∘ Dec) X509.AKIAuthCertIssuer
  parseAKIAuthCertIssuer = parseTLV _ Here.AKIAuthCertIssuer _ parseGeneralNamesElems

  parseAKIAuthCertSN : Parser Dig (Logging ∘ Dec) X509.AKIAuthCertSN
  parseAKIAuthCertSN = parseTLV _ Here.AKIAuthCertSN _ parseIntValue

  -- NOTE: The proof effort caught a bug in my original implementation :)
  -- (Try to parse all, then check lengths)
  parseAKIFieldsSeqFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.AKIFieldsSeqFields n)
  runParser (parseAKIFieldsSeqFields zero) xs =
    return (yes (success [] _ refl (mk×ₚ (X509.mkAKIFieldsSeqFields none none none refl) refl refl) xs refl))
  runParser (parseAKIFieldsSeqFields n'@(suc n)) xs = do
    x₁ ← runParser (parse≤ _ n' parseAKIKeyId Props.TLV.nonnesting (return (Level.lift tt))) xs
    case <-cmp n' (readDecSuccess _ x₁) of λ where
      (tri< n'<r₁ _ _) → contradiction n'<r₁ (check₁ x₁)
      (tri≈ _ n'≡r₁ _) → return (yes (ret₁ x₁ n'≡r₁))
      (tri> _ _ r₁<n') → do
        let n“ = n' - (readDecSuccess _ x₁)
        x₂ ← runParser (parse≤ _ n“ parseAKIAuthCertIssuer Props.TLV.nonnesting (return (Level.lift tt))) (suffixDecSuccess _ x₁)
        case <-cmp n“ (readDecSuccess _ x₂) of λ where
          (tri< n“<r₂ _ _) → contradiction n“<r₂ (check₂ x₁ r₁<n' self x₂)
          (tri≈ _ n“≡r₂ _) → return (yes (ret₂ x₁ r₁<n' self x₂ n“≡r₂))
          (tri> _ _ r₂<n“) → do
            let n‴ = n“ - (readDecSuccess _ x₂)
            x₃ ← runParser (parse≤ _ n‴ parseAKIAuthCertSN Props.TLV.nonnesting (return (Level.lift tt))) (suffixDecSuccess _ x₂)
            case <-cmp n‴ (readDecSuccess _ x₃) of λ where
              (tri< n‴<r₃ _ _) → contradiction n‴<r₃ (check₃ x₁ r₁<n' self x₂ r₂<n“ self x₃)
              (tri> _ _ r₃<n‴) → do
                return ∘ no $ ‼ underflow x₁ r₁<n' self x₂ r₂<n“ self x₃ r₃<n‴
              (tri≈ _ n‴≡r₃ _) → {!!}
    where
    Res₁ : (A : (@0 _ : List Dig) → Set) → Set
    Res₁ A = Dec (Success Dig (_×ₚ_ _ A ((_≤ n') ∘ length)) xs)

    Res₂ : ∀ {A₁} (A₂ : (@0 _ : List Dig) → Set) → (x₁ : Res₁ A₁) → ℕ → Set
    Res₂ A₂ x₁ n“ = Dec (Success Dig (_×ₚ_ _ A₂ ((_≤ n“) ∘ length)) (suffixDecSuccess _ x₁))

    Res₃ : ∀ {A₁ A₂} (A₃ : (@0 _ : List Dig) → Set) → (x₁ : Res₁ A₁) (n“ : ℕ) (x₂ : Res₂ A₂ x₁ n“) → ℕ → Set
    Res₃ A₃ x₁ n“ x₂ n‴ = Dec (Success _ (_×ₚ_ _ A₃ ((_≤ n‴) ∘ length)) (suffixDecSuccess _ x₂))

    check₁ : ∀ {@0 A} → (x₁ : Res₁ A) → ¬ n' < readDecSuccess _ x₁
    check₁ (no _) ()
    check₁ (yes (success prefix read read≡ (mk×ₚ akiId akiLen refl) suffix ps≡)) n'<r₁ =
      contradiction (≤-trans (Lemmas.≡⇒≤ read≡) akiLen) (<⇒≱ n'<r₁)

    ret₁ : (x₁ : Res₁ X509.AKIKeyId) → n' ≡ readDecSuccess _ x₁ → Success _ (ExactLength _ X509.AKIFieldsSeqFields n') xs
    ret₁ (no ¬parse) ()
    ret₁ (yes (success prefix ._ read≡ (mk×ₚ akiKeyId akiKeyIdLen refl) suffix ps≡)) refl =
      success prefix _ read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some akiKeyId) none none refl) (trans₀ (cong length (++-identityʳ prefix)) (sym read≡)) (++-identityʳ _ )) suffix ps≡

    -- `check₂` is given more information than it needs (e.g., the value of `n“` in terms of `n'` is never used)
    check₂ : ∀ {@0 A₁ A₂} (x₁ : Res₁ A₁) (r₁<n' : readDecSuccess _ x₁ < n') (n“ : Singleton (n' - readDecSuccess _ x₁)) (x₂ : Res₂ A₂ x₁ (Singleton.x n“))
             → ¬ Singleton.x n“ < readDecSuccess _ x₂
    check₂ (no _) _ (singleton ._ refl) x₂ n“<r₂ = check₁ x₂ n“<r₂
    check₂ (yes x₁) _ (singleton n“ n“≡) (no _) ()
    check₂ (yes (success _ r₁ read≡ (mk×ₚ fstₚ₁ r₁≤n' refl) suffix ps≡)) r₁<n' (singleton n“ n“≡) (yes (success _ r₂ read≡₁ (mk×ₚ fstₚ₂ r₂≤n“ refl) suffix₁ ps≡₁)) n“<r₂ =
      contradiction (≤-trans (Lemmas.≡⇒≤ read≡₁) r₂≤n“) (<⇒≱ n“<r₂)

    ret₂ : (x₁ : Res₁ X509.AKIKeyId) → n' > readDecSuccess _ x₁
           → (n“ : Singleton (n' - readDecSuccess _ x₁)) (x₂ : Res₂ X509.AKIAuthCertIssuer x₁ (Singleton.x n“))
           → Singleton.x n“ ≡ readDecSuccess _ x₂
           → Success _ (ExactLength _ X509.AKIFieldsSeqFields n') xs
    ret₂ (no _) _ (singleton n“@._ refl) (no _) ()
    ret₂ (no _) _ (singleton .n' refl) (yes (success prefix read read≡ (mk×ₚ akici akiciLen refl) suffix ps≡)) n“≡r₂ =
      success prefix _ read≡
        (mk×ₚ (X509.mkAKIFieldsSeqFields none (some akici) none (sym $ ++-identityʳ prefix))
          (trans₀ (sym read≡) (sym n“≡r₂)) refl)
        suffix ps≡
    ret₂ (yes (success prefix read read≡ (mk×ₚ akiID akiLen refl) suffix ps≡)) n'>r₁ (singleton .0 n“≡) (no _) refl =
      contradiction (m∸n≡0⇒m≤n (sym n“≡)) (<⇒≱ n'>r₁)
    ret₂ (yes (success pre₁ r₁ r₁≡ (mk×ₚ akiID akiIdLen refl) suf₁ ps≡₁)) n'>r₁ (singleton .r₂ n“≡) (yes (success pre₂ r₂ r₂≡ (mk×ₚ akiCI akiCILen refl) suf₂ ps≡₂)) refl =
      success (pre₁ ++ pre₂) (r₁ + r₂) r₁+r₂≡
        (mk×ₚ (X509.mkAKIFieldsSeqFields (some akiID) (some akiCI) none (pre₁ ++ pre₂ ≡ pre₁ ++ pre₂ ++ [] ∋ solve (++-monoid Dig)))
          (‼ (begin length (pre₁ ++ pre₂) ≡⟨ sym r₁+r₂≡ ⟩
                    r₁ + r₂               ≡⟨ cong (r₁ +_) n“≡ ⟩
                    r₁ + (n' - r₁)        ≡⟨ (sym $ +-∸-assoc r₁ (<⇒≤ n'>r₁)) ⟩
                    (r₁ + n') - r₁        ≡⟨ cong (_∸ r₁) (+-comm r₁ _) ⟩
                    (n' + r₁) - r₁        ≡⟨ +-∸-assoc n'{r₁} ≤-refl ⟩
                    n' + (r₁ - r₁)        ≡⟨ cong (n' +_) (n∸n≡0 r₁) ⟩
                    n' + 0                ≡⟨ +-identityʳ _ ⟩
                    n'                    ∎))
          refl)
        suf₂ (begin (pre₁ ++ pre₂) ++ suf₂ ≡⟨ solve (++-monoid Dig) ⟩
                    pre₁ ++ pre₂ ++ suf₂   ≡⟨ cong (pre₁ ++_) ps≡₂ ⟩
                    pre₁ ++ suf₁           ≡⟨ ps≡₁ ⟩
                    xs                     ∎)
      where
      open ≡-Reasoning
      @0 r₁+r₂≡ : r₁ + r₂ ≡ length (pre₁ ++ pre₂)
      r₁+r₂≡ = begin
        r₁ + r₂ ≡⟨ ‼ (cong₂ _+_ r₁≡ r₂≡) ⟩
        length pre₁ + length pre₂ ≡⟨ (sym $ length-++ pre₁) ⟩
        length (pre₁ ++ pre₂) ∎

    -- `check₃` is given more information than it needs (e.g., the value of `n‴` in terms of `n'` is never used)
    check₃ : ∀ {@0 A₁ A₂ A₃} (x₁ : Res₁ A₁) (r₁<n' : readDecSuccess _ x₁ < n') (n“ : Singleton (n' - readDecSuccess _ x₁))
             → (x₂ : Res₂ A₂ x₁ (Singleton.x n“)) (r₂<n“ : readDecSuccess _ x₂ < Singleton.x n“) (n‴ : Singleton (Singleton.x n“ - readDecSuccess _ x₂))
             → (x₃ : Res₃ A₃ x₁ (Singleton.x n“) x₂ (Singleton.x n‴)) → ¬ Singleton.x n‴ < readDecSuccess _ x₃
    check₃ (no _) r₁<n' (singleton n“@._ refl) x₂ r₂<n“ n‴ x₃ n‴<r₃ = check₂ x₂ r₂<n“ n‴ x₃ n‴<r₃
    check₃ (yes x₁) r₁<n' n“ (no _) r₂<n“ (self {n‴@._}) x₃ n‴<r₃ = check₂ (yes x₁) r₁<n' n“ x₃ n‴<r₃
    check₃ (yes x₁) r₁<n' n“ (yes x₂) r₂<n“ n‴ (no _) ()
    check₃ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) r₁<n' n“ (yes (success pre₂ r₂ r₂≡ v₂ suf₂ ps≡₂)) r₂<n“ (self {n‴@._}) (yes (success pre₃ r₃ r₃≡ (mk×ₚ v₃ r₃≤n‴ refl) suf₃ ps≡₃)) n‴<r₃ =
      contradiction (≤-trans (Lemmas.≡⇒≤ r₃≡) r₃≤n‴) (<⇒≱ n‴<r₃)

    @0 underflow : ∀ (x₁ : Res₁ X509.AKIKeyId) (r₁<n' : readDecSuccess _ x₁ < n') (n“ : Singleton (n' - readDecSuccess _ x₁))
                   → (x₂ : Res₂ X509.AKIAuthCertIssuer x₁ (Singleton.x n“)) (r₂<n“ : readDecSuccess _ x₂ < Singleton.x n“) (n‴ : Singleton (Singleton.x n“ - readDecSuccess _ x₂))
                   → (x₃ : Res₃ X509.AKIAuthCertSN x₁ (Singleton.x n“) x₂ (Singleton.x n‴)) → readDecSuccess _ x₃ < Singleton.x n‴  → ¬ Success _ (ExactLength _ X509.AKIFieldsSeqFields n') xs
    underflow (no ¬akeyid) r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} (some akeyid) authcertiss authcertsn refl) n'≡ refl) suffix ps≡) =
      contradiction
        (success _ _ refl (mk×ₚ akeyid (≤-trans (Lemmas.length-++-≤₁ akid (ci ++ csn)) (Lemmas.≡⇒≤ n'≡)) refl) (ci ++ csn ++ suffix) (trans (akid ++ ci ++ csn ++ suffix ≡ (akid ++ ci ++ csn) ++ suffix ∋ solve (++-monoid Dig)) ps≡))
        ¬akeyid
    underflow (yes (success pre₁ r₁ r₁≡ (mk×ₚ akeyid' _ refl) suf₁ ps≡₁)) r₁<n' self (no ¬authcertiss) r₂<n‴ self x₃ r₃<n“ (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} (some akeyid) (some authcertiss) authcertsn refl) n'≡ refl) suffix ps≡) = ‼
      let @0 ps≡' : akid ++ ci ++ csn ++ suffix ≡ pre₁ ++ suf₁
          ps≡' = begin akid ++ ci ++ csn ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                       (akid ++ ci ++ csn) ++ suffix ≡⟨ ps≡ ⟩
                       xs ≡⟨ sym ps≡₁ ⟩
                       pre₁ ++ suf₁ ∎

          @0 akid≡ : akid ≡ pre₁
          akid≡ = TLV.nonnesting ps≡' akeyid akeyid'

          @0 n'-r₁≡ : n' - r₁ ≡ length (ci ++ csn)
          n'-r₁≡ = begin
            n' - r₁ ≡⟨ cong (n' -_) r₁≡ ⟩
            n' - length pre₁ ≡⟨ cong (_- length pre₁) (sym n'≡) ⟩
            length (akid ++ ci ++ csn) - length pre₁ ≡⟨ cong (_∸ length pre₁) (length-++ akid) ⟩
            (length akid + length (ci ++ csn)) - length pre₁ ≡⟨ cong _ akid≡ ⟩
            (length pre₁ + length (ci ++ csn)) - length pre₁ ≡⟨ cong (_∸ length pre₁) (+-comm (length pre₁) _) ⟩
            (length (ci ++ csn) + length pre₁) - length pre₁ ≡⟨ +-∸-assoc (length (ci ++ csn)){length pre₁} ≤-refl ⟩
            length (ci ++ csn) + (length pre₁ - length pre₁) ≡⟨ cong (length (ci ++ csn) +_) (n∸n≡0 (length pre₁)) ⟩
            length (ci ++ csn) + 0 ≡⟨ +-identityʳ _ ⟩
            length (ci ++ csn) ∎
      in
      contradiction
        (success _ _ refl (mk×ₚ authcertiss (≤-trans (Lemmas.length-++-≤₁ ci _) (Lemmas.≡⇒≤ $ sym n'-r₁≡)) refl) (csn ++ suffix) (Lemmas.++-cancel≡ˡ _ _ akid≡ ps≡'))
        ¬authcertiss
    underflow (yes akeyid') r₁<n' n“ (yes authcertiss') r₂<n“ n‴ x₃ r₃<n‴ (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some akeyid) (some authcertiss) authcertsn refl) n'≡ refl) suffix ps≡) = {!!}
    underflow (yes akeyid') r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some akeyid) none authcertsn refl) n'≡ refl) suffix ps≡) = {!!}
    underflow x₁ r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success prefix read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none authcertiss authcertsn refl) n'≡ refl) suffix ps≡) = {!!}

    -- underflow (yes (success pre₁ r₁ r₁≡ (mk×ₚ akeyid akiIdLen refl) suf₁ ps≡₁)) r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} none none (some authcertsn) refl) read≡n' refl) suffix ps≡) =
    --   TLV.noconfusion (Tag.Eighty ≢ Tag.EightyTwo ∋ λ ()) (trans₀ ps≡₁ (sym ps≡)) akeyid authcertsn
    -- underflow (no _) r₁<n' n“ (yes (success pre₂ r₂ r₂≡ (mk×ₚ authcertiss akiIssLen refl) suf₂ ps≡₂)) r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} none none (some authcertsn) refl) read≡n' refl) suffix ps≡) =
    --   TLV.noconfusion (Tag.A1 ≢ Tag.EightyTwo ∋ λ ()) (trans₀ ps≡₂ (sym ps≡)) authcertiss authcertsn
    -- underflow (no _) _ self (no _) _ self (no ¬authcertsn) _ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} none none (some authcertsn) refl) read≡n' refl) suffix ps≡) =
    --   contradiction (success _ _ refl (mk×ₚ authcertsn (Lemmas.≡⇒≤ read≡n') refl) _ ps≡) ¬authcertsn
    -- underflow (no _) r₁<n' self (no _) r₂<n“ self (yes (success pre₃ r₃ r₃≡ (mk×ₚ authcertsn' _ refl) suf₃ ps≡₃)) r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} none none (some authcertsn) refl) read≡n' refl) suffix ps≡) =
    --   contradiction (trans (trans r₃≡ (cong length (TLV.nonnesting (trans ps≡₃ (sym ps≡)) authcertsn' authcertsn))) read≡n') (<⇒≢ r₃<n‴)
    -- underflow (no ¬akeyid) r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} (some akeyid) authcertiss authcertsn refl) read≡n' refl) suffix ps≡) = {!!}
    -- underflow (yes akeyid') r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} (some akeyid) authcertiss authcertsn refl) read≡n' refl) suffix ps≡) = {!!}
    -- underflow x₁ r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} none (some authcertiss) authcertsn refl) read≡n' refl) suffix ps≡) = {!!}

    -- underflow (yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ v₁Len refl) suf₁ ps≡₁)) r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none authcertiss authcertsn refl) bsLen refl) suffix ps≡) = {!!}
    -- underflow (no ¬aid) r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none       authcertiss authcertsn refl) bsLen refl) suffix ps≡) = {!!}
    -- underflow (no ¬aid) r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some aid) authcertiss authcertsn refl) bsLen refl) suffix ps≡) = {!!}
    -- underflow (yes aid') r₁<n' n“ x₂ r₂<n“ n‴ x₃ r₃<n‴ (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields (some aid) authcertiss authcertsn refl) bsLen refl) suffix ps≡) = {!!}

    -- yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ v₀Len refl) suf₀ ps≡₀)
    --   ← runParser (parse≤ _ n' parseAKIKeyId Props.TLV.nonnesting (tell $ Here.AKI String.++ ": underflow")) xs
    --   where no ¬parse → do
    --     return ∘ no $ λ where
    --       (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} (some x) authcertiss authcertsn refl) akiLen refl) suffix ps≡) →
    --         contradiction
    --           (success _ _ refl
    --             (mk×ₚ x (≤-trans (Lemmas.length-++-≤₁ akid (ci ++ csn)) (Lemmas.≡⇒≤ akiLen)) refl) (ci ++ csn ++ suffix)
    --             (trans (akid ++ ci ++ csn ++ suffix ≡ (akid ++ ci ++ csn) ++ suffix ∋ solve (++-monoid Dig)) ps≡))
    --           ¬parse
    --       (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none authcertiss authcertsn refl) akiLen refl) suffix ps≡) →
    --         contradiction
    --           (success {!!} {!!} {!!} {!!} {!!} {!!})
    --           ¬parse
    -- {!!}

--     x₁ ← runParser parseAKIKeyId xs
--     x₂ ← runParser parseAKIAuthCertIssuer (suffixDecSuccess _ x₁)
--     x₃ ← runParser parseAKIAuthCertSN (suffixDecSuccess _ x₂)
--     return (check x₁ x₂ x₃)
--     where
--     check : (x₁ : Dec (Success _ X509.AKIKeyId xs))
--             (x₂ : Dec (Success _ X509.AKIAuthCertIssuer (suffixDecSuccess Dig x₁)))
--             (x₃ : Dec (Success _ X509.AKIAuthCertSN (suffixDecSuccess Dig x₂)))
--             → Dec (Success _ (ExactLength _ X509.AKIFieldsSeqFields n) xs)
--     check x₁ x₂ x₃
--       with readDecSuccess _ x₁ + readDecSuccess _ x₂ + readDecSuccess _ x₃ in eq
--     ... | r
--       with x₁ | x₂ | x₃ | n ≟ r
--     ... | no  ¬1 | no  ¬2 | no  ¬3 | no  ¬4 =
--       no λ where
--         (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} (some x) authcertiss authcertsn refl) akiLen refl) suffix ps≡) →
--           contradiction
--             (success _ _ refl x (ci ++ csn ++ suffix) (trans (akid ++ ci ++ csn ++ suffix ≡ (akid ++ ci ++ csn) ++ suffix ∋ solve (++-monoid Dig)) ps≡))
--             ¬1
--         (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{ci = ci}{csn} none (some x) authcertsn refl) akiLen refl) suffix ps≡) →
--           contradiction
--             (success _ _ refl x (csn ++ suffix) (trans (ci ++ csn ++ suffix ≡ (ci ++ csn) ++ suffix ∋ solve (++-monoid Dig)) ps≡))
--             ¬2
--         (success .csn read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{csn = csn} none none (some x) refl) akiLen refl) suffix ps≡) →
--           contradiction
--             (success _ _ refl x suffix ps≡)
--             ¬3
--         (success .[] read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none none none refl) refl refl) suffix ps≡) →
--           contradiction eq ¬4
--     ... | no  ¬1 | no  ¬2 | no  ¬3 | yes ✓4 =
--       yes (success [] _ refl (mk×ₚ (X509.mkAKIFieldsSeqFields none none none refl) (trans eq (sym ✓4)) refl) xs refl)
--     ... | no  ¬1 | no  ¬2 | yes ✓3 | no  ¬4 =
--       no λ where
--         (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{akid = akid}{ci}{csn} (some x) authcertiss authcertsn refl) akiLen refl) suffix ps≡) →
--           contradiction
--             (success _ _ refl x (ci ++ csn ++ suffix) (trans (akid ++ ci ++ csn ++ suffix ≡ (akid ++ ci ++ csn) ++ suffix ∋ solve (++-monoid Dig)) ps≡))
--             ¬1
--         (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields{ci = ci}{csn} none (some x) authcertsn refl) akiLen refl) suffix ps≡) →
--           contradiction
--             (success _ _ refl x (csn ++ suffix) (trans (ci ++ csn ++ suffix ≡ (ci ++ csn) ++ suffix ∋ solve (++-monoid Dig)) ps≡))
--             ¬2
--         (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none none none refl) refl refl) suffix ps≡) →
--           {!!}
--         (success ._ read read≡ (mk×ₚ (X509.mkAKIFieldsSeqFields none none (some x) refl) akiLen refl) suffix ps≡) → {!!}
--     ... | no  ¬1 | no  ¬2 | yes ✓3 | yes ✓4 = {!!}
--     ... | no  ¬1 | yes ✓2 | no  ¬3 | no  ¬4 = {!!}
--     ... | no  ¬1 | yes ✓2 | no  ¬3 | yes ✓4 = {!!}
--     ... | no  ¬1 | yes ✓2 | yes ✓3 | no  ¬4 = {!!}
--     ... | no  ¬1 | yes ✓2 | yes ✓3 | yes ✓4 = {!!}
--     ... | yes ✓1 | no  ¬2 | no  ¬3 | no  ¬4 = {!!}
--     ... | yes ✓1 | no  ¬2 | no  ¬3 | yes ✓4 = {!!}
--     ... | yes ✓1 | no  ¬2 | yes ✓3 | no  ¬4 = {!!}
--     ... | yes ✓1 | no  ¬2 | yes ✓3 | yes ✓4 = {!!}
--     ... | yes ✓1 | yes ✓2 | no  ¬3 | no  ¬4 = {!!}
--     ... | yes ✓1 | yes ✓2 | no  ¬3 | yes ✓4 = {!!}
--     ... | yes ✓1 | yes ✓2 | yes ✓3 | no  ¬4 = {!!}
--     ... | yes ✓1 | yes ✓2 | yes ✓3 | yes ✓4 = {!!}


-- --   parseAKIFields = parseTLV Tag.Integer "Int" Generic.IntegerValue p
-- --     where
-- --     p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.IntegerValue n)
-- --     runParser (p n) xs = do
-- --       yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton v₀ refl) v₀Len refl) suf₀ ps≡₀)
-- --         ← runParser (parseN Dig n (tell $ here' String.++ ": underflow reading it")) xs
-- --         where no ¬parse → do
-- --           return ∘ no $ λ where
-- --             (success prefix read read≡ (mk×ₚ (Generic.mkIntegerValue val bs≡₁) sndₚ refl) suffix ps≡) →
-- --               contradiction
-- --                 (success prefix _ read≡
-- --                   (mk×ₚ (singleton prefix refl) sndₚ refl)
-- --                   suffix ps≡)
-- --                 ¬parse
-- --       return (yes
-- --         (success pre₀ _ r₀≡
-- --           (mk×ₚ (Generic.mkIntegerValue (twosComplement v₀) refl) v₀Len refl)
-- --           suf₀ ps≡₀))

-- -- open parseAKIFields public using (parseAKIFields)
