{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.PolicyQualifierInfo
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.CertPolFields where

open Base256

module parseCertPolFields where
  here' = "parseCertPolFields"

  open ≡-Reasoning

  parsePolicyInformationFields : ∀ n → Parser _ (Logging ∘ Dec) (ExactLength _ X509.PolicyInformationFields n)
  runParser (parsePolicyInformationFields n) xs = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ v₀ v₀Len refl) suf₀ ps≡₀) ←
      runParser (parse≤ _ n parseOID Props.TLV.nonnesting ((tell $ here' String.++ ": overflow"))) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (X509.mkPolicyInformationFields{pid = pid}{pqls} cpid cpqls refl) sndₚ₁ refl) suffix ps≡) →
            contradiction
              (success pid _ refl (mk×ₚ cpid (≤-trans (Lemmas.length-++-≤₁ pid pqls) (Lemmas.≡⇒≤ sndₚ₁)) refl) (pqls ++ suffix)
                (begin (pid ++ pqls ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                       (pid ++ pqls) ++ suffix ≡⟨ ps≡ ⟩
                       xs ∎)))
              ¬parse
    case <-cmp r₀ n of λ where
      (tri> _ _ n<r₀) → contradiction (subst (λ x → x ≤ n) (sym r₀≡) v₀Len) (<⇒≱ n<r₀)
      (tri≈ _ n≡r₀ _) →
        return (yes
          (success pre₀ r₀ r₀≡
            (mk×ₚ (X509.mkPolicyInformationFields v₀ none (sym $ ++-identityʳ pre₀))
              (trans₀ (sym r₀≡) n≡r₀) refl)
            suf₀ ps≡₀))
      (tri< r₀<n _ _) → do
        yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ v₁Len refl) suf₁ ps≡₁)
          ← runParser (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow") parsePolicyQualifiersSeq (n - r₀)) suf₀
          where no ¬parse → do
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (X509.mkPolicyInformationFields{pid = pid}{pqls} cpid none refl) sndₚ₁ refl) suffix ps≡) → ‼
                let @0 ps≡' : pid ++ suffix ≡ pre₀ ++ suf₀
                    ps≡' = (begin pid ++ suffix ≡⟨ cong (_++ suffix) (sym (++-identityʳ pid)) ⟩
                                  (pid ++ []) ++ suffix ≡⟨ ps≡ ⟩
                                  xs ≡⟨ sym ps≡₀ ⟩
                                  pre₀ ++ suf₀ ∎)
                    @0 pid≡ : pid ≡ pre₀
                    pid≡ = TLV.nonnesting ps≡' cpid v₀
                in
                contradiction
                  (begin (r₀ ≡⟨ r₀≡ ⟩
                         length pre₀ ≡⟨ cong length (sym pid≡) ⟩
                         length pid ≡⟨ cong length (sym (++-identityʳ pid)) ⟩
                         length (pid ++ []) ≡⟨ sndₚ₁ ⟩
                         n ∎))
                  (<⇒≢ r₀<n)
              (success prefix read read≡ (mk×ₚ (X509.mkPolicyInformationFields{pid = pid}{pqls} cpid (some cpqls) refl) sndₚ₁ refl) suffix ps≡) → ‼
                let @0 ps≡' : pid ++ pqls ++ suffix ≡ pre₀ ++ suf₀
                    ps≡' = (begin pid ++ pqls ++ suffix ≡⟨ solve (++-monoid Dig) ⟩
                                  (pid ++ pqls) ++ suffix ≡⟨ ps≡ ⟩
                                  xs ≡⟨ sym ps≡₀ ⟩
                                  pre₀ ++ suf₀ ∎)
                    @0 pid≡ : pid ≡ pre₀
                    pid≡ = TLV.nonnesting ps≡' cpid v₀
                in
                contradiction
                  (success _ _ refl
                    (mk×ₚ cpqls
                      (‼ (begin length pqls ≡⟨ sym (m+n∸m≡n (length pid) (length pqls)) ⟩
                                length pid + length pqls - length pid ≡⟨ cong (_∸ length pid) (sym (length-++ pid)) ⟩
                                length (pid ++ pqls) - length pid ≡⟨ cong (_∸ length pid) sndₚ₁ ⟩
                                n - length pid ≡⟨ cong ((n -_) ∘ length) pid≡ ⟩
                                n - length pre₀ ≡⟨ cong (n -_) (sym r₀≡) ⟩
                                n - r₀ ∎))
                      refl)
                    suffix
                    (Lemmas.++-cancel≡ˡ _ _ pid≡ ps≡'))
                  ¬parse
        return (yes
          (success (pre₀ ++ pre₁) (r₀ + r₁)
            (begin (r₀ + r₁ ≡⟨ cong₂ _+_ r₀≡ r₁≡ ⟩
                   length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
                   length (pre₀ ++ pre₁) ∎))
            (mk×ₚ (X509.mkPolicyInformationFields v₀ (some v₁ ) refl)
              (‼ (begin length (pre₀ ++ pre₁) ≡⟨ length-++ pre₀ ⟩
                        length pre₀ + length pre₁ ≡⟨ (sym $ cong (_+ length pre₁) r₀≡) ⟩
                        r₀ + length pre₁ ≡⟨ cong (r₀ +_) v₁Len ⟩
                        r₀ + (n - r₀) ≡⟨ m+[n∸m]≡n (<⇒≤ r₀<n) ⟩
                        n ∎))
              refl)
            suf₁
            (begin (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Dig) ⟩
                   pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
                   pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
                   xs ∎)))

  parsePolicyInformation : Parser _ (Logging ∘ Dec) X509.PolicyInformation
  parsePolicyInformation =
    parseTLV _ "policy info" _ parsePolicyInformationFields

  parseCertPolFieldsSeq : Parser _ (Logging ∘ Dec) X509.CertPolFieldsSeq
  parseCertPolFieldsSeq = parseSeq "policy info" _ Props.TLV.nonempty Props.TLV.nonnesting parsePolicyInformation

  parseCertPolFields : Parser _ (Logging ∘ Dec) X509.CertPolFields
  parseCertPolFields =
    parseTLV _ "cert. policy" _
      (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": overflow") parseCertPolFieldsSeq)

open parseCertPolFields public using (parsePolicyInformation ; parseCertPolFieldsSeq ; parseCertPolFields)