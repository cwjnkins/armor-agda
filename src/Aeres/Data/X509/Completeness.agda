{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Cert
import      Aeres.Data.X509.Properties as Props
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Completeness where

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Parser      Dig

abstract
  parseCert' : Parser (Logging ∘ Dec) X509.Cert
  parseCert' = parseCert

True_And_ : {P : Set} → Dec P → (P → Set) → Set
True_And_ (yes pf) Q = Q pf
True_And_ (no ¬pf) Q = ⊥

UniqueParse : Set
UniqueParse = ∀ {bs} → Unique (Success X509.Cert bs)

@0 uniqueParse : UniqueParse
uniqueParse (success prefix read read≡ value suffix ps≡) (success prefix₁ read₁ read≡₁ value₁ suffix₁ ps≡₁) =
  subst₂ (λ p s → ∀ r≡ v (ps≡ : p ++ s ≡ _) → _ ≡ success p read₁ r≡ v s ps≡)
    prefix≡ suffix≡
    (λ r≡ v ps≡₂ →
      subst₂ (λ r v' → (r≡' : r ≡ _) → _ ≡ success prefix r r≡' v' suffix ps≡₂)
        read≡' (Props.TLV.unambiguous Props.CertFields.unambiguous value v)
        (λ r≡' →
          subst₂ (λ r≡“ ps≡“ → _ ≡ success prefix read r≡“ value suffix ps≡“)
            (≡-unique read≡ r≡') (≡-unique ps≡ ps≡₂)
            refl)
        r≡)
    read≡₁ value₁ ps≡₁
  where
  @0 prefix≡ : prefix ≡ prefix₁
  prefix≡ = Props.TLV.nonnesting (trans₀ ps≡ (sym ps≡₁)) value value₁

  @0 read≡' : read ≡ read₁
  read≡' = trans₀ read≡ (trans₀ (cong length prefix≡) (sym read≡₁))

  @0 suffix≡ : suffix ≡ suffix₁
  suffix≡ = Lemmas.++-cancel≡ˡ _ _ prefix≡ (trans₀ ps≡ (sym ps≡₁))

completeness : ∀ {bs} → (cert : Success X509.Cert bs)
               → True (Logging.val (runParser parseCert' bs)) And (cert ≡_)
completeness{bs} cert
  with Logging.val $ runParser parseCert' bs
... | (yes s) = ‼ uniqueParse cert s
... | no ¬cert = contradiction cert ¬cert
