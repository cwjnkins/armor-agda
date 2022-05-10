{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.PEM.TCB
open import Aeres.Data.PEM.Properties
import      Aeres.Grammar.IList
import      Aeres.Grammar.Sum
import      Aeres.Grammar.Parser
open import Aeres.Prelude

open Aeres.Grammar.IList  Char
open Aeres.Grammar.Sum    Char
open Aeres.Grammar.Parser Char

module Aeres.Data.PEM.Parser where

module parsePEM where

  open ≡-Reasoning
  hereLine = "parseCertLine"

  parseCertLine : Parser (Logging ∘ Dec) λ bs → ∃[ n ] CertLine n bs
  runParser parseCertLine xs =
    case runParser (parseWhileₜ (_∈? Base64.charset)) xs of λ where
      (no ¬p) → do
        tell $ hereLine String.++ ": underflow"
        return ∘ no $ λ where
          (success prefix read read≡ (n , mkCertLine line valid64 len≡ refl) suffix ps≡) →
            contradiction
             (success (line ∷ʳ '\r') _ refl
               (mkParseWhile line '\r' valid64 (fromWitness{Q = _ ∈? _}) refl)
               ('\n' ∷ suffix)
               (begin
                 (line ++ [ '\r' ]) ++ ('\n' ∷ suffix) ≡⟨ ++-assoc line [ '\r' ] _ ⟩
                 line ++ (certEOL ++ suffix) ≡⟨ (sym $ ++-assoc line certEOL _) ⟩
                 (line ++ certEOL) ++ suffix ≡⟨ ps≡ ⟩
                 xs ∎))
             ¬p
      (yes (success ._ r₁ r₁≡ w@(mkParseWhile pre₁' term allPre₁ ¬term refl) [] ps≡₁)) → do
        tell $ hereLine String.++ ": missing ending newline"
        return ∘ no $ λ where
          (success prefix read read≡ (n , mkCertLine line valid64 len≡ refl) suffix ps≡) → ‼
            let @0 ps≡' : (line ++ [ '\r' ]) ++ [ '\n' ] ++ suffix ≡ (pre₁' ∷ʳ term) ++ []
                ps≡' = begin
                  (line ++ [ '\r' ]) ++ [ '\n' ] ++ suffix ≡⟨ ++-assoc line [ '\r' ] _ ⟩
                  line ++ certEOL ++ suffix ≡⟨ (sym $ ++-assoc line certEOL _) ⟩
                  (line ++ certEOL) ++ suffix ≡⟨ ps≡ ⟩
                  xs ≡⟨ sym ps≡₁ ⟩
                  pre₁' ∷ʳ term ++ [] ∎
                @0 line≡ : line ++ [ '\r' ] ≡ pre₁' ++ [ term ]
                line≡ = Properties.nonnesting ps≡' (mkParseWhile _ _ valid64 (toWitnessFalse {Q = _ ∈? _} tt) refl) w
            in
            contradiction ([ '\n' ] ++ suffix ≡ [] ∋ Lemmas.++-cancel≡ˡ _ _ line≡ ps≡' ) λ ()
      (yes (success ._ r₁ r₁≡ w@(mkParseWhile pre₁ term allPre₁ ¬term refl) (s ∷ suf₁) ps≡)) →
        case (term ≟ '\r') ,′ (s ≟ '\n') of λ where
          (no t≠\r , _) →
            return ∘ no $ λ where
              (success ._ read read≡ (n , mkCertLine line valid64 len≡ refl) suffix refl) → ‼
                let @0 ps≡' : (pre₁ ++ [ term ]) ++ (s ∷ suf₁) ≡ (line ++ [ '\r' ]) ++ '\n' ∷ suffix
                    ps≡' = begin
                      (pre₁ ++ [ term ]) ++ (s ∷ suf₁) ≡⟨ ps≡ ⟩
                      (line ++ certEOL) ++ suffix ≡⟨ ++-assoc line certEOL _ ⟩
                      line ++ certEOL ++ suffix ≡⟨ (sym $ ++-assoc line [ '\r' ] _) ⟩
                      (line ++ [ '\r' ]) ++ '\n' ∷ suffix ∎


                    @0 pre₁≡ : pre₁ ++ [ term ] ≡ line ++ [ '\r' ]
                    pre₁≡ = Properties.nonnesting ps≡' w
                              (mkParseWhile _ _ valid64 (toWitnessFalse{Q = _ ∈? _} tt) refl)
                in    
                contradiction (proj₂ $ ∷ʳ-injective _ _ pre₁≡) t≠\r
          (_ , (no  s≠\n)) →
            return ∘ no $ λ where
              (success ._ read read≡ (n , mkCertLine line valid64 len≡ refl) suffix refl) → ‼
                let @0 ps≡' : (pre₁ ++ [ term ]) ++ (s ∷ suf₁) ≡ (line ++ [ '\r' ]) ++ '\n' ∷ suffix
                    ps≡' = begin
                      (pre₁ ++ [ term ]) ++ (s ∷ suf₁) ≡⟨ ps≡ ⟩
                      (line ++ certEOL) ++ suffix ≡⟨ ++-assoc line certEOL _ ⟩
                      line ++ certEOL ++ suffix ≡⟨ (sym $ ++-assoc line [ '\r' ] _) ⟩
                      (line ++ [ '\r' ]) ++ '\n' ∷ suffix ∎


                    @0 pre₁≡ : pre₁ ++ [ term ] ≡ line ++ [ '\r' ]
                    pre₁≡ = Properties.nonnesting ps≡' w
                              (mkParseWhile _ _ valid64 (toWitnessFalse{Q = _ ∈? _} tt) refl)
                in    
                contradiction (∷-injectiveˡ (Lemmas.++-cancel≡ˡ _ _ pre₁≡ ps≡')) s≠\n
          (yes refl , yes refl) →
            return (yes
              (success
                (pre₁ ++ '\r' ∷ [ '\n' ]) (r₁ + 1)
                (begin (r₁ + 1 ≡⟨ cong (_+ 1) r₁≡ ⟩
                       length (pre₁ ++ [ '\r' ]) + length [ '\n' ] ≡⟨ (sym $ length-++ (pre₁ ++ [ '\r' ]) {[ '\n' ]}) ⟩
                       length (pre₁ ∷ʳ '\r' ++ [ '\n' ]) ≡⟨ cong length (++-assoc pre₁ [ '\r' ] _) ⟩
                       _ ∎))
                ((length pre₁) , (mkCertLine pre₁ allPre₁ refl refl))
                suf₁
                (begin
                  (pre₁ ++ '\r' ∷ [ '\n' ]) ++ suf₁       ≡⟨ cong (_++ suf₁) (sym $ ++-assoc pre₁ _ _) ⟩
                  ((pre₁ ++ [ '\r']) ++ [ '\n' ]) ++ suf₁ ≡⟨ ++-assoc _ [ '\n' ] suf₁ ⟩
                  (pre₁ ++ [ '\r' ]) ++ '\n' ∷ suf₁       ≡⟨ ps≡ ⟩
                  xs ∎)))

