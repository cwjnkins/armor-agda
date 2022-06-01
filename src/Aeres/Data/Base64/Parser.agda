{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64.TCB
open import Aeres.Data.Base64.Properties
open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties

module Aeres.Data.Base64.Parser where

open Base256
open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Parser      Char
module Props = Aeres.Grammar.Properties Char

module parseBase64 where
  hereChar = "parseBase64Char"

  open ≡-Reasoning

  parseBase64Char : Parser (Logging ∘ Dec) Base64Char
  parseBase64Char =
    parseEquivalent Base64Char.equiv
      (parseSigma' (Props.NonNesting.erased exactLength-nonnesting)
        (λ where
          {c ∷ []} (─ e@(mk×ₚ self (─ refl) refl)) →
            case c ∈? Base64.charset of λ where
              (no ¬c∈) →
                no λ where
                  (─ c∈ , snd) → contradiction c∈ ¬c∈
              (yes c∈) → yes ((─ c∈) , self))
          (λ where
            {bs} (─ mk×ₚ self (─ len≡) refl) (─ mk×ₚ self (─ len≡') refl) (─ c∈ , singleton i i≡) →
              let @0 c : Char
                  c = lookupELS{bs} (mk×ₚ self (─ len≡) refl) (# 0)
                  bs≡ : Erased (bs ≡ [ c ])
                  bs≡ = ─ (case ((Σ[ xs ∈ List Char ] length xs ≡ 1) ∋ bs , len≡) ret (λ where (bs' , bsLen) → bs' ≡ [ lookupELS (mkELS 1 bs' bsLen) (# 0) ]) of λ where
                            (c ∷ [] , refl) → refl)
              in
              subst₀
                (λ xs → (@0 len≡“ : length xs ≡ 1) →
                  Exists─ (lookupELS (mkELS 1 xs len≡“) (# 0) ∈ Base64.charset)
                    λ (@0 c∈₁) → Singleton (Any.index c∈₁))
                (sym $ Erased.x bs≡)
                  (λ where refl → (─ c∈) , (singleton i i≡))
                  len≡')
        (parseErased (parseExactLengthString (tell $ hereChar String.++ ": underflow") 1)))

  parseBase64Str : ∀ n {n%4 : True (n % 4 ≟ 0)}  → Parser (Logging ∘ Dec) (ExactLength Base64Str n)
  runParser (parseBase64Str n) xs = {!!}

  -- runParser parseBase64Str [] =
  --   return (yes
  --     (success [] _ refl (mk64Str _ _ nil pad0 refl refl) _ refl))
  -- runParser parseBase64Str xs@(c ∷ xs') = do
  --   yes (success pre₁ r₁ r₁≡ (mkParseWhile pre₁' t allPre ¬t refl) suf₁ ps≡₁)
  --     ← return $ runParser (parseWhileₜ (_∈? Base64.charset)) xs
  --     where no ¬parse → {!!}
  --   let allPre' = (Base64Char.all2IList (uneraseDec allPre (All.all? (_∈? Base64.charset) _)))
  --   case (singleton (length pre₁' % 4) refl) of λ where
  --     (singleton 0 x≡) →
  --       return (yes
  --         (success pre₁' _ refl
  --           (mk64Str pre₁' [] {!!} pad0 {!!} (sym (++-identityʳ _)))
  --           (t ∷ suf₁) {!!}))
  --     (singleton 1 x≡) → {!!}
  --     (singleton 2 x≡) →
  --       case singleton suf₁ refl of λ where
  --         (singleton [] s≡) → {!!}
  --         (singleton (c' ∷ s) s≡) →
  --           case (t ≟ '=') ,′ (c' ≟ '=') of λ where
  --             (no ¬p , _) → {!!}
  --             (yes _ , no ¬p) → {!!}
  --             (yes refl , yes refl) →
  --               let @0 %4 : length (pre₁' ++ '=' ∷ [ '=' ]) % 4 ≡ 0
  --                   %4 = begin
  --                          length (pre₁' ++ '=' ∷ [ '=' ]) % 4 ≡⟨ cong (_% 4) (length-++ pre₁') ⟩
  --                          (length pre₁' + 2) % 4 ≡⟨ %-distribˡ-+ (length pre₁') _ _ ⟩
  --                          (length pre₁' % 4 + 2) % 4 ≡⟨ cong (λ x → (x + 2) % 4) (sym x≡) ⟩
  --                          (2 + 2) % 4 ≡⟨⟩
  --                          0 ∎
  --               in
  --               return (yes
  --                 (success (pre₁' ++ '=' ∷ [ '=' ]) _ refl
  --                   (mk64Str pre₁' ('=' ∷ [ '=' ] ) allPre' pad2
  --                     {!!} refl)
  --                   {!!} {!!}))
  --     (singleton 3 x≡) →
  --       case t ≟ '=' of λ where
  --         (no ¬t≡) →
  --           return ∘ no $ λ where
  --             (success ._ read read≡ (mk64Str s ._ str pad0 mult refl) suffix ps≡) →
  --               contradiction
  --                 (begin 0 ≡⟨ sym mult ⟩
  --                        length (s ++ []) % 4 ≡⟨ {!!} ⟩
  --                        {!!})
  --                 (0 ≢ 3 ∋ λ ())
  --             (success ._ read read≡ (mk64Str s ._ str pad1 mult refl) suffix ps≡) → {!!}
  --             (success ._ read read≡ (mk64Str s ._ str pad2 mult refl) suffix ps≡) → {!!}
  --         (yes refl) →
  --           let @0 %4 : length (pre₁' ++ [ '=' ]) % 4 ≡ 0
  --               %4 = begin
  --                      (length (pre₁' ++ [ '=' ]) % 4 ≡⟨ cong (_% 4) (length-++ pre₁') ⟩
  --                      (length pre₁' + 1) % 4 ≡⟨ %-distribˡ-+ (length pre₁') 1 4 ⟩
  --                      ((length pre₁' % 4) + 1) % 4 ≡⟨ cong (λ x → (x + 1) % 4) (sym x≡) ⟩
  --                      (3 + 1) % 4 ≡⟨⟩
  --                      0 ∎)
  --           in
  --           return (yes
  --             (success (pre₁' ∷ʳ '=') _ refl
  --               (mk64Str pre₁' [ '=' ] allPre' pad1 %4 refl)
  --               suf₁ ps≡₁))
  --     (singleton (suc (suc (suc (suc n)))) x≡) →
  --       contradiction (m%n<n (length pre₁') 3) (subst (λ x → ¬ x < 4) x≡ λ where
  --         (s≤s (s≤s (s≤s (s≤s ())))))

  --     -- Base64Str.equiv
  --     -- (parse×Dec {!!} (tell "parseBase64Char: underflow") p (λ _ → _ ≟ _))
  --   -- where
  --   -- p : Parser (Logging ∘ Dec) (&ₚ (IList Base64Char) Pad)
  --   -- runParser p [] =
  --   --   return (yes
  --   --     (success [] _ refl (mk&ₚ nil pad0 refl) _ refl))
  --   -- runParser p (c ∷ xs) =
  --   --   case c ∈? Base64.charset of λ where
  --   --     x → {!!}
