{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64.TCB
open import Aeres.Data.Base64.Properties
open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Data.Nat.Properties as Nat

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

  parseBase64Pad1 : Parser (Logging ∘ Dec) Base64Pad1
  parseBase64Pad1 =
    parseEquivalent Base64Pad.equiv₁
      (parse& (NonNesting&ₚ Base64Char.nonnesting Base64Char.nonnesting) (parse& Base64Char.nonnesting parseBase64Char parseBase64Char)
        (parse& (nonnestingΣₚ₁ Base64Char.nonnesting)
          (parseSigma Base64Char.nonnesting Base64Char.unambiguous parseBase64Char
            λ where
              (mk64 c c∈ i bs≡) → _ ≟ 0)
          (parseLit (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") _)))
    where here' = "parseBase64Pad1"

  parseBase64Pad2 : Parser (Logging ∘ Dec) Base64Pad2
  parseBase64Pad2 =
    parseEquivalent Base64Pad.equiv₂
      (parse& Base64Char.nonnesting
        parseBase64Char
        (parse& (nonnestingΣₚ₁ Base64Char.nonnesting)
          (parseSigma Base64Char.nonnesting Base64Char.unambiguous parseBase64Char
            λ where
              (mk64 c c∈ i bs≡) → _ ≟ 0)
          (parseLit (tell $ here' String.++ ": underflow" ) (tell $ here' String.++ ": mismatch") _)))
    where
    here' = "parseBase64Pad2"

    parseMaxBase64Pad : LogDec.MaximalParser Base64Pad
    parseMaxBase64Pad = LogDec.mkMaximalParser help
      where
      help : ∀ xs → Σ (Logging ∘ Dec $ Success Base64Pad xs) _
      help [] = (mkLogged [] (yes (success [] _ refl (pad0 refl) [] refl)))
                , λ where
                    .[] .[] refl (pad0 refl) → z≤n
                    pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁ c₂ c₃ pad bs≡)) →
                      contradiction{P = 4 + length suf' ≡ 0}
                        (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'                     ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                         ≡⟨ cong length eq ⟩
                               length{A = Char} []                           ∎)
                        λ ()
                    pre' suf' eq (pad2 (mk64P1{b₁}{b₂} c₁ c₂ pad bs≡)) →
                      contradiction {P = 4 + length suf' ≡ 0}
                        (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'                      ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                          ≡⟨ cong length eq ⟩
                               length{A = Char} []                            ∎)
                        λ ()
      help (c₁ ∷ []) =
        (mkLogged [] (yes (success [] _ refl (pad0 refl) [ c₁ ] refl)))
        , λ where
            .[] suf' eq (pad0 refl) → z≤n
            pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁' c₂' c₃' pad bs≡)) →
              contradiction {P = 4 + length suf' ≡ 1}
                (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'             ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                 ≡⟨ cong length eq ⟩
                               length [ c₁ ]                         ∎)
                (λ ())
            pre' suf' eq (pad2 (mk64P1{b₁}{b₂} c₁ c₂ pad bs≡)) →
              contradiction {P = 4 + length suf' ≡ 1}
                (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'              ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                  ≡⟨ cong length eq ⟩
                               length [ c₁ ]                          ∎)
                (λ ())
      help (c₁ ∷ c₂ ∷ []) =
        (mkLogged [] (yes (success [] _ refl (pad0 refl) (c₁ ∷ [ c₂ ]) refl)))
        , λ where
            .[] suf' eq (pad0 refl) → z≤n
            pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁' c₂' c₃' pad bs≡)) →
              contradiction {P = 4 + length suf' ≡ 2}
                (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'             ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                 ≡⟨ cong length eq ⟩
                               length (c₁ ∷ [ c₂ ])                  ∎)
                (λ ())
            pre' suf' eq (pad2 (mk64P1{b₁}{b₂} c₁' c₂' pad bs≡)) →
              contradiction {P = 4 + length suf' ≡ 2}
                (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'              ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                  ≡⟨ cong length eq ⟩
                               length (c₁ ∷ [ c₂ ])                   ∎)
                (λ ())
      help (c₁ ∷ c₂ ∷ c₃ ∷ []) =
        (mkLogged [] (yes (success [] _ refl (pad0 refl) (c₁ ∷ c₂ ∷ [ c₃ ]) refl)))
        , λ where
            .[] suf' eq (pad0 refl) → z≤n
            pre' suf' eq (pad1 (mk64P1{b₁}{b₂}{b₃} c₁' c₂' c₃' pad bs≡)) →
              contradiction {P = 4 + length suf' ≡ 3}
                (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'             ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                 ≡⟨ cong length eq ⟩
                               length (c₁ ∷ c₂ ∷ [ c₃ ])             ∎)
                (λ ())
            pre' suf' eq (pad2 (mk64P1{b₁}{b₂} c₁' c₂' pad bs≡)) →
              contradiction {P = 4 + length suf' ≡ 3}
                (begin length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
                               length pre' + length suf'              ≡⟨ sym (length-++ pre') ⟩
                               length (pre' ++ suf')                  ≡⟨ cong length eq ⟩
                               length (c₁ ∷ c₂ ∷ [ c₃ ])              ∎)
                (λ ())
      help xs'@(c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ xs) =
        let p₁ = runParser parseBase64Pad1 xs'
        in
        case p₁ of λ where
          (mkLogged log (yes (success prefix read read≡ value@(mk64P1 c₁ c₂ c₃ pad refl) suffix ps≡))) →
            (mkLogged log (yes (success prefix _ read≡ (pad1 value) suffix ps≡)))
            , λ where
                .[] suf' eq (pad0 refl) → z≤n
                pre' suf' eq (pad1 (mk64P1 c₁ c₂ c₃ pad bs≡)) →
                  Lemmas.≡⇒≤
                    (begin (length pre' ≡⟨ ‼ (cong length bs≡) ⟩
                           4 ≡⟨ ‼ sym read≡ ⟩
                           read ∎))
                pre' suf' eq (pad2 (mk64P1 c₁ c₂ pad bs≡)) → {!!}
          (mkLogged log (no ¬p)) →
            let p₂ = runParser parseBase64Pad2 xs'
            in
            {!!}

--   parseMaxBase64Str : LogDec.MaximalParser Base64Str
--   parseMaxBase64Str = LogDec.mkMaximalParser help
--     where
--     help : ∀ xs → Σ (Logging ∘ Dec $ Success Base64Str xs) _
--     help [] = (mkLogged [] (yes (success [] 0 refl (mk64Str nil refl (pad0 refl) refl) [] refl)))
--               , λ pre' suf' eq x₁ → case ++-conicalˡ pre' suf' eq ,′ ++-conicalʳ pre' suf' eq of λ where
--                   (refl , refl) → Nat.≤-refl
--     help (c₁ ∷ []) =
--       mkLogged []
--         (yes (success [] _ refl (mk64Str nil refl (pad0 refl) refl) [ c₁ ] refl))
--       , λ where
--         .[] suf' eq (mk64Str nil strLen (pad0 refl) refl) → Nat.≤-refl
--         pre' suf' eq (mk64Str Aeres.Grammar.IList.nil strLen (pad1 (mk64P1{b₁}{b₂}{b₃} _ _ _ pad bs≡)) refl) →
--           contradiction {P = 4 + length suf' ≡ 1}
--             (begin length (b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
--                    length pre' + length suf'                     ≡⟨ sym (length-++ pre') ⟩
--                    length (pre' ++ suf')                         ≡⟨ cong length eq ⟩
--                    length [ c₁ ]                                 ∎ )
--             (λ ())
--         pre' suf' eq (mk64Str Aeres.Grammar.IList.nil strLen (pad2 (mk64P1{b₁}{b₂} _ _ pad bs≡)) refl) →
--           contradiction {P = 4 + length suf' ≡ 1}
--             (begin (length (b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]) + length suf' ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
--             length pre' + length suf' ≡⟨ sym (length-++ pre') ⟩
--             length (pre' ++ suf') ≡⟨ cong length eq ⟩
--             length [ c₁ ] ∎))
--             (λ ())
--         pre' suf' eq (mk64Str{p = p} (consIList (mk64 c c∈ i refl) (consIList{bs₂ = bs₂} (mk64 c' c∈₁ i₁ refl) tail₁ refl) refl) strLen pad bs≡) →
--           contradiction {P = 2 + length bs₂ + length p + length suf' ≡ 1}
--             (begin length (c ∷ [ c' ]) + length bs₂ + length p + length suf' ≡⟨ cong (λ x → x + length p + length suf') (sym (length-++ (c ∷ [ c' ]) {bs₂})) ⟩
--                    length (c ∷ c' ∷ bs₂) + length p + length suf'            ≡⟨ cong (_+ length suf') (sym (length-++ (c ∷ c' ∷ bs₂))) ⟩
--                    length (c ∷ c' ∷ bs₂ ++ p) + length suf'                  ≡⟨ cong (λ x → length x + length suf') (sym bs≡) ⟩
--                    length pre' + length suf'                                 ≡⟨ sym (length-++ pre') ⟩
--                    length (pre' ++ suf')                                     ≡⟨ cong length eq ⟩
--                    length [ c₁ ]                                             ∎)
--             (λ ())
--     help (c₁ ∷ c₂ ∷ []) = {!!}
--     help (c₁ ∷ c₂ ∷ c₃ ∷ []) = {!!}
--     help (c₁ ∷ c₂ ∷ c₃ ∷ c₄ ∷ xs) =
--       {!!}

--   parseBase64Str : ∀ n {n%4 : True (n % 4 ≟ 0)}  → Parser (Logging ∘ Dec) (ExactLength Base64Str n)
--   runParser (parseBase64Str n {n%4}) xs = do
--     yes (success .v₀ r₀ r₀≡ (mk×ₚ (singleton v₀ refl) (─ v₀Len) refl) suf₀ ps≡₀)
--       ← runParser (parseExactLengthString (tell $ "parseBase64Str: underflow") n) xs
--       where no ¬parse → do
--         return ∘ no $ λ where
--           (success prefix read read≡ (mk×ₚ str (─ strLen) bs≡) suffix ps≡) →
--             contradiction (success prefix _ read≡ (mk×ₚ self (─ strLen) bs≡) suffix ps≡) ¬parse
--     case Base64Str.b64Str? v₀ of λ where
--       (no ¬p) → return ∘ no $ λ where
--         (success prefix read read≡ (mk×ₚ{bs} str (─ strLen) refl) suffix ps≡) →
--           contradiction
--             (subst Base64Str
--               (proj₁
--                 (Lemmas.length-++-≡ _ _ _ _
--                   (begin (prefix ++ suffix ≡⟨ ps≡ ⟩
--                          xs                ≡⟨ sym ps≡₀ ⟩
--                          v₀ ++ suf₀        ∎))
--                   (begin length bs ≡⟨ strLen ⟩
--                          n         ≡⟨ sym v₀Len ⟩
--                          length v₀ ∎)))
--               str)
--             ¬p
--       (yes p) → return (yes (success v₀ r₀ r₀≡ (mk×ₚ p (─ v₀Len) refl) suf₀ ps≡₀))

-- open parseBase64 public using (parseBase64Char; parseBase64Str)
