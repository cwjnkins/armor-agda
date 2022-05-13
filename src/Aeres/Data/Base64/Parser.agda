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
{-
Goal: (λ { _ (─ xs)
             → Exists─
               ((setoid Char.Char Data.List.Membership.Setoid.∈
                 lookupELS xs (# 0))
                Base64.charset)
               (λ (@0 c∈₁) → Singleton (Any.index c∈₁))
         })
      bs (─ mk×ₚ (singleton bs refl) (─ len≡') refl)

-}
              -- let @0 els : @0 length bs ≡ 1 → ExactLengthString 1 bs
              --     els eq = (mk×ₚ (singleton bs refl) (─ eq) refl)
              --     @0 G : @0 length bs ≡ 1 → Set
              --     G eq = lookupELS (els eq) (# 0) ∈ Base64.charset
              --     @0 c∈' : Erased (G _)
              --     c∈' = ─ (subst G (≡-unique len≡ _) c∈)
              -- in
              -- (─ (G len≡' ∋ Erased.x c∈'))
              -- , singleton i (trans i≡ (begin
              --   Any.index {P = lookupELS (els len≡) (# 0) ≡_} c∈ ≡⟨ {!!} ⟩
              --   Any.index {P = {!!}} {!!} ≡⟨ {!!} ⟩
              --   {!!})))

        (parseErased (parseExactLengthString (tell $ hereChar String.++ ": underflow") 1)))
