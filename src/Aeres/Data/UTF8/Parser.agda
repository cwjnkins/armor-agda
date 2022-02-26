{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
import      Aeres.Data.UTF8.Properties as UTF8Props
open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser

module Aeres.Data.UTF8.Parser where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Parser      UInt8

module parseUTF8 where
  hereChar = "parseUTF8Char"

  parseUTF8Char1 : Parser (Logging ∘ Dec) UTF8Char1
  runParser parseUTF8Char1 [] = do
    tell $ hereChar String.++ ": underflow"
    return ∘ no $ λ where
      (success prefix read read≡ value suffix ps≡) →
        contradiction
          (++-conicalˡ _ suffix ps≡) λ where
            refl → case ‼ UTF8Char1.bs≡ value of λ ()
      
  runParser parseUTF8Char1 (x ∷ xs) =
    case toℕ x <? 128 of λ where
      (no ¬p) → do
        tell $ hereChar String.++ ": invalid UTF8(1)"
        return ∘ no $ λ where
          (success prefix read read≡ value suffix ps≡) →
            let @0 b₁≡ : x ≡ UTF8Char1.b₁ value
                b₁≡ =
                  ∷-injectiveˡ
                    (proj₁
                      (Lemmas.length-++-≡ [ x ] _ [ UTF8Char1.b₁ value ] _
                        (trans₀ (sym ps≡) (cong (_++ suffix) (UTF8Char1.bs≡ value))) refl))
            in
            contradiction
              (subst (λ z → toℕ z < 128) (sym b₁≡) (UTF8Char1.b₁range value))
              ¬p
      (yes p) → do
        return (yes
          (success [ x ] 1 refl (mkUTF8Char1 x p refl) xs refl))


  parseUTF8Char2 : Parser (Logging ∘ Dec) UTF8Char2
  runParser parseUTF8Char2 [] = do
    tell $ hereChar String.++ ": underflow"
    return ∘ no $ λ where
      (success prefix read read≡ value suffix ps≡) →
        contradiction
          (++-conicalˡ _ suffix ps≡) λ where
            refl → case ‼ UTF8Char2.bs≡ value of λ ()
  runParser parseUTF8Char2 (b₁ ∷ []) = do
    tell $ hereChar String.++ ": underflow"
    return ∘ no $ λ where
      (success prefix read read≡ value suffix ps≡) →
        contradiction
          (++-conicalˡ _ suffix (∷-injectiveʳ (trans₀ (cong (_++ suffix) (sym $ UTF8Char2.bs≡ value)) ps≡)))
          λ ()
  runParser parseUTF8Char2 (b₁ ∷ b₂ ∷ xs) =
    case (inRange? 192 223 b₁ ,′ inRange? 128 191 b₂) of λ where
      (no ¬p , _) → do
        tell $ hereChar String.++ ": invalid UTF8(2)"
        return ∘ no $ λ where
          (success prefix read read≡ value suffix ps≡) →
            let @0 b₁≡ : UTF8Char2.b₁ value ≡ b₁
                b₁≡ =
                  ∷-injectiveˡ (proj₁
                    (Lemmas.length-++-≡ [ UTF8Char2.b₁ value ] _ [ b₁ ] _
                      (trans₀ (cong (_++ suffix) (sym $ UTF8Char2.bs≡ value)) ps≡) refl))
            in
            contradiction
              (subst (InRange 192 223) b₁≡ (UTF8Char2.b₁range value))
              ¬p
      (yes _ , no ¬p) → do
        tell $ hereChar String.++ ": invalid UTF8(2)"
        return ∘ no $ λ where
          (success prefix read read≡ value suffix ps≡) →
            let @0 b₂≡ : UTF8Char2.b₂ value ≡ b₂
                b₂≡ =
                  ∷-injectiveˡ (∷-injectiveʳ
                    (trans₀ (cong (_++ suffix) (sym $ UTF8Char2.bs≡ value)) ps≡))
            in
            contradiction
              (subst₀ (InRange 128 191) b₂≡ (UTF8Char2.b₂range value))
              ¬p
      (yes b₁range , yes b₂range) →
        return (yes
          (success (b₁ ∷ [ b₂ ]) _ refl (mkUTF8Char2 b₁ b₂ b₁range b₂range refl) xs refl))

  parseUTF8Char3 : Parser (Logging ∘ Dec) UTF8Char3
  parseUTF8Char3 =
    parseEquivalent (proj₁ UTF8Props.UTF8Char3Props.iso)
      (parseSigma exactLength-nonnesting exactLengthString-unambiguous
        (parseN 3 (tell $ hereChar String.++ ": underflow (3)"))
        λ els →
          let b₁ = lookupELS els (# 0)
              b₂ = lookupELS els (# 1)
              b₃ = lookupELS els (# 2)
          in
          erased? (inRange? 224 239 b₁
                   ×-dec inRange? 128 191 b₂
                   ×-dec inRange? 128 191 b₃))

  parseUTF8Char4 : Parser (Logging ∘ Dec) UTF8Char4
  parseUTF8Char4 =
    parseEquivalent UTF8Props.UTF8Char4Props.equiv
      (parseSigma exactLength-nonnesting exactLengthString-unambiguous
        (parseN 4 (tell $ hereChar String.++ ": underflow (4)"))
        λ els →
          let b₁ = lookupELS els (# 0)
              b₂ = lookupELS els (# 1)
              b₃ = lookupELS els (# 2)
              b₄ = lookupELS els (# 3)
          in
          erased? (      inRange? 240 247 b₁ ×-dec inRange? 128 191 b₂
                   ×-dec inRange? 128 191 b₃ ×-dec inRange? 128 191 b₄))

  parseUTF8Char : Parser (Logging ∘ Dec) UTF8Char
  parseUTF8Char =
    parseEquivalent UTF8Props.UTF8CharProps.equiv
      (parseSum parseUTF8Char1
        (parseSum parseUTF8Char2
          (parseSum parseUTF8Char3
            parseUTF8Char4)))
