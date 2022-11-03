{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
import      Aeres.Data.UTF8.Properties as UTF8Props
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.UTF8.Parser where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

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
  runParser parseUTF8Char3 [] = do
    tell "parseUTF8Char3: underflow(0)"
    return ∘ no $ λ where
      (success prefix read read≡ (mkUTF8Char3 b₁ b₁range b₂ b₂range b₃ b₃range refl) suffix ())
  runParser parseUTF8Char3 (x ∷ []) = do
    tell "parseUTF8Char3: underflow(1)"
    return ∘ no $ λ where
      (success prefix read read≡ (mkUTF8Char3 b₁ b₁range b₂ b₂range b₃ b₃range refl) suffix ())
  runParser parseUTF8Char3 (x ∷ x₁ ∷ []) = do
    tell "parseUTF8Char3: underflow(2)"
    return ∘ no $ λ where
      (success prefix read read≡ (mkUTF8Char3 b₁ b₁range b₂ b₂range b₃ b₃range refl) suffix ())
  runParser parseUTF8Char3 (x ∷ x₁ ∷ x₂ ∷ x₃) =
    case inRange? 224 239 x ,′ inRange? 128 191 x₁ ,′ inRange? 128 191 x₂ of λ where
      (no ¬p , _) → do
        tell $ "parseUTF8Char3: bad char range (1: " String.++ (show ∘ toℕ $ x) String.++ ")"
        return ∘ no $ λ where
          (success prefix read read≡ (mkUTF8Char3 b₁ b₁range b₂ b₂range b₃ b₃range refl) suffix refl) →
            contradiction b₁range ¬p
      (yes p , no ¬p , _) → do
        tell $ "parseUTF8Char3: bad char range (2: " String.++ (show ∘ toℕ $ x₁) String.++ ")"
        return ∘ no $ λ where
          (success prefix read read≡ (mkUTF8Char3 b₁ b₁range b₂ b₂range b₃ b₃range refl) suffix refl) →
            contradiction b₂range ¬p
      (yes p , yes p₁ , no ¬p) → do
        tell $ "parseUTF8Char3: bad char range (3: " String.++ (show ∘ toℕ $ x₂) String.++ ")"
        return ∘ no $ λ where
          (success prefix read read≡ (mkUTF8Char3 b₁ b₁range b₂ b₂range b₃ b₃range refl) suffix refl) →
            contradiction b₃range ¬p
      (yes p , yes p₁ , yes p₂) →
        return (yes
          (success (x ∷ x₁ ∷ [ x₂ ]) _ refl (mkUTF8Char3 x p x₁ p₁ x₂ p₂ refl) x₃ refl))

  parseUTF8Char4 : Parser (Logging ∘ Dec) UTF8Char4
  runParser parseUTF8Char4 [] = do
    tell $ "parseUTF8Char4: underflow(0)"
    return ∘ no $ λ where
      (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ _ _ _ _ refl) _ ())
  runParser parseUTF8Char4 (x ∷ []) = do
    tell $ "parseUTF8Char4: underflow(1)"
    return ∘ no $ λ where
      (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ _ _ _ _ refl) _ ())
  runParser parseUTF8Char4 (x ∷ x₁ ∷ []) = do
    tell $ "parseUTF8Char4: underflow(2)"
    return ∘ no $ λ where
      (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ _ _ _ _ refl) _ ())
  runParser parseUTF8Char4 (x ∷ x₁ ∷ x₂ ∷ []) = do
    tell $ "parseUTF8Char4: underflow(3)"
    return ∘ no $ λ where
      (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ _ _ _ _ refl) _ ())
  runParser parseUTF8Char4 (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ xs) =
    case    inRange? 240 247 x  ,′ inRange? 128 191 x₁
         ,′ inRange? 128 191 x₂ ,′ inRange? 128 191 x₃
    of λ where
      (no ¬p , _) → do
        tell $ "parseUTF8Char4: bad char range (1: " String.++ (show ∘ toℕ $ x) String.++ ")"
        return ∘ no $ λ where
          (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range _ _ _ refl) _ refl) →
            contradiction b₁range ¬p
      (yes p , no ¬p , _) → do
        tell $ "parseUTF8Char4: bad char range (2: " String.++ (show ∘ toℕ $ x₁) String.++ ")"
        return ∘ no $ λ where
          (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range _ _ refl) _ refl) →
            contradiction b₂range ¬p
      (yes p , yes p₁ , no ¬p , _) → do
        tell $ "parseUTF8Char4: bad char range (3: " String.++ (show ∘ toℕ $ x₂) String.++ ")"
        return ∘ no $ λ where
          (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range _ refl) _ refl) →
            contradiction b₃range ¬p
      (yes p , yes p₁ , yes p₂ , no ¬p) → do
        tell $ "parseUTF8Char4: bad char range (4: " String.++ (show ∘ toℕ $ x₃) String.++ ")"
        return ∘ no $ λ where
          (success _ _ _ (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range refl) _ refl) →
            contradiction b₄range ¬p
      (yes p , yes p₁ , yes p₂ , yes p₃) →
        return (yes
          (success _ _ refl (mkUTF8Char4 x x₁ x₂ x₃ p p₁ p₂ p₃ refl) _ refl))

  parseUTF8Char : Parser (Logging ∘ Dec) UTF8Char
  parseUTF8Char =
    parseEquivalent UTF8Props.UTF8CharProps.equiv
      (parseSum parseUTF8Char1
        (parseSum parseUTF8Char2
          (parseSum parseUTF8Char3
            parseUTF8Char4)))

  parseUTF8 : ∀ n → Parser (Logging ∘ Dec) (ExactLength UTF8 n)
  parseUTF8 =
    parseIList (tell "parseUTF8: underflow") UTF8Char
      UTF8Props.UTF8CharProps.nonempty
      UTF8Props.UTF8CharProps.nonnesting
      parseUTF8Char

open parseUTF8 public using (parseUTF8)
