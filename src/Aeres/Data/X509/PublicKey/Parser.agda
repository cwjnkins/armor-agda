{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg
open import Aeres.Data.X509.PublicKey.Properties
open import Aeres.Data.X509.PublicKey.TCB
open import Aeres.Data.X509.PublicKey.Val
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

private
  here' = "X509: PublicKey"

parsePublicKeyFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength PublicKeyFields n)
parsePublicKeyFields n =
  parseEquivalent eq p₁
  where
  A = WithinLength PublicKeyAlg n
  B : (@0 bs : List UInt8) → (a : A bs) → @0 List UInt8 → Set
  B = λ (@0 bs₁) a →
        ExactLength
          (PublicKeyVal (proj₂ (Alg.getOID (fstₚ a))))
          (n - length bs₁)
  eq : Equivalent (&ₚᵈ A B) (ExactLength PublicKeyFields n)
  eq = Iso.transEquivalent (Iso.symEquivalent (Distribute.exactLength-&ᵈ)) (equivalent×ₚ equiv)

  @0 nn₁ : NonNesting A
  nn₁ = withinLength-nonnesting Alg.nonnesting

  @0 ua₁ : Unambiguous A
  ua₁ = withinLength-unambiguous Alg.unambiguous

  p₂ : Parser (Logging ∘ Dec) A
  p₂ = parse≤ _ parsePublicKeyAlg Alg.nonnesting
         (tell $ here' String.++ ": overflow (Alg)")

  p₃ : ∀ {@0 bs} → Singleton (length bs) → (a : A bs) → Parser (Logging ∘ Dec) (B bs a)
  p₃ (singleton x x≡) a =
    subst₀
      (λ y → Parser (Logging ∘ Dec) (ExactLength (PublicKeyVal o) (n - y)))
      x≡
      p
    where
    o = proj₂ (Alg.getOID (fstₚ a))
    p : Parser (Logging ∘ Dec) (ExactLength (PublicKeyVal o) (n - x))
    p = parseExactLength (Val.nonnesting o)
          (tell $ here' String.++ ": length mismatch (Val)")
          (parsePublicKeyVal o) (n - x)

  p₁ : Parser (Logging ∘ Dec) (&ₚᵈ A B)
  p₁ = parse&ᵈ{A = A} {B = B} nn₁ ua₁ p₂ p₃

parsePublicKey : Parser (Logging ∘ Dec) PublicKey
parsePublicKey = parseTLV _ here' _ parsePublicKeyFields
