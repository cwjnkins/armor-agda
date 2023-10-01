{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg
open import Aeres.Data.X509.PublicKey.Properties
open import Aeres.Data.X509.PublicKey.TCB
open import Aeres.Data.X509.PublicKey.Val
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey"

parsePublicKeyFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength PublicKeyFields n)
parsePublicKeyFields n =
  parseEquivalent eq p₁
  where
  A = Length≤ PublicKeyAlg n
  B : {@0 bs : List UInt8} → (a : A bs) → @0 List UInt8 → Set
  B{bs} a = ExactLength (PublicKeyVal (proj₂ (Alg.getOID (fstₚ a)))) (n - length bs)

  eq : Equivalent (&ₚᵈ A B) (ExactLength PublicKeyFields n)
  eq = Iso.transEquivalent (Iso.symEquivalent (Distribute.exactLength-&ᵈ)) (Parallel.equivalent₁ equiv)

  @0 nn₁ : NoSubstrings A
  nn₁ = Parallel.nosubstrings₁ Alg.nosubstrings

  @0 ua₁ : Unambiguous A
  ua₁ = Parallel.Length≤.unambiguous _ Alg.unambiguous

  p₂ : Parser (Logging ∘ Dec) A
  p₂ = parse≤ _ parsePublicKeyAlg Alg.nosubstrings
         (tell $ here' String.++ ": overflow (Alg)")

  p₃ : ∀ {@0 bs} → Singleton (length bs) → (a : A bs) → Parser (Logging ∘ Dec) (B a)
  p₃ (singleton x x≡) a =
    subst₀
      (λ y → Parser (Logging ∘ Dec) (ExactLength (PublicKeyVal o) (n - y)))
      x≡
      p
    where
    o = proj₂ (Alg.getOID (fstₚ a))
    p : Parser (Logging ∘ Dec) (ExactLength (PublicKeyVal o) (n - x))
    p = parseExactLength (Val.nosubstrings o)
          (tell $ here' String.++ ": length mismatch (Val)")
          (parsePublicKeyVal o) (n - x)

  p₁ : Parser (Logging ∘ Dec) (&ₚᵈ A B)
  p₁ = parse&ᵈ{A = A} {B = B} nn₁ ua₁ p₂ p₃

parsePublicKey : Parser (Logging ∘ Dec) PublicKey
parsePublicKey = parseTLV _ here' _ parsePublicKeyFields
