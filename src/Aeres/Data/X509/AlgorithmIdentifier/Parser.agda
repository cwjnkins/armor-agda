{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.AlgorithmIdentifier.Properties
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.AlgorithmIdentifier.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

parseAlgorithmIdentifierFields
  : ∀ {@0 P : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set}
    → (∀ n {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (P o) n))
    → ∀ n → Parser (Logging ∘ Dec) (ExactLength (AlgorithmIdentifierFields P) n)
parseAlgorithmIdentifierFields{P} p₁ n =
  parseEquivalent
    (transEquivalent{B = ExactLength (Rep P) n} (symEquivalent Distribute.exactLength-&ᵈ) (equivalent×ₚ (equiv P)))
    (parse&ᵈ
      (withinLength-nonnesting TLV.nonnesting) (withinLength-unambiguous OID.unambiguous)
      (parse≤ _ parseOID TLV.nonnesting (tell $ "X509: AlgorithmIdentifier: Fields: overflow (OID)"))
      λ where
        (singleton r r≡) (mk×ₚ a (─ r≤) refl) →
          let p = p₁ (n - r) a
          in
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (P a) (n - x)))
            r≡ p)

parseAlgorithmIdentifier
  : ∀ {@0 P : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set}
    → String
    → (∀ n {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (P o) n))
    → Parser (Logging ∘ Dec) (AlgorithmIdentifier P)
parseAlgorithmIdentifier{P} s p =
  parseTLV _ ("parseAlgorithmIdentifier: " String.++ s)
    (AlgorithmIdentifierFields P) λ n → parseAlgorithmIdentifierFields p n
