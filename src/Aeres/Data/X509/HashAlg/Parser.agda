{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
import      Aeres.Data.X509.HashAlg.TCB
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.HashAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8

module RSASSA-PSS where
  open Aeres.Data.X509.HashAlg.TCB.RSASSA-PSS

  parser : Parser (Logging ∘ Dec) HashAlg
  parser = parseAlgorithmIdentifier "Hash" help
    where
    help : ∀ n {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (Param o) n)
    runParser (help n o) xs =
      case (-, TLV.val o) ∈? OIDs.NullOrAbsent ret (const _) of λ where
        (yes p) → do
          yes (success pre₁ r₁ r₁≡ (mk×ₚ v₁ v₁Len refl) suf₁ ps≡₁) ←
            runParser
              (parseOption₁ExactLength TLV.nonempty TLV.nonnesting
                (tell "X509: HashAlg: RSASSA-PSS: underflow")
                parseNull n)
              xs
            where no ¬p → do
              tell "X509: HashAlg: RSASSA-PSS: failed to parse parameter"
              return ∘ no $ λ where
                (success prefix read read≡ (mk×ₚ (mk×ₚ p p∈ refl) vLen refl) suffix ps≡) →
                  contradiction
                    (success prefix _ read≡ (mk×ₚ p vLen refl) suffix ps≡)
                    ¬p
          return (yes
            (success pre₁ r₁ r₁≡ (mk×ₚ (mk×ₚ v₁ (fromWitness p) refl) v₁Len refl) suf₁ ps≡₁))
        (no ¬p) → do
          tell $ "X509: HashAlg: RSASSA-PSS: unknown OID: "
                 String.++ show (map toℕ (↑ (OID.serialize o)))
          return ∘ no $ λ where
            (success prefix read read≡ (mk×ₚ (mk×ₚ _ o∈ refl) vLen refl) suffix ps≡) →
              contradiction (toWitness o∈) ¬p
