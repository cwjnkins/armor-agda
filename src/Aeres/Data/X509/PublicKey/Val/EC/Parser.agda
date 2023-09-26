{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

private
  here' = "X509: PublicKey: Val: EC"

parseECBitString : Parser (Logging ∘ Dec) ECBitString
parseECBitString =
  parse× TLV.nonnesting
    (λ where
      xs₁++ys₁≡xs₂++ys₂ (─ a₁) (─ a₂) →
        ‼ TLV.nonnesting xs₁++ys₁≡xs₂++ys₂ a₁ a₂)
    (return (Level.lift tt))
    parseBitstring
    (parseErased (parseTLV _ "X509: PublicKey: Val: EC:" _
      λ n →
        parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
         (parse&ᵈ
           (withinLength-nonnesting λ where _ refl refl → refl)
           (withinLength-unambiguous (λ where refl refl → refl))
           (parse≤ _
             (parseLit
               (tell $ "X509: PublicKey: Val: EC: underflow")
               (tell $ "X509: PublicKey: Val: EC: unused bits not 0")
               _)
             (λ where _ refl refl → refl)
             (tell $ "X509: PublicKey: Val: EC: overlfow"))
           λ where
             (singleton r r≡) _ →
               subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength OctetStringValue (n - x)))
                 r≡ (parseOctetStringValue (n - r)))))
