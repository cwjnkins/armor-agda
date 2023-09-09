{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X509.RDN.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

module parseRDN where

  here₁ = "X509: RDN"

  parseRDNATVFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RDNATVFields n)
  runParser (parseRDNATVFields n) xs = do
    yes (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁}{bs₂} oid ds refl) valLen refl) suffix ps≡)
      ← runParser (parseExactLength
                    (NonNesting&ₚ TLV.nonnesting DirectoryString.nonnesting)
                    (tell $ here₁ String.++ ": underflow")
                    (parse& TLV.nonnesting parseOID parseDirectoryString) n) xs
      where no ¬parse → do
        tell $ here₁
        return ∘ no $ λ where
          (success prefix@.(bs₁ ++ bs₂) read read≡ (mk×ₚ (mkRDNATVFields{bs₁}{bs₂} oid ds refl) valLen refl) suffix ps≡) →
            contradiction
              (success prefix _ read≡ (mk×ₚ (mk&ₚ oid ds refl) valLen refl) suffix ps≡)
              ¬parse
    return (yes
      (success prefix _ read≡ (mk×ₚ (mkRDNATVFields oid ds refl) valLen refl) suffix ps≡))

  parseRDNATV : Parser (Logging ∘ Dec) RDNATV
  parseRDNATV = parseTLV _ (here₁ String.++ ": ATV") _ parseRDNATVFields

  parseRDN : Parser (Logging ∘ Dec) RDN
  parseRDN =
    parseTLV _ here₁ _
      λ n → parseBoundedSequenceOf here₁ _ TLV.nonempty TLV.nonnesting parseRDNATV n 1

  parseRDNSeq : Parser (Logging ∘ Dec) RDNSeq
  parseRDNSeq =
    parseSeq (here₁ String.++ " (fields)") _ TLV.nonempty TLV.nonnesting parseRDN

open parseRDN public
  using (parseRDNATV ; parseRDN ; parseRDNSeq)
