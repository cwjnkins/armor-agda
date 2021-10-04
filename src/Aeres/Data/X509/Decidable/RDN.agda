{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.DirectoryString
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.RDN where

open Base256

module parseRDN where

  here₁ = "parseRDNATVFields"

  parseRDNATVFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig X509.RDNATVFields n)
  runParser (parseRDNATVFields n) xs = do
    yes (success prefix read read≡ (mk×ₚ (mk&ₚ{bs₁}{bs₂} oid ds refl) valLen refl) suffix ps≡)
      ← runParser (parseExactLength Dig
                    (NonNesting&ₚ Dig NonNesting.TLV NonNesting.DirectoryString)
                    (tell $ here₁ String.++ ": underflow")
                    (parse× Dig NonNesting.TLV parseOID parseDirectoryString) n) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix@.(bs₁ ++ bs₂) read read≡ (mk×ₚ (X509.mkRDNATVFields{bs₁}{bs₂} oid ds refl) valLen refl) suffix ps≡) →
            contradiction
              (success prefix _ read≡ (mk×ₚ (mk&ₚ oid ds refl) valLen refl) suffix ps≡)
              ¬parse
    return (yes
      (success prefix _ read≡ (mk×ₚ (X509.mkRDNATVFields oid ds refl) valLen refl) suffix ps≡))

  parseRDNATV : Parser Dig (Logging ∘ Dec) X509.RDNATV
  parseRDNATV = parseTLV _ "RDNATV" _ parseRDNATVFields

  parseRDN : Parser Dig (Logging ∘ Dec) X509.RDN
  parseRDN =
    parseTLV _ "RDN" _
      (parseSeqElems "RDNATV" _ NonEmpty.TLV NonNesting.TLV
        parseRDNATV)

  parseRDNSeq : Parser Dig (Logging ∘ Dec) X509.RDNSeq
  parseRDNSeq =
    parseSeq "RDNSeq" _ NonEmpty.TLV NonNesting.TLV parseRDN