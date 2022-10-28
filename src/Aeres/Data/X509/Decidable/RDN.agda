{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.DirectoryString
open import Aeres.Data.X509.Properties as Props
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
                    (NonNesting&ₚ Dig TLV.nonnesting Props.DirectoryString.nonnesting)
                    (tell $ here₁ String.++ ": underflow")
                    (parse& Dig TLV.nonnesting parseOID parseDirectoryString) n) xs
      where no ¬parse → do
        tell $ here₁
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
      λ n → parseBoundedSequenceOf "RDNATV" _ TLV.nonempty TLV.nonnesting parseRDNATV n 1

  parseRDNSeq : Parser Dig (Logging ∘ Dec) X509.RDNSeq
  parseRDNSeq =
    parseSeq "RDNSeq" _ TLV.nonempty TLV.nonnesting parseRDN

open parseRDN public
  using (parseRDNATV ; parseRDN ; parseRDNSeq)
