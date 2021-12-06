{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.DirectoryString
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.SequenceOf
open import Aeres.Data.X509.Decidable.TLV
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
                    (NonNesting&ₚ Dig Props.TLV.nonnesting Props.DirectoryString.nonnesting)
                    (tell $ here₁ String.++ ": underflow")
                    (parse& Dig Props.TLV.nonnesting parseOID parseDirectoryString) n) xs
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
      (parseSequenceOf "RDNATV" _ Props.TLV.nonempty Props.TLV.nonnesting
        parseRDNATV)

  parseRDNSeq : Parser Dig (Logging ∘ Dec) X509.RDNSeq
  parseRDNSeq =
    parseSeq "RDNSeq" _ Props.TLV.nonempty Props.TLV.nonnesting parseRDN

open parseRDN public
  using (parseRDNATV ; parseRDN ; parseRDNSeq)


private
  module Test where

  Name₁ : List Dig
  Name₁ = Tag.Sequence ∷ # 26 ∷ # 49 ∷ # 11  ∷ # 48  ∷ # 9  ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ [ # 83 ]

  Name₂ : List Dig
  Name₂ = Tag.Sequence ∷ # 26 ∷ # 49 ∷ # 11  ∷ # 48  ∷ # 9  ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 48 ∷ # 11 ∷ # 49 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ [ # 83 ]

  test₁ : X509.RDNSeq Name₁
  test₁ = Success.value (toWitness {Q = Logging.val (runParser parseRDNSeq Name₁)} tt)

  test₂ : ¬ Success _ X509.RDNSeq Name₂
  test₂ = toWitnessFalse {Q = Logging.val (runParser parseRDNSeq Name₂)} tt
