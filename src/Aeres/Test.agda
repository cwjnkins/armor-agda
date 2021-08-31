open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.Parser

module Aeres.Test where

open Base256

M = Maybe

open Aeres.Data.Parser Dig
open Parser

ParserX509 = λ (A : List Dig → Set) → Parser A M


parseLen : ∀ n → ParserX509 Length n
parseLen n = Aeres.Data.Parser.mkParser {!!}
  where
  go : (xs : List Dig) → .(length xs ≤ n) → M (Success Length n)
  go [] ≤n = nothing
  go (x ∷ xs) ≤n
    with Fin.<-cmp x (# 128)
  go (x ∷ xs) ≤n | tri< a ¬b ¬c =
    just ((short x (fromWitness a)) Aeres.Data.Parser.^ xs , {!!})
  go (x ∷ xs) ≤n | tri≈ ¬a b ¬c = nothing
  go (x ∷ xs) ≤n | tri> ¬a ¬b c = {!!}

postulate
  parseTBS : ∀ n → ParserX509 X509.TBSCert n
  parseSignAlg : ∀ n → ParserX509 X509.SignAlg n
  parseSignature : ∀ n → ParserX509 X509.Signature n

parseCertField : ∀ n → ParserX509 X509.CertField n
parseCertField n = Aeres.Data.Parser.mkParser go
  where
  go : (xs : List Dig) → .(length xs ≤ n) → M (Success X509.CertField n)
  go xs ≤n = {!!}

parseCert : ∀ n → ParserX509 X509.Cert n
parseCert n = Aeres.Data.Parser.mkParser go
  where
  go : ∀ xs → .(length xs ≤ n) → M (Success X509.Cert n)
  go [] ≤n = nothing
  go (x ∷ xs) ≤n
    with x ≟ Tag.Sequence
  go (x ∷ xs) ≤n | no  proof₁ = nothing
  go (._ ∷ xs) ≤n | yes refl
    with runParser (parseLen (length xs)) xs {!!}
  go ._ ≤n | yes refl | nothing = nothing
  go ._ ≤n | yes refl | just lCert = {!!}
