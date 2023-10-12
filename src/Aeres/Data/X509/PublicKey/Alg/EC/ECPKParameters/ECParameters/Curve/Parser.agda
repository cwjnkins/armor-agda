{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.Curve.Properties
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.Curve.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.Curve.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Alg: EC: ECPKParameters: ECParameters: Curve"

parseCurveFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength CurveFields n)
parseCurveFields n =
  parseEquivalent
    (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalent))
    (parse&ᵈ (Parallel.nosubstrings₁ (Seq.nosubstrings TLV.nosubstrings  TLV.nosubstrings))
      (Parallel.Length≤.unambiguous _
        (Seq.unambiguous (TLV.unambiguous OctetString.unambiguous)
          TLV.nosubstrings (TLV.unambiguous OctetString.unambiguous)))
      (parse≤ n (parse& TLV.nosubstrings  parseOctetString parseOctetString)
        (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings) ((tell $ here' String.++ ": overflow")))
          λ where
            {bs} (singleton read read≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
                (Option.parseOption₁ExactLength
                  TLV.nosubstrings
                  (tell $ here' String.++ ": underflow")
                  parseBitstring _))

parseCurve : Parser (Logging ∘ Dec) Curve
parseCurve = parseTLV _ here' _ parseCurveFields

