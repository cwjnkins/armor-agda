{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Properties
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq       
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Params.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: EcPkAlg: Params: parseEcParamsFields"

parseFieldID :  Parser (Logging ∘ Dec) FieldID
parseFieldID = parseTLV _ "X509: EcPkAlg: Params: FieldId" _ parseOctetStringValue

parseEcParamsFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength EcParamsFields n)
parseEcParamsFields n =
  parseEquivalent
    (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (Parallel.equivalent₁ Fields.equivalent))
    (parse&ᵈ 
      (Parallel.nosubstrings₁
        (Seq.nosubstrings
          (Seq.nosubstrings
            (Seq.nosubstrings
              (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings)
              TLV.nosubstrings)
            TLV.nosubstrings)
          TLV.nosubstrings))
      (Parallel.Length≤.unambiguous _
        (Seq.unambiguous
          (Seq.unambiguous
            (Seq.unambiguous
              (Seq.unambiguous (λ where refl refl → refl) (λ where _ refl refl → refl)
                (TLV.unambiguous OctetString.unambiguous))
              (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings)
              (TLV.unambiguous Curve.unambiguous))
            (Seq.nosubstrings (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings) TLV.nosubstrings)
            (TLV.unambiguous OctetString.unambiguous))
          (Seq.nosubstrings (Seq.nosubstrings (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings) TLV.nosubstrings) TLV.nosubstrings)
          (TLV.unambiguous λ{xs} → Int.unambiguous{xs})))
        (parse≤ n (parse& (Seq.nosubstrings (Seq.nosubstrings (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings) TLV.nosubstrings) TLV.nosubstrings)
          (parse& (Seq.nosubstrings (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings) TLV.nosubstrings)
            (parse& (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings)
              (parse& (λ where _ refl refl → refl) (parseLit (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") (# 2 ∷ # 1 ∷ [ # 1 ]))
              parseFieldID) parseCurve) parseOctetString) Int.parse)
          (Seq.nosubstrings (Seq.nosubstrings (Seq.nosubstrings (Seq.nosubstrings (λ where _ refl refl → refl) TLV.nosubstrings) TLV.nosubstrings) TLV.nosubstrings) TLV.nosubstrings) (tell $ here' String.++ ": overflow"))
        λ where
          {bs} (singleton read read≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
              (Option.parseOption₁ExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow") Int.parse (n - read)))

parseEcParams :  Parser (Logging ∘ Dec) EcParams
parseEcParams = parseTLV _ "EC params" _ parseEcParamsFields

parseEcPkAlgParams : Parser (Logging ∘ Dec) EcPkAlgParams
runParser parseEcPkAlgParams xs = do
  no ¬ecparams ← runParser parseEcParams xs
    where yes p → return (yes (mapSuccess (λ x → ecparams x) p))
  no ¬namedcurve ← runParser parseOID xs
    where yes q → return (yes (mapSuccess (λ x → namedcurve x) q))
  no ¬impca ← runParser parseNull xs
    where yes r → return (yes (mapSuccess implicitlyCA r))
  return ∘ no $ λ where
   (success prefix read read≡ (ecparams x) suffix ps≡) →
     contradiction (success _ _ read≡ x _ ps≡) ¬ecparams
   (success prefix read read≡ (namedcurve x) suffix ps≡) →
     contradiction (success _ _ read≡ x _ ps≡) ¬namedcurve
   (success prefix read read≡ (implicitlyCA x) suffix ps≡) →
     contradiction (success _ _ read≡ x _ ps≡) ¬impca
