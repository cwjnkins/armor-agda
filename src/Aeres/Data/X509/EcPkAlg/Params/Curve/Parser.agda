{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.EcPkAlg.Params.Curve.Properties
open import Aeres.Data.X509.EcPkAlg.Params.Curve.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.EcPkAlg.Params.Curve.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

private
  here' = "parseCurveFields"

parseCurveFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength CurveFields n)
parseCurveFields n =
  parseEquivalent
    (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ equivalent))
    (parse&ᵈ (withinLength-nonnesting (NonNesting&ₚ TLV.nonnesting  TLV.nonnesting))
      (withinLength-unambiguous
        (unambiguous&ₚ (TLV.unambiguous OctetString.unambiguous)
          TLV.nonnesting (TLV.unambiguous OctetString.unambiguous)))
        (parse≤ n (parse& TLV.nonnesting  parseOctetString parseOctetString)
          (NonNesting&ₚ TLV.nonnesting TLV.nonnesting) ((tell $ here' String.++ ": overflow")))
          λ where
            {bs} (singleton read read≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
                (parseOption₁ExactLength TLV.nonempty TLV.nonnesting
                  (tell $ here' String.++ ": underflow") parseBitstring (n - read)))

parseCurve : Parser (Logging ∘ Dec) Curve
parseCurve = parseTLV _ "Curve" _ parseCurveFields

