open import Armor.Binary
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Properties
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: Extension: CRLDistPoint: DistPoint"

parseDistPointFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength DistPointFields n)
parseDistPointFields n =
  parseEquivalent (Parallel.equivalent₁ equivalentDistPointFields) $
    mkParser λ xs → do
      (yes (success pre r r≡ (mk×ₚ (mk×ₚ v vLen) nor) suf ps≡)) ← runParser
            (parseSigma{B = λ where _ (mk×ₚ crls _) → T (notOnlyReasons (fstₚ (sndₚ crls)) (fstₚ crls) (sndₚ (sndₚ crls)))}
              (Parallel.ExactLength.nosubstrings _) (Parallel.ExactLength.unambiguous _ unambiguous')
              p λ _ → T-dec)
            xs
        where no ¬p → return ∘ no $ λ where
          (success pre r r≡ (mk×ₚ (mk×ₚ v nor) vLen) suf ps≡) →
            contradiction
              (success pre r r≡ (mk×ₚ (mk×ₚ v vLen) nor) suf ps≡)
              ¬p
      return (yes
        (success
          pre r r≡ (mk×ₚ (mk×ₚ v nor) vLen) suf ps≡))
  where
  p : Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option DistPointName) (&ₚ (Option ReasonFlags) (Option CrlIssuer))) n)
  p = parse₂Option₃ here'
        TLV.nosubstrings TLV.nosubstrings TLV.nosubstrings
        (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
        (parseTLV Tag.AA0 (here' String.++ " (name)") DistPointNameChoice
          (parseExactLength Name.nosubstrings (tell $ here' String.++ ": underflow")
            parseDistPointNameChoice))
        (parseTLV Tag.A81 (here' String.++ " (reason flags)") _ parseBitstringValue)
        (parseTLV Tag.AA2 (here' String.++ " (CRL issuer)") _ parseGeneralNamesElems)
        n

parseDistPoint : Parser (Logging ∘ Dec) DistPoint
parseDistPoint =
  parseTLV _ here' _ parseDistPointFields
