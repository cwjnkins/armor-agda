open import Armor.Binary
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X509.CRL.Extension.IDP.Properties as Prop
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Properties
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Boool
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Option
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.IDP.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: CRL: CertList: TBSCertList: Extension: IDP"

parseIDPFieldsSeqFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength IDPFieldsSeqFields n)
parseIDPFieldsSeqFields n =
  parseEquivalent (Parallel.equivalent₁ equivalentIDPFieldsSeqFields) $
    mkParser λ xs → do
      (yes (success pre r r≡ (mk×ₚ (mk×ₚ v vLen) ne) suf ps≡)) ← runParser
            (parseSigma{B = λ where _ (mk×ₚ idp _) → T (notEmpty (fstₚ idp) (fstₚ(sndₚ idp)) (fstₚ (sndₚ(sndₚ idp)))
                                                               (fstₚ(sndₚ (sndₚ(sndₚ idp)))) (fstₚ(sndₚ(sndₚ (sndₚ(sndₚ idp)))))
                                                               (sndₚ(sndₚ(sndₚ (sndₚ(sndₚ idp))))))}
              (Parallel.ExactLength.nosubstrings _) (Parallel.ExactLength.unambiguous _ uaRep)
              p λ _ → T-dec)
            xs
        where no ¬p → return ∘ no $ λ where
          (success pre r r≡ (mk×ₚ (mk×ₚ v ne) vLen) suf ps≡) →
            contradiction
              (success pre r r≡ (mk×ₚ (mk×ₚ v vLen) ne) suf ps≡)
              ¬p
      return (yes
        (success
          pre r r≡ (mk×ₚ (mk×ₚ v ne) vLen) suf ps≡))
  where
  p : Parser (Logging ∘ Dec) (ExactLength RepIDPField n)
  p = Sequence.parseOption₂Default₄ _ _ _ _ here'
        Name.unambiguous TLV.nosubstrings TLV.nonempty
        (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
        (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
        (TLV.unambiguous BitString.unambiguousValue) TLV.nosubstrings TLV.nonempty
        (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
        (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
        (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))
        (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))
        (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))
        (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))
        (parseTLV Tag.AA0 (here' String.++ " (name)") DistPointNameChoice
          (parseExactLength Name.nosubstrings (tell $ here' String.++ ": underflow") parseDistPointNameChoice))
        (parseTLV Tag.A81 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
        (parseTLV Tag.A82 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
        (parseTLV Tag.A83 here' _ parseBitstringValue)
        (parseTLV Tag.A84 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
        (parseTLV Tag.A85 here' _ (parseExactLength Boool.nosubstrings (tell $ here' String.++ ": underflow") Boool.parseValue))
        n

parseIDPFields : Parser (Logging ∘ Dec) IDPFields
parseIDPFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseTLV _ here' _
        parseIDPFieldsSeqFields))
