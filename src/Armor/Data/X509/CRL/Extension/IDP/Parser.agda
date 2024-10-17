open import Armor.Binary
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Properties
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
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

-- open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
-- open import Armor.Data.X690-DER.BitString.TCB
-- open import Armor.Data.X690-DER.TLV.TCB
-- open import Armor.Data.X690-DER.TLV.Properties
-- import      Armor.Data.X690-DER.Tag as Tag

-- open import Armor.Data.X690-DER.Boool.TCB
-- open import Armor.Data.X690-DER.SequenceOf.TCB
-- open import Armor.Data.X690-DER.Boool.Eq
-- import      Armor.Grammar.Definitions
-- import      Armor.Grammar.Option
-- import      Armor.Grammar.Parallel
-- import      Armor.Grammar.Seq.TCB

module Armor.Data.X509.CRL.Extension.IDP.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: CRL: CertList: TBSCertList: Extension: IDP"

postulate
  parseIDPFieldsSeqFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength IDPFieldsSeqFields n)
-- parseIDPFieldsSeqFields n = {!!}
--   where

--   p : Parser (Logging ∘ Dec) (ExactLength (&ₚ (Option DistPointName)
--              (&ₚ (Default [ Tag.A81 ]Boool [ Tag.A81 ]falseBoool)
--                  (Default [ Tag.A82 ]Boool [ Tag.A82 ]falseBoool))) n)
--   p =





-- -- case parse₂Option₃ here' TLV.nosubstrings TLV.nosubstrings TLV.nosubstrings
-- --                          (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
-- --                          (parseTLV Tag.AA0 (here' String.++ " (name)") DistPointNameChoice
-- --                            (parseExactLength Name.nosubstrings (tell $ here' String.++ ": underflow")
-- --                             parseDistPointNameChoice))
-- --                          (parseTLV Tag.A81 here' _ {!!})
-- --                          (parseTLV Tag.A82 here' _ {!!})
-- --                          n of λ where
-- --             v → {!!}


parseIDPFields : Parser (Logging ∘ Dec) IDPFields
parseIDPFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseTLV _ here' _
        parseIDPFieldsSeqFields))
