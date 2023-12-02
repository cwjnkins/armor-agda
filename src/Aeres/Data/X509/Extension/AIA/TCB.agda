open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.TCB where

open Aeres.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.2.1
--    id-pe-authorityInfoAccess OBJECT IDENTIFIER ::= { id-pe 1 }

--    AuthorityInfoAccessSyntax  ::=
--            SEQUENCE SIZE (1..MAX) OF AccessDescription

--    AccessDescription  ::=  SEQUENCE {
--            accessMethod          OBJECT IDENTIFIER,
--            accessLocation        GeneralName  }

--    id-ad OBJECT IDENTIFIER ::= { id-pkix 48 }

--    id-ad-caIssuers OBJECT IDENTIFIER ::= { id-ad 2 }

--    id-ad-ocsp OBJECT IDENTIFIER ::= { id-ad 1 }
           
AIAFieldsSeq : @0 List UInt8 → Set
AIAFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf AccessDesc) xs

AIAFields : @0 List UInt8 → Set
AIAFields xs = TLV Tag.OctetString AIAFieldsSeq xs

RawAIAFields : Raw AIAFields
RawAIAFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawAccessDesc 1))
