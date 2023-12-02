open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.KU.TCB where

open Aeres.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
--      id-ce-keyUsage OBJECT IDENTIFIER ::=  { id-ce 15 }

--       KeyUsage ::= BIT STRING {
--            digitalSignature        (0),
--            nonRepudiation          (1), -- recent editions of X.509 have
--                                 -- renamed this bit to contentCommitment
--            keyEncipherment         (2),
--            dataEncipherment        (3),
--            keyAgreement            (4),
--            keyCertSign             (5),
--            cRLSign                 (6),
--            encipherOnly            (7),
--            decipherOnly            (8) }

KUFields : @0 List UInt8 → Set
KUFields xs = TLV Tag.OctetString BitString xs

RawKUFields : Raw KUFields
RawKUFields = RawTLV _ RawBitString
