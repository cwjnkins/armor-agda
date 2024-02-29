open import Armor.Binary
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X509.Extension.KU.TCB where

open Armor.Grammar.Definitions UInt8

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

module KUFields where
  BitField = Fin 9

  digitalSignature nonRepudation keyEncipherment dataEncipherment keyAgreement keyCertSign cRLSign encipherOnly decipherOnly : BitField

  digitalSignature = # 0
  nonRepudation    = # 1
  keyEncipherment  = # 2
  dataEncipherment = # 3
  keyAgreement     = # 4
  keyCertSign      = # 5
  cRLSign          = # 6
  encipherOnly     = # 7
  decipherOnly     = # 8

  getBitField : ∀ {@0 bs} → KUFields bs → BitField → Bool
  getBitField ku bf =
    case toℕ bf <? length bitFields of λ where
      (no  bf≮len) → false
      (yes bf<len) → lookup bitFields (Fin.fromℕ< bf<len)
    where
    bitFields = ↑ BitStringValue.bits (TLV.val (TLV.val ku))

RawKUFields : Raw KUFields
RawKUFields = RawTLV _ RawBitString
