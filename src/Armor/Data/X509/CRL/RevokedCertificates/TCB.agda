open import Armor.Binary
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Int.TCB
open import Armor.Data.X690-DER.SequenceOf.TCB
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import      Armor.Grammar.Option
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.TCB where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

-- TBSCertList  ::=  SEQUENCE  {
--      version                 Version OPTIONAL,
--                                   -- if present, MUST be v2
--      signature               AlgorithmIdentifier,
--      issuer                  Name,
--      thisUpdate              Time,
--      nextUpdate              Time OPTIONAL,
--      revokedCertificates     SEQUENCE OF SEQUENCE  {
--           userCertificate         CertificateSerialNumber,
--           revocationDate          Time,
--           crlEntryExtensions      Extensions OPTIONAL
--                                    -- if present, version MUST be v2
--                                }  OPTIONAL,
--      crlExtensions           [0]  EXPLICIT Extensions OPTIONAL
--                                    -- if present, version MUST be v2
--                                }

record RevokedCertificateFields (@0 bs : List UInt8) : Set where
  constructor mkRevokedCertificateFields
  field
    @0 {ser ti ex} : List UInt8
    cserial : Int ser
    rdate : Time ti
    entryextensions : Option {!EntryExtensions!} ex
    @0 bs≡  : bs ≡ ser ++ ti ++ ex


RevokedCertificate : (@0 _ : List UInt8) → Set
RevokedCertificate xs = TLV Tag.Sequence RevokedCertificateFields xs

RevokedCertificates : (@0 _ : List UInt8) → Set
RevokedCertificates xs = TLV Tag.Sequence (NonEmptySequenceOf RevokedCertificate) xs
