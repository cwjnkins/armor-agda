open import Armor.Binary
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.CRL.Version.TCB
open import Armor.Data.X509.CRL.Extension.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import      Armor.Grammar.Option
open import Armor.Prelude

module Armor.Data.X509.CRL.TBSCertList.TCB where

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

record TBSCertListFields (@0 bs : List UInt8) : Set where
  constructor mkTBSCertListFields
  field
    @0 {ver sa i tu nu r e} : List UInt8
    version : Option Version ver
    signAlg : SignAlg sa
    issuer  : Name i
    thisUpdate : Time tu
    nextUpdate : Option Time nu
    revokedCertificates : Option EntryExtensions e
    crlExtensions : Option Extensions e
    @0 bs≡  : bs ≡ ver ++ sa ++ i ++ tu ++ nu ++ r ++ e

TBSCertList : (@0 _ : List UInt8) → Set
TBSCertList xs = TLV Tag.Sequence TBSCertListFields xs
