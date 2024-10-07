open import Armor.Binary
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.CRL.TBSCertList.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.CRL.CertList.TCB where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8


-- CertificateList  ::=  SEQUENCE  {
--         tbsCertList          TBSCertList,
--         signatureAlgorithm   AlgorithmIdentifier,
--         signatureValue       BIT STRING  }

record CertListFields (@0 bs : List UInt8) : Set where
  constructor mkCertListFields
  field
    @0 {t sa sig} : List UInt8
    tbs : TBSCertList t
    signAlg : SignAlg sa
    signature : BitString sig
    @0 bs≡  : bs ≡ t ++ sa ++ sig

CertList : (@0 _ : List UInt8) → Set
CertList xs = TLV Tag.Sequence  CertListFields xs
