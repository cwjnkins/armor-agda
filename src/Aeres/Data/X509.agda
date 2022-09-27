{-# OPTIONS --subtyping --inversion-max-depth=1000 #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509 where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Sum         UInt8

open import Aeres.Data.X690-DER public

------------------------------X.509-----------------------------------------------------------

module X509 where

  record IA5StringValue (@0 bs : List Dig) : Set where
    constructor mkIA5StringValue
    field
      str : OctetStringValue bs
      @0 all<128 : All (Fin._< # 128) (Singleton.x str)

  module SOID where
    -- NOTE: These are proven to be OIDs after the fact (see Aeres.Data.X509.Decidable.OID)
    Md5Rsa : List Dig
    Md5Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 4 ]

    Sha1Rsa : List Dig
    Sha1Rsa =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 5 ]

    RsaPss : List Dig
    RsaPss =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 10 ]

    Sha256Rsa : List Dig
    Sha256Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 11 ]

    Sha384Rsa : List Dig
    Sha384Rsa =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 12 ]

    Sha512Rsa : List Dig
    Sha512Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 13 ]

    Sha224Rsa : List Dig
    Sha224Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 14 ]

  module PKOID where
    RsaEncPk : List Dig
    RsaEncPk = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ]

    EcPk : List Dig
    EcPk = Tag.ObjectIdentifier ∷ # 7 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 2 ∷ [ # 1 ]

    Supported : List (List Dig)
    Supported = RsaEncPk ∷ [ EcPk ]

  ExpNull : List Dig
  ExpNull = # 5 ∷ [ # 0 ]

  module SignAlg where
  
    record SignAlgFields (@0 bs : List Dig) : Set where
      constructor mkSignAlgFields
      field
        @0 {o p} : List Dig
        signOID : OID o
        param : Option (NotEmpty OctetStringValue) p
        @0 bs≡  : bs ≡ o ++ p

    SignAlg : (@0 _ : List Dig) → Set
    SignAlg xs = TLV Tag.Sequence SignAlgFields xs

    getSignAlgOIDbs : ∀ {@0 bs} → SignAlg bs → List UInt8
    getSignAlgOIDbs = Singleton.x ∘ OID.serialize ∘ SignAlgFields.signOID ∘ TLV.val

   
  open SignAlg public using (SignAlg)

 --------------- RDNSeq -------------------------------------

  TeletexString : (@0 _ : List Dig) → Set
  TeletexString xs = TLV Tag.TeletexString  OctetStringValue xs

  PrintableString : (@0 _ : List Dig) → Set
  PrintableString xs = TLV Tag.PrintableString  IA5StringValue xs

  UniversalString : (@0 _ : List Dig) → Set
  UniversalString xs = TLV Tag.UniversalString  UTF8 xs

  UTF8String : (@0 _ : List Dig) → Set
  UTF8String xs = TLV Tag.UTF8String  UTF8 xs

  BMPString : (@0 _ : List Dig) → Set
  BMPString xs = TLV Tag.BMPString  UTF8 xs

  IA5String : (@0 _ : List Dig) → Set
  IA5String xs = TLV Tag.IA5String  IA5StringValue xs

  -- TODO: check this (is it UTF8?)
  VisibleString : (@0 _ : List Dig) → Set
  VisibleString xs = TLV Tag.VisibleString  UTF8 xs

  data DirectoryString : @0 List Dig → Set where
    teletexString : ∀ {@0 bs} → Σₚ TeletexString TLVNonEmptyVal bs → DirectoryString bs
    printableString : ∀ {@0 bs} → Σₚ PrintableString TLVNonEmptyVal bs → DirectoryString bs
    universalString : ∀ {@0 bs} → Σₚ UniversalString TLVNonEmptyVal bs → DirectoryString bs
    utf8String : ∀ {@0 bs} → Σₚ UTF8String TLVNonEmptyVal bs → DirectoryString bs
    bmpString  : ∀ {@0 bs} → Σₚ BMPString  TLVNonEmptyVal bs → DirectoryString bs

  data DisplayText : @0 List Dig → Set where
    ia5String     : ∀ {@0 bs} → Σₚ IA5String     (TLVLenBounded 1 200) bs → DisplayText bs
    visibleString : ∀ {@0 bs} → Σₚ VisibleString (TLVLenBounded 1 200) bs → DisplayText bs
    bmpString     : ∀ {@0 bs} → Σₚ BMPString     (TLVLenBounded 1 200) bs → DisplayText bs
    utf8String    : ∀ {@0 bs} → Σₚ UTF8String    (TLVLenBounded 1 200) bs → DisplayText bs

  record RDNATVFields (@0 bs : List Dig) : Set where
    constructor mkRDNATVFields
    field
      @0 {o v} : List Dig
      oid : OID o
      val : DirectoryString v
      @0 bs≡  : bs ≡ o ++ v

  RDNATV : (@0 _ : List Dig) → Set
  RDNATV xs = TLV Tag.Sequence RDNATVFields xs

  RDNElems : @0 List Dig → Set
  RDNElems = NonEmptySequenceOf RDNATV

  RDN : (@0 _ : List Dig) → Set
  RDN = TLV Tag.Sett RDNElems

  module RDNSeq where
    RDNSeq : (@0 _ : List Dig) → Set
    RDNSeq = Seq RDN

    getRDNSeqLen : ∀ {@0 bs} → RDNSeq bs → ℕ
    getRDNSeqLen (mkTLV len val len≡ bs≡) = lengthSequence val
  open RDNSeq public using (RDNSeq)

----------------------- Generalnames --------------------

  --- we do not support OtherName since very rarely used
  OtherName : (@0 _ : List Dig) → Set
  OtherName xs = TLV Tag.AA0 OctetStringValue xs --abstracted

  RfcName : (@0 _ : List Dig) → Set
  RfcName xs = TLV Tag.A81 IA5StringValue xs

  DnsName : (@0 _ : List Dig) → Set
  DnsName xs = TLV Tag.A82 IA5StringValue xs

  --- we do not support X400Address since very rarely used
  X400Address : (@0 _ : List Dig) → Set
  X400Address xs = TLV Tag.AA3 OctetStringValue xs --abstracted

  DirName : (@0 _ : List Dig) → Set
  DirName xs = TLV Tag.AA4 (SequenceOf RDN) xs

  --- we do not support EdipartyName since very rarely used
  EdipartyName : (@0 _ : List Dig) → Set
  EdipartyName xs = TLV Tag.AA5 OctetStringValue xs --abstracted

  URI : (@0 _ : List Dig) → Set
  URI xs = TLV Tag.A86 IA5StringValue xs

  IpAddress : (@0 _ : List Dig) → Set
  IpAddress xs = TLV Tag.A87 OctetStringValue xs

  RegID : (@0 _ : List Dig) → Set
  RegID xs = TLV Tag.A88 (NonEmptySequenceOf OIDSub) xs

  data GeneralName : @0 List Dig → Set where
    oname : ∀ {@0 bs} → OtherName bs → GeneralName bs
    rfcname : ∀ {@0 bs} → RfcName bs → GeneralName bs
    dnsname : ∀ {@0 bs} → DnsName bs → GeneralName bs
    x400add : ∀ {@0 bs} → X400Address bs → GeneralName bs
    dirname : ∀ {@0 bs} → DirName bs → GeneralName bs
    ediname : ∀ {@0 bs} → EdipartyName bs → GeneralName bs
    uri : ∀ {@0 bs} → URI bs → GeneralName bs
    ipadd : ∀ {@0 bs} → IpAddress bs → GeneralName bs
    rid : ∀ {@0 bs} → RegID bs → GeneralName bs

  GeneralNamesElems = NonEmptySequenceOf GeneralName
  GeneralNames = TLV Tag.Sequence GeneralNamesElems

  --------------------------TBSCert-----------------------------------------------------------------

  module Version where
    Version : (@0 _ : List Dig) → Set
    Version xs = TLV Tag.AA0 Int xs

    getVal : ∀ {@0 bs} → Version bs → ℤ
    getVal v = Int.getVal (TLV.val v)
  open Version public using (Version)

  IssUID : (@0 _ : List Dig) → Set
  IssUID xs = TLV Tag.A81 BitStringValue xs

  SubUID : (@0 _ : List Dig) → Set
  SubUID xs = TLV Tag.A82 BitStringValue xs

--------------------------------------------------------- Validity --------------------------------
  record ValidityFields (@0 bs : List Dig) : Set where
    --- move getter in Generic.Time
    constructor mkValidityFields
    field
      @0 {nb na} : List Dig
      start : Time nb
      end : Time na
      @0 bs≡  : bs ≡ nb ++ na

  module Validity where
    Validity : (@0 _ : List Dig) → Set
    Validity xs = TLV Tag.Sequence ValidityFields xs

    getYearNB : ∀ {@0 bs} → Validity bs →  ℕ
    getYearNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getYear start
    getMonthNB : ∀ {@0 bs} → Validity bs →  ℕ
    getMonthNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMonth start
    getDayNB : ∀ {@0 bs} → Validity bs →  ℕ
    getDayNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getDay start
    getHourNB : ∀ {@0 bs} → Validity bs →  ℕ
    getHourNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getHour start
    getMinNB : ∀ {@0 bs} → Validity bs →  ℕ
    getMinNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMin start
    getSecNB : ∀ {@0 bs} → Validity bs →  ℕ
    getSecNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getSec start

    getYearNA : ∀ {@0 bs} → Validity bs →  ℕ
    getYearNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getYear end
    getMonthNA : ∀ {@0 bs} → Validity bs →  ℕ
    getMonthNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMonth end
    getDayNA : ∀ {@0 bs} → Validity bs →  ℕ
    getDayNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getDay end
    getHourNA : ∀ {@0 bs} → Validity bs →  ℕ
    getHourNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getHour end
    getMinNA : ∀ {@0 bs} → Validity bs →  ℕ
    getMinNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMin end
    getSecNA : ∀ {@0 bs} → Validity bs →  ℕ
    getSecNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getSec end
    
  open Validity public using (Validity)

-----------------------------------------Public Key------------------------------------------
 
  record CurveFields (@0 bs : List Dig) : Set where
    constructor mkCurveFields
    field
      @0 {p q r} : List Dig
      a : OctetString p
      b : OctetString q
      seed : Option BitString r
      @0 bs≡  : bs ≡ p ++ q ++ r

  Curve : (@0 _ : List Dig) → Set
  Curve xs = TLV Tag.Sequence CurveFields xs

  FieldID : (@0 _ : List Dig) → Set
  FieldID xs = TLV Tag.Sequence OctetStringValue xs
 
  record EcParamsFields (@0 bs : List Dig) : Set where
    constructor mkEcParamsFields
    field
      @0 {f c b o cf} : List Dig
      version : Singleton (# 2 ∷ # 1 ∷ [ # 1 ])
      fieldID : FieldID f
      curve : Curve c
      base : OctetString b
      order : Int o
      cofactor : Option Int cf
      @0 bs≡  : bs ≡ Singleton.x version ++ f ++ c ++ b ++ o ++ cf

  EcParams : (@0 _ : List Dig) → Set
  EcParams xs = TLV Tag.Sequence EcParamsFields xs

  data EcPkAlgParams : @0 List Dig → Set where
    ecparams : ∀ {@0 bs} → EcParams bs → EcPkAlgParams bs
    namedcurve : ∀ {@0 bs} → OID bs → EcPkAlgParams bs
    implicitlyCA : ∀ {@0 bs} → (bs ≡ ExpNull) → EcPkAlgParams bs

  record EcPkAlgFields (@0 bs : List Dig) : Set where
    constructor mkEcPkAlgFields
    field
      @0 {p} : List Dig
      oid : Singleton PKOID.EcPk
      param : EcPkAlgParams p
      @0 bs≡  : bs ≡ (Singleton.x oid) ++ p

  EcPkAlg : (@0 _ : List Dig) → Set
  EcPkAlg xs = TLV Tag.Sequence EcPkAlgFields xs

  record RSAPkIntsFields (@0 bs : List Dig) : Set where
    constructor mkRSAPkIntsFields
    field
      @0 {n e} : List Dig
      nval : Int n 
      eval : Int e
      @0 bs≡ : bs ≡ n ++ e

  RSAPkInts : (@0 _ : List Dig) → Set
  RSAPkInts xs = TLV Tag.Sequence RSAPkIntsFields xs
  
  record RSABitStringFields (@0 bs : List Dig) : Set where
    constructor mkRSABitStringFields
    field
      @0 {neseq} : List Dig
      z : Singleton ([ # 0 ]) 
      rsane : RSAPkInts neseq
      @0 bs≡ : bs ≡ (Singleton.x z) ++ neseq

  RSABitString : @0 List UInt8 → Set
  RSABitString xs = TLV Tag.BitString RSABitStringFields xs

  record RSAPkAlgFields (@0 bs : List Dig) : Set where
    constructor mkRSAPkAlgFields
    field
      oid : Singleton PKOID.RsaEncPk
      param : Singleton ExpNull
      @0 bs≡  : bs ≡ (Singleton.x oid) ++ (Singleton.x param)

  RSAPkAlg : (@0 _ : List Dig) → Set
  RSAPkAlg xs = TLV Tag.Sequence RSAPkAlgFields xs

  module PkAlg where
    data PkAlg : @0 List UInt8 → Set where
      rsapkalg : ∀ {@0 bs} → RSAPkAlg bs → PkAlg bs
      ecpkalg :  ∀ {@0 bs} → EcPkAlg bs → PkAlg bs
      otherpkalg : ∀ {@0 bs} → (sa : SignAlg bs) → False (SignAlg.getSignAlgOIDbs sa ∈? PKOID.Supported) → PkAlg bs

    getOID : ∀ {@0 bs} → PkAlg bs → List UInt8
    getOID (rsapkalg x) = (Singleton.x ∘ RSAPkAlgFields.oid) ∘ TLV.val $ x
    getOID (ecpkalg x) = (Singleton.x ∘ EcPkAlgFields.oid) ∘ TLV.val $ x
    getOID (otherpkalg x _) = SignAlg.getSignAlgOIDbs x

  open PkAlg public using (PkAlg) hiding (module PkAlg)

  data PkVal : @0 List UInt8 → @0 List UInt8 → Set where
    rsapkbits : ∀ {@0 o bs} → (o≡ : o ≡ PKOID.RsaEncPk) → RSABitString bs → PkVal o bs
    ecpkbits : ∀ {@0 o bs} → (o≡ : o ≡ PKOID.EcPk) → BitString bs → PkVal o bs
    otherpkbits :  ∀ {@0 o bs} → (o∉ : False (o ∈? PKOID.Supported)) → BitString bs → PkVal o bs

  record PublicKeyFields (@0 bs : List Dig) : Set where
    constructor mkPublicKeyFields
    field
      @0 {alg pk} : List Dig
      pkalg : PkAlg alg
      pubkey : PkVal (PkAlg.getOID pkalg) pk
      @0 bs≡ : bs ≡ alg ++ pk

  PublicKey : (@0 _ : List Dig) → Set
  PublicKey xs = TLV Tag.Sequence PublicKeyFields xs
 
-----------------------------------------Extensions------------------------------------------
 ----------------------- aki extension -------------------

  AKIKeyId : (@0 _ : List Dig) → Set
  AKIKeyId xs = TLV Tag.A80 OctetStringValue xs

  AKIAuthCertIssuer : (@0 _ : List Dig) → Set
  AKIAuthCertIssuer xs = TLV Tag.AA1 GeneralNamesElems xs

  AKIAuthCertSN : (@0 _ : List Dig) → Set
  AKIAuthCertSN xs = TLV Tag.A82  IntegerValue xs

  record AKIFieldsSeqFields (@0 bs : List Dig) : Set where
    constructor mkAKIFieldsSeqFields
    field
      @0 {akid ci csn} : List Dig
      akeyid : Option AKIKeyId akid
      authcertiss : Option AKIAuthCertIssuer ci
      authcertsn : Option AKIAuthCertSN csn
      @0 bs≡  : bs ≡ akid ++ ci ++ csn

  AKIFieldsSeq : (@0 _ : List Dig) → Set
  AKIFieldsSeq xs = TLV Tag.Sequence  AKIFieldsSeqFields xs

  AKIFields : (@0 _ : List Dig) → Set
  AKIFields xs = TLV Tag.OctetString  AKIFieldsSeq xs
------------------------------------------------------------------------------------------

  SKIFields : (@0 _ : List Dig) → Set
  SKIFields xs = TLV Tag.OctetString  OctetString xs

  KUFields : (@0 _ : List Dig) → Set
  KUFields xs = TLV Tag.OctetString  BitString xs

----------------------------------- eku extension -----------------------------------

  EKUFieldsSeq : (@0 _ : List Dig) → Set
  EKUFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf OID) xs

  EKUFields : (@0 _ : List Dig) → Set
  EKUFields xs = TLV Tag.OctetString  EKUFieldsSeq xs

-------------------------------------------------------------------------------

  record BCFieldsSeqFields (@0 bs : List Dig) : Set where
    constructor mkBCFieldsSeqFields
    field
      @0 {ca pl} : List Dig
      bcca : Option Boool ca
      bcpathlen : Option Int pl
      @0 bs≡  : bs ≡ ca ++ pl

  BCFieldsSeq : (@0 _ : List Dig) → Set
  BCFieldsSeq xs = TLV Tag.Sequence  BCFieldsSeqFields xs

  BCFields : (@0 _ : List Dig) → Set
  BCFields xs = TLV Tag.OctetString  BCFieldsSeq xs

-------------------------- ian/san alternative names extensions ------------------
  IANFieldsSeq : (@0 _ : List Dig) → Set
  IANFieldsSeq = GeneralNames

  IANFields : (@0 _ : List Dig) → Set
  IANFields xs = TLV Tag.OctetString IANFieldsSeq xs

  SANFieldsSeq : (@0 _ : List Dig) → Set
  SANFieldsSeq = GeneralNames

  SANFields : (@0 _ : List Dig) → Set
  SANFields xs = TLV Tag.OctetString SANFieldsSeq xs

------------------------- certificate policies -------------------------
  module PQOID where
    CPSURI : List Dig
    CPSURI = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]

    USERNOTICE : List Dig
    USERNOTICE = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]

  record NoticeReferenceFields (@0 bs : List Dig) : Set where
    constructor mkNoticeReferenceFields
    field
      @0 {org nn} : List Dig
      organization : DisplayText org
      noticenums : IntegerSeq nn
      @0 bs≡  : bs ≡ org ++ nn

  NoticeReference : (@0 _ : List Dig) → Set
  NoticeReference xs = TLV Tag.Sequence NoticeReferenceFields xs

  record UserNoticeFields (@0 bs : List Dig) : Set where
    constructor mkUserNoticeFields
    field
      @0 {nr et} : List Dig
      noticeRef : Option NoticeReference nr
      expText : Option DisplayText et
      @0 bs≡  : bs ≡ nr ++ et

  UserNotice : (@0 _ : List Dig) → Set
  UserNotice xs = TLV Tag.Sequence UserNoticeFields xs

  record CPSURIQualifier (@0 bs : List Dig) : Set where
    constructor mkCPSURIQualifier
    field
      @0 {bs₁ bs₂} : List Dig
      ≡cpsuri : bs₁ ≡ PQOID.CPSURI
      cpsPointer : IA5String bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  record UserNoticeQualifier (@0 bs : List Dig) : Set where
    constructor mkUserNoticeQualifier
    field
      @0 {bs₁ bs₂} : List Dig
      ≡usernotice : bs₁ ≡ PQOID.USERNOTICE
      unotice : UserNotice bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data PolicyQualifierInfoFields : @0 List Dig → Set where
    cpsURI : ∀ {@0 bs} → CPSURIQualifier bs → PolicyQualifierInfoFields bs
    userNotice : ∀ {@0 bs} → UserNoticeQualifier bs → PolicyQualifierInfoFields bs

  PolicyQualifierInfo : (@0 _ : List Dig) → Set
  PolicyQualifierInfo xs = TLV Tag.Sequence PolicyQualifierInfoFields xs

  PolicyQualifiersSeq : (@0 _ : List Dig) → Set
  PolicyQualifiersSeq xs = TLV Tag.Sequence (NonEmptySequenceOf PolicyQualifierInfo) xs

  record PolicyInformationFields (@0 bs : List Dig) : Set where
    constructor mkPolicyInformationFields
    field
      @0 {pid pqls} : List Dig
      cpid : OID pid
      cpqls : Option PolicyQualifiersSeq pqls
      @0 bs≡  : bs ≡ pid ++ pqls

  PolicyInformation : (@0 _ : List Dig) → Set
  PolicyInformation xs = TLV Tag.Sequence PolicyInformationFields xs

  CertPolFieldsSeq : (@0 _ : List Dig) → Set
  CertPolFieldsSeq = TLV Tag.Sequence (NonEmptySequenceOf PolicyInformation)

  CertPolFields : (@0 _ : List Dig) → Set
  CertPolFields xs = TLV Tag.OctetString  CertPolFieldsSeq xs

----------------------------- crl dist point extension --------------------------------

  CrlIssuer : (@0 _ : List Dig) → Set
  CrlIssuer xs = TLV Tag.AA2 GeneralNamesElems xs

  ReasonFlags : (@0 _ : List Dig) → Set
  ReasonFlags xs = TLV Tag.A81 BitStringValue xs

  FullName : (@0 _ : List Dig) → Set
  FullName xs = TLV Tag.AA0 GeneralNamesElems xs

  NameRTCrlIssuer : (@0 _ : List Dig) → Set
  NameRTCrlIssuer xs = TLV Tag.AA1 RDNElems xs

  data DistPointNameChoice : (@0 _ : List Dig) → Set where
    fullname : ∀ {@0 bs} → FullName bs → DistPointNameChoice bs
    nameRTCrlissr : ∀ {@0 bs} → NameRTCrlIssuer bs → DistPointNameChoice bs

  DistPointName : (@0 _ : List Dig) → Set
  DistPointName xs = TLV Tag.AA0  DistPointNameChoice xs

  record DistPointFields (@0 bs : List Dig) : Set where
    constructor mkDistPointFields
    field
      @0 {dp rsn issr} : List Dig
      crldp : Option DistPointName dp
      crldprsn : Option ReasonFlags rsn
      crlissr : Option CrlIssuer issr
      @0 bs≡  : bs ≡ dp ++ rsn ++ issr

  DistPoint : (@0 _ : List Dig) → Set
  DistPoint xs = TLV Tag.Sequence DistPointFields xs

  CRLDistFieldsSeq : (@0 _ : List Dig) → Set
  CRLDistFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf DistPoint) xs

  CRLDistFields : (@0 _ : List Dig) → Set
  CRLDistFields xs = TLV Tag.OctetString  CRLDistFieldsSeq xs

----------------------------------------- Authority Info access -----------------
  module ACMOID where
    CAISSUERS : List Dig
    CAISSUERS = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 2 ]

    OCSP : List Dig
    OCSP = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 1 ]

  data AccessMethod : @0 List Dig → Set where
    caissid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.CAISSUERS) → AccessMethod bs
    ocspid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.OCSP) → AccessMethod bs

  record AccessDescFields (@0 bs : List Dig) : Set where
    constructor mkAccessDescFields
    field
      @0 {acm acl} : List Dig
      acmethod : AccessMethod acm
      aclocation : GeneralName acl
      @0 bs≡  : bs ≡ acm ++ acl

  AccessDesc : (@0 _ : List Dig) → Set
  AccessDesc xs = TLV Tag.Sequence  AccessDescFields xs

  AIAFieldsSeq : (@0 _ : List Dig) → Set
  AIAFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf AccessDesc) xs

  AIAFields : (@0 _ : List Dig) → Set
  AIAFields xs = TLV Tag.OctetString  AIAFieldsSeq xs

------------------------------------ Name Constraints ---------------------------

  MinBaseDistance : (@0 _ : List Dig) → Set
  MinBaseDistance xs = TLV Tag.A80 IntegerValue xs

  MaxBaseDistance : (@0 _ : List Dig) → Set
  MaxBaseDistance xs = TLV Tag.A81 IntegerValue xs

  record GeneralSubtreeFields (@0 bs : List Dig) : Set where
    constructor mkGeneralSubtreeFields
    field
      @0 {bse minb maxb} : List Dig
      base : GeneralName bse
      minimum : Option MinBaseDistance minb
      maximum : Option MaxBaseDistance maxb
      @0 bs≡  : bs ≡ bse ++ minb ++ maxb

  GeneralSubtree : (@0 _ : List Dig) → Set
  GeneralSubtree xs = TLV Tag.Sequence GeneralSubtreeFields xs

  GeneralSubtrees : (@0 _ : List Dig) → Set
  GeneralSubtrees xs = TLV Tag.Sequence (NonEmptySequenceOf GeneralSubtree) xs

  PermittedSubtrees : (@0 _ : List Dig) → Set
  PermittedSubtrees xs = TLV Tag.AA0 GeneralSubtrees xs

  ExcludedSubtrees : (@0 _ : List Dig) → Set
  ExcludedSubtrees xs = TLV Tag.AA1 GeneralSubtrees xs

  record NCFieldsSeqFields (@0 bs : List Dig) : Set where
    constructor mkNCFieldsSeqFields
    field
      @0 {pe ex} : List Dig
      permt : Option PermittedSubtrees pe
      excld : Option ExcludedSubtrees ex
      @0 bs≡  : bs ≡ pe ++ ex

  NCFieldsSeq : (@0 _ : List Dig) → Set
  NCFieldsSeq xs = TLV Tag.Sequence NCFieldsSeqFields xs

  NCFields : (@0 _ : List Dig) → Set
  NCFields xs = TLV Tag.OctetString  NCFieldsSeq xs

------------------------------------ Policy Constraints ---------------------------

  RequireExplicitPolicy : (@0 _ : List Dig) → Set
  RequireExplicitPolicy xs = TLV Tag.A80 IntegerValue xs

  InhibitPolicyMapping : (@0 _ : List Dig) → Set
  InhibitPolicyMapping xs = TLV Tag.A81 IntegerValue xs

  record PCFieldsSeqFields (@0 bs : List Dig) : Set where
    constructor mkPCFieldsSeqFields
    field
      @0 {req ini} : List Dig
      require : Option RequireExplicitPolicy req
      ihibit : Option InhibitPolicyMapping ini
      @0 bs≡  : bs ≡ req ++ ini

  PCFieldsSeq : (@0 _ : List Dig) → Set
  PCFieldsSeq xs = TLV Tag.Sequence PCFieldsSeqFields xs

  PCFields : (@0 _ : List Dig) → Set
  PCFields xs = TLV Tag.OctetString  PCFieldsSeq xs

------------------------------------ Policy Mappings ---------------------------

  record PolicyMapFields (@0 bs : List Dig) : Set where
    constructor mkPolicyMapFields
    field
      @0 {iss sub} : List Dig
      issuerDomainPolicy : OID iss
      subjectDomainPolicy : OID sub
      @0 bs≡  : bs ≡ iss ++ sub

  PolicyMap : (@0 _ : List Dig) → Set
  PolicyMap xs = TLV Tag.Sequence PolicyMapFields xs

  PMFieldsSeq : (@0 _ : List Dig) → Set
  PMFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf PolicyMap) xs

  PMFields : (@0 _ : List Dig) → Set
  PMFields xs = TLV Tag.OctetString  PMFieldsSeq xs

------------------------------------ Inhibit anyPolicy ---------------------------

  INAPFields : (@0 _ : List Dig) → Set
  INAPFields xs = TLV Tag.OctetString Int xs

--------------------------------Extensions selection----------------------------------------

  module ExtensionOID where
    AKI : List Dig
    AKI = # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 35 ]

    SKI : List Dig
    SKI =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 14 ]

    KU : List Dig
    KU =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 15 ]

    EKU : List Dig
    EKU =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 37 ]

    BC : List Dig
    BC =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 19 ]

    IAN : List Dig
    IAN =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 18 ]

    SAN : List Dig
    SAN =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 17 ]

    CPOL : List Dig
    CPOL =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 32 ]

    CRLDIST : List Dig
    CRLDIST =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 31 ]

    NC : List Dig
    NC =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 30 ]

    PC : List Dig
    PC =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 36 ]

    PM : List Dig
    PM =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 33 ]

    INAP : List Dig
    INAP =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 54 ]

    AIA : List Dig
    AIA =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 1 ∷ [ # 1 ]

    Supported : List (List Dig)
    Supported = AKI ∷ SKI ∷ KU ∷ EKU ∷ BC ∷ IAN ∷ SAN ∷ CPOL ∷ CRLDIST ∷ NC ∷ PC ∷ PM ∷ INAP ∷ [ AIA ] 

  record ExtensionFields (@0 P : List Dig → Set) (A : @0 List Dig → Set) (@0 bs : List Dig) : Set where
    constructor mkExtensionFields
    field
      @0 {oex cex ocex} : List Dig
      extnId : OID oex
      @0 extnId≡ : P oex -- oex ≡ lit
      crit : Option Boool cex
      extension : A ocex
      @0 bs≡ : bs ≡ oex ++ cex ++ ocex

  data SelectExtn : @0 List Dig → Set where
    akiextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.AKI    )              AKIFields           bs → SelectExtn bs 
    skiextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.SKI    )              SKIFields           bs → SelectExtn bs 
    kuextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.KU     )              KUFields            bs → SelectExtn bs 
    ekuextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.EKU    )              EKUFields           bs → SelectExtn bs 
    bcextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.BC     )              BCFields            bs → SelectExtn bs 
    ianextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.IAN    )              IANFields           bs → SelectExtn bs 
    sanextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.SAN    )              SANFields           bs → SelectExtn bs 
    cpextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.CPOL   )              CertPolFields       bs → SelectExtn bs 
    crlextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.CRLDIST)              CRLDistFields       bs → SelectExtn bs 
    ncextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.NC     )              NCFields            bs → SelectExtn bs 
    pcextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.PC     )              PCFields            bs → SelectExtn bs 
    pmextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.PM     )              PMFields            bs → SelectExtn bs 
    inapextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.INAP )              INAPFields          bs → SelectExtn bs 
    aiaextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.AIA    )              AIAFields           bs → SelectExtn bs
    other   : ∀ {@0 bs} → ExtensionFields (False ∘ (_∈? ExtensionOID.Supported)) OctetString bs → SelectExtn bs

  module Extension where
    Extension : (@0 _ : List Dig) → Set
    Extension xs = TLV Tag.Sequence SelectExtn xs

    getBC : ∀ {@0 bs} → Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC (mkTLV len (bcextn x) len≡ bs≡) = _ , (some x)
    getBC (mkTLV len _ len≡ bs≡) = _ , none

    getKU : ∀ {@0 bs} → Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU (mkTLV len (kuextn x) len≡ bs≡) = _ , (some x)
    getKU (mkTLV len _ len≡ bs≡) = _ , none

    getSAN : ∀ {@0 bs} → Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN (mkTLV len (sanextn x) len≡ bs≡) = _ , (some x)
    getSAN (mkTLV len _ len≡ bs≡) = _ , none

    getCRLDIST : ∀ {@0 bs} → Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST (mkTLV len (crlextn x) len≡ bs≡) = _ , (some x)
    getCRLDIST (mkTLV len _ len≡ bs≡) = _ , none

    getCPOL : ∀ {@0 bs} → Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL (mkTLV len (cpextn x) len≡ bs≡) = _ , (some x)
    getCPOL (mkTLV len _ len≡ bs≡) = _ , none
  open Extension public using (Extension)

  module ExtensionsSeq where
    ExtensionsSeq : (@0 _ : List Dig) → Set
    ExtensionsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf Extension) xs

    getBC : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getBC h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getKU : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getKU h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getSAN : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getSAN h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getCRLDIST : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getCRLDIST h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getCPOL : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getCPOL h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getExtensionsList : ∀ {@0 bs} → ExtensionsSeq bs → List (Exists─ (List Dig) Extension)
    getExtensionsList (mkTLV len (mk×ₚ fstₚ₁ sndₚ₁ bs≡₁) len≡ bs≡) = helper fstₚ₁
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → List (Exists─ (List Dig) Extension)
      helper nil = []
      helper (consIList h t bs≡) = (_ , h) ∷ helper t
  open ExtensionsSeq public using (ExtensionsSeq)

  module Extensions where
    Extensions : (@0 _ : List Dig) → Set
    Extensions xs = TLV Tag.AA3  ExtensionsSeq xs

    getBC : ∀ {@0 bs} → Extensions bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC (mkTLV len val len≡ bs≡) = ExtensionsSeq.getBC val

    getKU : ∀ {@0 bs} → Extensions bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU (mkTLV len val len≡ bs≡) = ExtensionsSeq.getKU val

    getSAN : ∀ {@0 bs} → Extensions bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN (mkTLV len val len≡ bs≡) = ExtensionsSeq.getSAN val

    getCRLDIST : ∀ {@0 bs} → Extensions bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCRLDIST val

    getCPOL : ∀ {@0 bs} → Extensions bs → Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCPOL val

    getExtensionsList : ∀ {@0 bs} → Extensions bs → List (Exists─ (List Dig) Extension)
    getExtensionsList (mkTLV len val len≡ bs≡) = ExtensionsSeq.getExtensionsList val
  open Extensions public using (Extensions)

-----------------------------------------------------------------------------------------------

  record TBSCertFields (@0 bs : List Dig) : Set where
    constructor mkTBSCertFields
    field
      @0 {ver ser sa i va u p u₁ u₂ e} : List Dig
      version : Option Version ver
      serial  : Int ser
      signAlg : SignAlg sa
      issuer  : RDNSeq i
      validity : Validity va
      subject  : RDNSeq u
      pk       : PublicKey p
      issuerUID : Option IssUID u₁ -- if this takes a lot of time, this and the lower can be dropped
      subjectUID : Option SubUID u₂
      extensions : Option Extensions e
      @0 bs≡  : bs ≡ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

    getVersion : ℤ
    getVersion = elimOption{X = const ℤ} (ℤ.+ 0) (λ v → Version.getVal v) version

    getSerial : ℤ
    getSerial = Int.getVal serial

    getYearNB :  ℕ
    getYearNB = Validity.getYearNB validity
    getMonthNB :  ℕ
    getMonthNB = Validity.getMonthNB validity
    getDayNB :  ℕ
    getDayNB = Validity.getDayNB validity
    getHourNB :  ℕ
    getHourNB = Validity.getHourNB validity
    getMinNB :  ℕ
    getMinNB = Validity.getMinNB validity
    getSecNB :  ℕ
    getSecNB = Validity.getSecNB validity

    getYearNA :  ℕ
    getYearNA = Validity.getYearNA validity
    getMonthNA :  ℕ
    getMonthNA = Validity.getMonthNA validity
    getDayNA :  ℕ
    getDayNA = Validity.getDayNA validity
    getHourNA :  ℕ
    getHourNA = Validity.getHourNA validity
    getMinNA :  ℕ
    getMinNA = Validity.getMinNA validity
    getSecNA :  ℕ
    getSecNA = Validity.getSecNA validity

    getIssuerLen : ℕ
    getIssuerLen = RDNSeq.getRDNSeqLen issuer

    getSubjectLen :  ℕ
    getSubjectLen = RDNSeq.getRDNSeqLen subject

    getIssuer : Exists─ (List Dig) RDNSeq
    getIssuer = _ , issuer

    getSubject : Exists─ (List Dig) RDNSeq
    getSubject = _ , subject

    getSignAlg : Exists─ (List Dig) SignAlg
    getSignAlg = _ , signAlg

    getBC : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC = elimOption (_ , none) (λ v → Extensions.getBC v) extensions

    getKU : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU = elimOption (_ , none) (λ v → Extensions.getKU v) extensions

    getSAN : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN = elimOption (_ , none) (λ v → Extensions.getSAN v) extensions

    getCRLDIST : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST = elimOption (_ , none) (λ v → Extensions.getCRLDIST v) extensions

    getCPOL : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL = elimOption (_ , none) (λ v → Extensions.getCPOL v) extensions

    getExtensionsList : List (Exists─ (List Dig) Extension)
    getExtensionsList = elimOption [] (λ v → Extensions.getExtensionsList v) extensions
 
  TBSCert : (@0 _ : List Dig) → Set
  TBSCert xs = TLV Tag.Sequence TBSCertFields xs

  ---------------------------------Certificate---------------------------------------------------

  record CertFields (@0 bs : List Dig) : Set where
    constructor mkCertFields
    field
      @0 {t sa sig} : List Dig
      tbs : TBSCert t
      signAlg : SignAlg sa
      signature : BitString sig
      @0 bs≡  : bs ≡ t ++ sa ++ sig

    getVersion : ℤ
    getVersion = TBSCertFields.getVersion (TLV.val tbs)

    getSerial : ℤ
    getSerial = TBSCertFields.getSerial (TLV.val tbs)

    getYearNB :  ℕ
    getYearNB = TBSCertFields.getYearNB (TLV.val tbs)
    getMonthNB :  ℕ
    getMonthNB = TBSCertFields.getMonthNB (TLV.val tbs)
    getDayNB :  ℕ
    getDayNB = TBSCertFields.getDayNB (TLV.val tbs)
    getHourNB :  ℕ
    getHourNB = TBSCertFields.getHourNB (TLV.val tbs)
    getMinNB :  ℕ
    getMinNB = TBSCertFields.getMinNB (TLV.val tbs)
    getSecNB :  ℕ
    getSecNB = TBSCertFields.getSecNB (TLV.val tbs)

    getYearNA :  ℕ
    getYearNA = TBSCertFields.getYearNA (TLV.val tbs)
    getMonthNA :  ℕ
    getMonthNA = TBSCertFields.getMonthNA (TLV.val tbs)
    getDayNA :  ℕ
    getDayNA = TBSCertFields.getDayNA (TLV.val tbs)
    getHourNA :  ℕ
    getHourNA = TBSCertFields.getHourNA (TLV.val tbs)
    getMinNA :  ℕ
    getMinNA = TBSCertFields.getMinNA (TLV.val tbs)
    getSecNA :  ℕ
    getSecNA = TBSCertFields.getSecNA (TLV.val tbs)

    getIssuerLen :  ℕ
    getIssuerLen = TBSCertFields.getIssuerLen (TLV.val tbs)

    getSubjectLen :  ℕ
    getSubjectLen = TBSCertFields.getSubjectLen (TLV.val tbs)

    getIssuer :  Exists─ (List Dig) RDNSeq
    getIssuer = TBSCertFields.getIssuer (TLV.val tbs)

    getSubject :  Exists─ (List Dig) RDNSeq
    getSubject = TBSCertFields.getSubject (TLV.val tbs)

    getIssUID : Exists─ (List Dig) (Option IssUID)
    getIssUID = _ , (TBSCertFields.issuerUID (TLV.val tbs))

    getSubUID : Exists─ (List Dig) (Option SubUID)
    getSubUID = _ , (TBSCertFields.subjectUID (TLV.val tbs))

    getTBSCertSignAlg : Exists─ (List Dig) SignAlg
    getTBSCertSignAlg = TBSCertFields.getSignAlg (TLV.val tbs)
 
    getCertSignAlg : Exists─ (List Dig) SignAlg
    getCertSignAlg =  _ , signAlg

    getBC : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC = TBSCertFields.getBC (TLV.val tbs)

    getKU : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU = TBSCertFields.getKU (TLV.val tbs)

    getSAN : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN = TBSCertFields.getSAN (TLV.val tbs)

    getCRLDIST : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST = TBSCertFields.getCRLDIST (TLV.val tbs)

    getCPOL : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL = TBSCertFields.getCPOL (TLV.val tbs)

    getExtensions : Exists─ (List Dig) (Option Extensions)
    getExtensions = _ , (TBSCertFields.extensions (TLV.val tbs))
    
    getExtensionsList : List (Exists─ (List Dig) Extension)
    getExtensionsList = TBSCertFields.getExtensionsList (TLV.val tbs)

  module Cert where
    Cert : (@0 _ : List Dig) → Set
    Cert xs = TLV Tag.Sequence  CertFields xs

    module _ {@0 bs} (c : Cert bs) where
      getVersion : ℤ
      getVersion = CertFields.getVersion (TLV.val c)

      getSerial : ℤ
      getSerial = CertFields.getSerial (TLV.val c)

      getYearNB :  ℕ
      getYearNB = CertFields.getYearNB (TLV.val c)
      getMonthNB :  ℕ
      getMonthNB = CertFields.getMonthNB (TLV.val c)
      getDayNB :  ℕ
      getDayNB = CertFields.getDayNB (TLV.val c)
      getHourNB :  ℕ
      getHourNB = CertFields.getHourNB (TLV.val c)
      getMinNB :  ℕ
      getMinNB = CertFields.getMinNB (TLV.val c)
      getSecNB :  ℕ
      getSecNB = CertFields.getSecNB (TLV.val c)

      getYearNA :  ℕ
      getYearNA = CertFields.getYearNA (TLV.val c)
      getMonthNA :  ℕ
      getMonthNA = CertFields.getMonthNA (TLV.val c)
      getDayNA :  ℕ
      getDayNA = CertFields.getDayNA (TLV.val c)
      getHourNA :  ℕ
      getHourNA = CertFields.getHourNA (TLV.val c)
      getMinNA :  ℕ
      getMinNA = CertFields.getMinNA (TLV.val c)
      getSecNA :  ℕ
      getSecNA = CertFields.getSecNA (TLV.val c)

      getIssuerLen :  ℕ
      getIssuerLen = CertFields.getIssuerLen (TLV.val c)

      getSubjectLen :  ℕ
      getSubjectLen = CertFields.getSubjectLen (TLV.val c)

      getIssuer :  Exists─ (List Dig) RDNSeq
      getIssuer = CertFields.getIssuer (TLV.val c)

      getSubject :  Exists─ (List Dig) RDNSeq
      getSubject = CertFields.getSubject (TLV.val c)

      getIssUID : Exists─ (List Dig) (Option IssUID)
      getIssUID = CertFields.getIssUID (TLV.val c)

      getSubUID : Exists─ (List Dig) (Option SubUID)
      getSubUID = CertFields.getSubUID (TLV.val c)

      getTBSCertSignAlg : Exists─ (List Dig) SignAlg
      getTBSCertSignAlg = CertFields.getTBSCertSignAlg (TLV.val c)

      getCertSignAlg : Exists─ (List Dig) SignAlg
      getCertSignAlg = CertFields.getCertSignAlg (TLV.val c)

      getBC : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
      getBC = CertFields.getBC (TLV.val c)

      getKU : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
      getKU = CertFields.getKU (TLV.val c)

      getSAN : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
      getSAN = CertFields.getSAN (TLV.val c)

      getCRLDIST : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
      getCRLDIST = CertFields.getCRLDIST (TLV.val c)

      getCPOL : Exists─ (List Dig) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
      getCPOL = CertFields.getCPOL (TLV.val c)

      getExtensions : Exists─ (List Dig) (Option Extensions)
      getExtensions = CertFields.getExtensions (TLV.val c)
 
      getExtensionsList : List (Exists─ (List Dig) Extension)
      getExtensionsList = CertFields.getExtensionsList (TLV.val c)

  open Cert public using (Cert)

  module Chain where
    Chain : (@0 _ : List Dig) → Set
    Chain = IListNonEmpty Cert
  open Chain public using (Chain)
