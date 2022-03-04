{-# OPTIONS --subtyping --inversion-max-depth=1000 #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509 where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Sum         UInt8

open import Aeres.Data.X690-DER public

-------------------------------------------Generic---------------------------------------
module Generic where

  OIDLeastDigs : List Dig → Set
  OIDLeastDigs = maybe (Fin._> # 128) ⊤ ∘ head

  oidLeastDigs? : ∀ bs → Dec (OIDLeastDigs bs)
  oidLeastDigs? [] = yes tt
  oidLeastDigs? (x ∷ bs) = (# 128) Fin.<? x

  oidLeastDigs-unique : ∀ {bs} → Unique (OIDLeastDigs bs)
  oidLeastDigs-unique {[]} tt tt = refl
  oidLeastDigs-unique {x ∷ bs} x₁ x₂ = ≤-irrelevant x₁ x₂
    where open import Data.Nat.Properties

  record OIDSub (@0 bs : List Dig) : Set where
    constructor mkOIDSub
    field
      lₚ : List Dig
      @0 lₚ≥128 : All (λ d → toℕ d ≥ 128) lₚ
      lₑ   : Dig
      @0 lₑ<128 : toℕ lₑ < 128
      @0 leastDigs : OIDLeastDigs lₚ
      @0 bs≡ : bs ≡ lₚ ∷ʳ lₑ

  mkOIDSubₛ : (lₚ : List Dig) (lₑ : Dig) {@0 _ : True (All.all ((_≥? 128) ∘ toℕ) lₚ)} {@0 _ : True (oidLeastDigs? lₚ)} {@0 _ : True (lₑ Fin.<? # 128)} → OIDSub (lₚ ∷ʳ lₑ)
  mkOIDSubₛ lₚ lₑ {lₚ≥128}{leastDigs}{lₑ<128} = mkOIDSub lₚ (toWitness lₚ≥128) lₑ (toWitness lₑ<128) (toWitness leastDigs) refl

  --private
  --  oidsub₁ : OIDSub (# 134 ∷ [ # 72 ])
  --  oidsub₁ = mkOIDSub [ # 134 ] (toWitness{Q = All.all ((128 ≤?_) ∘ toℕ) _} tt) (# 72) (toWitness{Q = 72 <? 128} tt) (toWitness{Q = 134 >? 128} tt) refl

  OID : (@0 _ : List Dig) → Set
  OID = TLV Tag.ObjectIdentifier (NonEmptySequenceOf OIDSub)

  data BoolRep : Bool → Dig → Set where
    falseᵣ : BoolRep false (# 0)
    trueᵣ  : BoolRep true  (# 255)

  record BoolValue (@0 bs : List Dig) : Set where
    constructor mkBoolValue
    field
      v : Bool
      @0 b : Dig
      @0 vᵣ : BoolRep v b
      @0 bs≡ : bs ≡ [ b ]

  Boool : (@0 _ : List Dig) → Set
  Boool = TLV Tag.Boolean BoolValue

------------------------------Time------------------------------------------------------------

  MonthRange : (mo₁ mo₂ : Dig) → Set
  MonthRange mo₁ mo₂ =   mo₁ ≡ # '0' × InRange '0' '9' mo₂
                       ⊎ mo₁ ≡ # '1' × InRange '0' '2' mo₂

  DayRange : (d₁ d₂ : Dig) → Set
  DayRange d₁ d₂ =   InRange '0' '2' d₁ × InRange '0' '9' d₂
                   ⊎ toℕ d₁ ≡ toℕ '3' × InRange '0' '1' d₂

  HourRange : (h₁ h₂ : Dig) → Set
  HourRange h₁ h₂ =    InRange '0' '1' h₁ × InRange '0' '9' h₂
                     ⊎ toℕ h₁ ≡ toℕ '2' × InRange '0' '3' h₂

  MinuteRange : (mi₁ mi₂ : Dig) → Set
  MinuteRange mi₁ mi₂ = InRange '0' '5' mi₁ × InRange '0' '9' mi₂

  SecRange = MinuteRange

  record MonthDayHourMinSecFields (@0 bs : List Dig) : Set where
    constructor mkMDHMSFields
    field
      @0 {mo₁ mo₂ d₁ d₂ h₁ h₂ mi₁ mi₂ s₁ s₂} : Dig

      mon : Singleton (asciiNum (mo₁ ∷ [ mo₂ ]))
      @0 monRange  : MonthRange mo₁ mo₂

      -- TODO: where do we check valid dom? (Feb, leap year, etc)
      day : Singleton (asciiNum (d₁ ∷ [ d₂ ]))
      @0 dayRange  : DayRange d₁ d₂

      hour : Singleton (asciiNum (h₁ ∷ [ h₂ ]))
      @0 hourRange : HourRange h₁ h₂

      min : Singleton (asciiNum (mi₁ ∷ [ mi₂ ]))
      @0 minRange : MinuteRange mi₁ mi₂

      sec : Singleton (asciiNum (s₁ ∷ [ s₂ ]))
      @0 secRange : SecRange s₁ s₂

      @0 bs≡ : bs ≡ mo₁ ∷ mo₂ ∷ d₁ ∷ d₂ ∷ h₁ ∷ h₂ ∷ mi₁ ∷ mi₂ ∷ s₁ ∷ [ s₂ ]

  record UTCTimeFields (@0 bs : List Dig) : Set where
    constructor mkUTCTimeFields
    field
      @0 {y1 y2 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z} : Dig

      year : Singleton (asciiNum (y1 ∷ [ y2 ]))
      @0 yearRange : All (InRange '0' '9') (y1 ∷ [ y2 ])

      mmddhhmmss : MonthDayHourMinSecFields (mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ [ s2 ])

      @0 term : z ≡ # toℕ 'Z'
      @0 bs≡  : bs ≡ y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ [ z ]

  UTCTime : (@0 _ : List Dig) → Set
  UTCTime xs = TLV Tag.UTCTime UTCTimeFields xs

  record GenTimeFields (@0 bs : List Dig) : Set where
    constructor mkGenTimeFields
    field
      @0 {y1 y2 y3 y4 z} : Dig
      @0 {mdhms} : List Dig

      year : Singleton (asciiNum (y1 ∷ y2 ∷ y3 ∷ [ y4 ]))
      @0 yearRange : All (InRange '0' '9') (y1 ∷ y2 ∷ y3 ∷ [ y4 ])

      mmddhhmmss : MonthDayHourMinSecFields mdhms

      @0 z≡ : z ≡ # 'Z'

      @0 bs≡ : bs ≡ y1 ∷ y2 ∷ y3 ∷ y4 ∷ mdhms ∷ʳ z

  GenTime : (@0 _ : List Dig) → Set
  GenTime = TLV Tag.GeneralizedTime GenTimeFields

  module Time where
    data Time : @0 List Dig → Set where
      utctm : ∀ {@0 bs} → UTCTime bs → Time bs
      gentm  : ∀ {@0 bs} → GenTime  bs → Time bs

    getYear : ∀ {@0 bs} →  Time bs → ℕ
    getYear (utctm x) = 
      let year = Singleton.x (UTCTimeFields.year (TLV.val x)) in
        case year <? 50 of λ where
          (yes _) → 2000 + year
          (no  _) → 1900 + year
    getYear (gentm x) = Singleton.x (GenTimeFields.year (TLV.val x))

    getMonth : ∀ {@0 bs} → Time bs → ℕ
    getMonth (utctm x) = Singleton.x (MonthDayHourMinSecFields.mon (UTCTimeFields.mmddhhmmss (TLV.val x)))
    getMonth (gentm x) = Singleton.x (MonthDayHourMinSecFields.mon (GenTimeFields.mmddhhmmss (TLV.val x)))

    getDay : ∀ {@0 bs} → Time bs → ℕ
    getDay (utctm x) = Singleton.x (MonthDayHourMinSecFields.day (UTCTimeFields.mmddhhmmss (TLV.val x)))
    getDay (gentm x) = Singleton.x (MonthDayHourMinSecFields.day (GenTimeFields.mmddhhmmss (TLV.val x)))

    getHour : ∀ {@0 bs} → Time bs → ℕ
    getHour (utctm x) = Singleton.x (MonthDayHourMinSecFields.hour (UTCTimeFields.mmddhhmmss (TLV.val x)))
    getHour (gentm x) = Singleton.x (MonthDayHourMinSecFields.hour (GenTimeFields.mmddhhmmss (TLV.val x)))

    getMin : ∀ {@0 bs} → Time bs → ℕ
    getMin (utctm x) = Singleton.x (MonthDayHourMinSecFields.min (UTCTimeFields.mmddhhmmss (TLV.val x)))
    getMin (gentm x) = Singleton.x (MonthDayHourMinSecFields.min (GenTimeFields.mmddhhmmss (TLV.val x)))

    getSec : ∀ {@0 bs} → Time bs → ℕ
    getSec (utctm x) = Singleton.x (MonthDayHourMinSecFields.sec (UTCTimeFields.mmddhhmmss (TLV.val x)))
    getSec (gentm x) = Singleton.x (MonthDayHourMinSecFields.sec (GenTimeFields.mmddhhmmss (TLV.val x)))
    

  open Time public using (Time ; utctm ; gentm) hiding (module Time)
------------------------------X.509-----------------------------------------------------------

module X509 where

  record IA5StringValue (@0 bs : List Dig) : Set where
    constructor mkIA5StringValue
    field
      str : OctetStringValue bs
      @0 all<128 : All (Fin._< # 128) (Singleton.x str)

  module SOID where
    -- NOTE: These are proven to be OIDs after the fact (see Aeres.Data.X509.Decidable.OID)
    -- TODO: add other RSA signature algorithms
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

    RsaEncPk : List Dig
    RsaEncPk = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ] 

  -- RSA explicit null param case covered here
  -- TODO : add cases for other RSA signature algorithms
  -- TODO: The current definition fails the "Unambiguous" property
  -- data SignParam : List Dig →  List Dig → Set where
  --   md5rsap    : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Md5Rsa)    → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   sha1rsap   : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha1Rsa)   → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   rsapssp    : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.RsaPss)    → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   sha256rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha256Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   sha384rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha384Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   sha512rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha512Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   sha224rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha224Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   rsaEncPk    : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.RsaEncPk)    → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
  --   _ : ∀ {@0 bs1 bs2} → OctetStringValue bs2 → SignParam bs1 bs2

  record SignAlgFields (@0 bs : List Dig) : Set where
    constructor mkSignAlgFields
    field
      @0 {o p} : List Dig
      signOID : Generic.OID o
      param : Option (NotEmpty OctetStringValue) p
--      wparam : Option (SignParam o) p -- RSA implicit null param case covered here
      @0 bs≡  : bs ≡ o ++ p

  SignAlg : (@0 _ : List Dig) → Set
  SignAlg xs = TLV Tag.Sequence SignAlgFields xs

 --------------- RDNSeq -------------------------------------

  TeletexString : (@0 _ : List Dig) → Set
  TeletexString xs = TLV Tag.TeletexString  OctetStringValue xs

  PrintableString : (@0 _ : List Dig) → Set
  PrintableString xs = TLV Tag.PrintableString  OctetStringValue xs

  UniversalString : (@0 _ : List Dig) → Set
  UniversalString xs = TLV Tag.UniversalString  OctetStringValue xs

  UTF8String : (@0 _ : List Dig) → Set
  UTF8String xs = TLV Tag.UTF8String  OctetStringValue xs

  BMPString : (@0 _ : List Dig) → Set
  BMPString xs = TLV Tag.BMPString  OctetStringValue xs

  IA5String : (@0 _ : List Dig) → Set
  IA5String xs = TLV Tag.IA5String  IA5StringValue xs

  VisibleString : (@0 _ : List Dig) → Set
  VisibleString xs = TLV Tag.VisibleString  OctetStringValue xs

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


  -- AttributeTypeAndValue ::= SEQUENCE {
  --   type     AttributeType,
  --   value    AttributeValue }
  -- AttributeType ::= OBJECT IDENTIFIER
  -- AttributeValue ::= ANY -- DEFINED BY AttributeType
  record RDNATVFields (@0 bs : List Dig) : Set where
    constructor mkRDNATVFields
    field
      @0 {o v} : List Dig
      oid : Generic.OID o
      val : DirectoryString v
      @0 bs≡  : bs ≡ o ++ v

  RDNATV : (@0 _ : List Dig) → Set
  RDNATV xs = TLV Tag.Sequence RDNATVFields xs

 -- RelativeDistinguishedName ::=
 --   SET SIZE (1..MAX) OF AttributeTypeAndValue
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
  RegID xs = TLV Tag.A88 (NonEmptySequenceOf Generic.OIDSub) xs

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
      where open Generic
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
      start : Generic.Time nb
      end : Generic.Time na
      @0 bs≡  : bs ≡ nb ++ na

  module Validity where
    Validity : (@0 _ : List Dig) → Set
    Validity xs = TLV Tag.Sequence ValidityFields xs

    getYearNB : ∀ {@0 bs} → Validity bs →  ℕ
    getYearNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getYear start
    getMonthNB : ∀ {@0 bs} → Validity bs →  ℕ
    getMonthNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getMonth start
    getDayNB : ∀ {@0 bs} → Validity bs →  ℕ
    getDayNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getDay start
    getHourNB : ∀ {@0 bs} → Validity bs →  ℕ
    getHourNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getHour start
    getMinNB : ∀ {@0 bs} → Validity bs →  ℕ
    getMinNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getMin start
    getSecNB : ∀ {@0 bs} → Validity bs →  ℕ
    getSecNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getSec start

    getYearNA : ∀ {@0 bs} → Validity bs →  ℕ
    getYearNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getYear end
    getMonthNA : ∀ {@0 bs} → Validity bs →  ℕ
    getMonthNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getMonth end
    getDayNA : ∀ {@0 bs} → Validity bs →  ℕ
    getDayNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getDay end
    getHourNA : ∀ {@0 bs} → Validity bs →  ℕ
    getHourNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getHour end
    getMinNA : ∀ {@0 bs} → Validity bs →  ℕ
    getMinNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getMin end
    getSecNA : ∀ {@0 bs} → Validity bs →  ℕ
    getSecNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Generic.Time.getSec end
    
  open Validity public using (Validity)

  record PublicKeyFields (@0 bs : List Dig) : Set where
    constructor mkPublicKeyFields
    field
      @0 {alg pk} : List Dig
      signalg : SignAlg alg
      pubkey : BitString pk
      @0 bs≡  : bs ≡ alg ++ pk

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
  EKUFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf Generic.OID) xs

  EKUFields : (@0 _ : List Dig) → Set
  EKUFields xs = TLV Tag.OctetString  EKUFieldsSeq xs

-------------------------------------------------------------------------------

  record BCFieldsSeqFields (@0 bs : List Dig) : Set where
    constructor mkBCFieldsSeqFields
    field
      @0 {ca pl} : List Dig
      bcca : Option Generic.Boool ca
      bcpathlen : Option Int pl
      @0 bs≡  : bs ≡ ca ++ pl

  BCFieldsSeq : (@0 _ : List Dig) → Set
  BCFieldsSeq xs = TLV Tag.Sequence  BCFieldsSeqFields xs

  BCFields : (@0 _ : List Dig) → Set
  BCFields xs = TLV Tag.OctetString  BCFieldsSeq xs

-------------------------- ian/san alternative names extensions ------------------
  IANFieldsSeq : (@0 _ : List Dig) → Set
  IANFieldsSeq = GeneralNames -- TLV Tag.Sequence GeneralNamesElems

  IANFields : (@0 _ : List Dig) → Set
  IANFields xs = TLV Tag.OctetString IANFieldsSeq xs

  SANFieldsSeq : (@0 _ : List Dig) → Set
  SANFieldsSeq = GeneralNames -- TLV Tag.Sequence GeneralNamesElems

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
      cpid : Generic.OID pid
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

  -- DistributionPointName ::= CHOICE {
  --      fullName                [0]     GeneralNames,
  --      nameRelativeToCRLIssuer [1]     RelativeDistinguishedName }
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

    AIA : List Dig
    AIA =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 1 ∷ [ # 1 ]

    Supported : List (List Dig)
    Supported = AKI ∷ SKI ∷ KU ∷ EKU ∷ BC ∷ IAN ∷ SAN ∷ CPOL ∷ CRLDIST ∷ [ AIA ]

  record ExtensionFields (@0 P : List Dig → Set) (A : @0 List Dig → Set) (@0 bs : List Dig) : Set where
    constructor mkExtensionFields
    field
      @0 {oex cex ocex} : List Dig
      extnId : Generic.OID oex
      @0 extnId≡ : P oex -- oex ≡ lit
      crit : Option Generic.Boool cex
      extension : A ocex
      @0 bs≡ : bs ≡ oex ++ cex ++ ocex

  data SelectExtn : @0 List Dig → Set where
    akiextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.AKI    )              AKIFields           bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.AKI) → AKIFields bs2 → SelectExtn bs1 bs2
    skiextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.SKI    )              SKIFields           bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.SKI) → SKIFields bs2 → SelectExtn bs1 bs2
    kuextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.KU     )              KUFields            bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.KU) → KUFields bs2 → SelectExtn bs1 bs2
    ekuextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.EKU    )              EKUFields           bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.EKU) → EKUFields bs2 → SelectExtn bs1 bs2
    bcextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.BC     )              BCFields            bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.BC) → BCFields bs2 → SelectExtn bs1 bs2
    ianextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.IAN    )              IANFields           bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.IAN) → IANFields bs2 → SelectExtn bs1 bs2
    sanextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.SAN    )              SANFields           bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.SAN) → SANFields bs2 → SelectExtn bs1 bs2
    cpextn  : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.CPOL   )              CertPolFields       bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.CPOL) → CertPolFields bs2 → SelectExtn bs1 bs2
    crlextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.CRLDIST)              CRLDistFields       bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.CRLDIST) → CRLDistFields bs2 → SelectExtn bs1 bs2
    aiaextn : ∀ {@0 bs} → ExtensionFields (_≡ ExtensionOID.AIA    )              AIAFields           bs → SelectExtn bs -- ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.AIA) → AIAFields bs2 → SelectExtn bs1 bs2
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
    Chain = NonEmptySequenceOf Cert
  open Chain public using (Chain)

    
  
