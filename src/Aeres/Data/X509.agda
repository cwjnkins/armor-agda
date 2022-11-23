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

open import Aeres.Data.X690-DER             public
open import Aeres.Data.X509.DirectoryString public
open import Aeres.Data.X509.DisplayText     public
open import Aeres.Data.X509.Extension.AKI   public
open import Aeres.Data.X509.Extension.BC    public
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation
  public
open import Aeres.Data.X509.Extension.EKU   public
open import Aeres.Data.X509.Extension.IAN   public
open import Aeres.Data.X509.Extension.KU    public
open import Aeres.Data.X509.Extension.SAN   public
open import Aeres.Data.X509.Extension.SKI   public
open import Aeres.Data.X509.GeneralName     public
open import Aeres.Data.X509.IA5String       public
open import Aeres.Data.X509.PublicKey       public
open import Aeres.Data.X509.RDN             public
open import Aeres.Data.X509.SignAlg         public
open import Aeres.Data.X509.Strings         public
open import Aeres.Data.X509.TBSCert         public
open import Aeres.Data.X509.Validity        public

------------------------------X.509-----------------------------------------------------------

module X509 where

  -- module SOID where
  --   -- NOTE: These are proven to be OIDs after the fact (see Aeres.Data.X509.Decidable.OID)
  --   Md5Rsa : List UInt8
  --   Md5Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 4 ]

  --   Sha1Rsa : List UInt8
  --   Sha1Rsa =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 5 ]

  --   RsaPss : List UInt8
  --   RsaPss =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 10 ]

  --   Sha256Rsa : List UInt8
  --   Sha256Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 11 ]

  --   Sha384Rsa : List UInt8
  --   Sha384Rsa =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 12 ]

  --   Sha512Rsa : List UInt8
  --   Sha512Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 13 ]

  --   Sha224Rsa : List UInt8
  --   Sha224Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 14 ]

  ExpNull : List UInt8
  ExpNull = # 5 ∷ [ # 0 ]

-----------------------------------------Extensions------------------------------------------

------------------------- certificate policies -------------------------

  CertPolFieldsSeq : (@0 _ : List UInt8) → Set
  CertPolFieldsSeq = TLV Tag.Sequence (NonEmptySequenceOf PolicyInformation)

  CertPolFields : (@0 _ : List UInt8) → Set
  CertPolFields xs = TLV Tag.OctetString  CertPolFieldsSeq xs

----------------------------- crl dist point extension --------------------------------

  CrlIssuer : (@0 _ : List UInt8) → Set
  CrlIssuer xs = TLV Tag.AA2 GeneralNamesElems xs

  ReasonFlags : (@0 _ : List UInt8) → Set
  ReasonFlags xs = TLV Tag.A81 BitStringValue xs

  FullName : (@0 _ : List UInt8) → Set
  FullName xs = TLV Tag.AA0 GeneralNamesElems xs

  NameRTCrlIssuer : (@0 _ : List UInt8) → Set
  NameRTCrlIssuer xs = TLV Tag.AA1 RDNElems xs

  data DistPointNameChoice : (@0 _ : List UInt8) → Set where
    fullname : ∀ {@0 bs} → FullName bs → DistPointNameChoice bs
    nameRTCrlissr : ∀ {@0 bs} → NameRTCrlIssuer bs → DistPointNameChoice bs

  DistPointName : (@0 _ : List UInt8) → Set
  DistPointName xs = TLV Tag.AA0  DistPointNameChoice xs

  record DistPointFields (@0 bs : List UInt8) : Set where
    constructor mkDistPointFields
    field
      @0 {dp rsn issr} : List UInt8
      crldp : Option DistPointName dp
      crldprsn : Option ReasonFlags rsn
      crlissr : Option CrlIssuer issr
      @0 bs≡  : bs ≡ dp ++ rsn ++ issr

  DistPoint : (@0 _ : List UInt8) → Set
  DistPoint xs = TLV Tag.Sequence DistPointFields xs

  CRLDistFieldsSeq : (@0 _ : List UInt8) → Set
  CRLDistFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf DistPoint) xs

  CRLDistFields : (@0 _ : List UInt8) → Set
  CRLDistFields xs = TLV Tag.OctetString  CRLDistFieldsSeq xs

----------------------------------------- Authority Info access -----------------
  module ACMOID where
    CAISSUERS : List UInt8
    CAISSUERS = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 2 ]

    OCSP : List UInt8
    OCSP = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 1 ]

  data AccessMethod : @0 List UInt8 → Set where
    caissid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.CAISSUERS) → AccessMethod bs
    ocspid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.OCSP) → AccessMethod bs

  record AccessDescFields (@0 bs : List UInt8) : Set where
    constructor mkAccessDescFields
    field
      @0 {acm acl} : List UInt8
      acmethod : AccessMethod acm
      aclocation : GeneralName acl
      @0 bs≡  : bs ≡ acm ++ acl

  AccessDesc : (@0 _ : List UInt8) → Set
  AccessDesc xs = TLV Tag.Sequence  AccessDescFields xs

  AIAFieldsSeq : (@0 _ : List UInt8) → Set
  AIAFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf AccessDesc) xs

  AIAFields : (@0 _ : List UInt8) → Set
  AIAFields xs = TLV Tag.OctetString  AIAFieldsSeq xs

------------------------------------ Name Constraints ---------------------------

  MinBaseDistance : (@0 _ : List UInt8) → Set
  MinBaseDistance xs = TLV Tag.A80 IntegerValue xs

  MaxBaseDistance : (@0 _ : List UInt8) → Set
  MaxBaseDistance xs = TLV Tag.A81 IntegerValue xs

  record GeneralSubtreeFields (@0 bs : List UInt8) : Set where
    constructor mkGeneralSubtreeFields
    field
      @0 {bse minb maxb} : List UInt8
      base : GeneralName bse
      minimum : Option MinBaseDistance minb
      maximum : Option MaxBaseDistance maxb
      @0 bs≡  : bs ≡ bse ++ minb ++ maxb

  GeneralSubtree : (@0 _ : List UInt8) → Set
  GeneralSubtree xs = TLV Tag.Sequence GeneralSubtreeFields xs

  GeneralSubtrees : (@0 _ : List UInt8) → Set
  GeneralSubtrees xs = TLV Tag.Sequence (NonEmptySequenceOf GeneralSubtree) xs

  PermittedSubtrees : (@0 _ : List UInt8) → Set
  PermittedSubtrees xs = TLV Tag.AA0 GeneralSubtrees xs

  ExcludedSubtrees : (@0 _ : List UInt8) → Set
  ExcludedSubtrees xs = TLV Tag.AA1 GeneralSubtrees xs

  record NCFieldsSeqFields (@0 bs : List UInt8) : Set where
    constructor mkNCFieldsSeqFields
    field
      @0 {pe ex} : List UInt8
      permt : Option PermittedSubtrees pe
      excld : Option ExcludedSubtrees ex
      @0 bs≡  : bs ≡ pe ++ ex

  NCFieldsSeq : (@0 _ : List UInt8) → Set
  NCFieldsSeq xs = TLV Tag.Sequence NCFieldsSeqFields xs

  NCFields : (@0 _ : List UInt8) → Set
  NCFields xs = TLV Tag.OctetString  NCFieldsSeq xs

------------------------------------ Policy Constraints ---------------------------

  RequireExplicitPolicy : (@0 _ : List UInt8) → Set
  RequireExplicitPolicy xs = TLV Tag.A80 IntegerValue xs

  InhibitPolicyMapping : (@0 _ : List UInt8) → Set
  InhibitPolicyMapping xs = TLV Tag.A81 IntegerValue xs

  record PCFieldsSeqFields (@0 bs : List UInt8) : Set where
    constructor mkPCFieldsSeqFields
    field
      @0 {req ini} : List UInt8
      require : Option RequireExplicitPolicy req
      ihibit : Option InhibitPolicyMapping ini
      @0 bs≡  : bs ≡ req ++ ini

  PCFieldsSeq : (@0 _ : List UInt8) → Set
  PCFieldsSeq xs = TLV Tag.Sequence PCFieldsSeqFields xs

  PCFields : (@0 _ : List UInt8) → Set
  PCFields xs = TLV Tag.OctetString  PCFieldsSeq xs

------------------------------------ Policy Mappings ---------------------------

  record PolicyMapFields (@0 bs : List UInt8) : Set where
    constructor mkPolicyMapFields
    field
      @0 {iss sub} : List UInt8
      issuerDomainPolicy : OID iss
      subjectDomainPolicy : OID sub
      @0 bs≡  : bs ≡ iss ++ sub

  PolicyMap : (@0 _ : List UInt8) → Set
  PolicyMap xs = TLV Tag.Sequence PolicyMapFields xs

  PMFieldsSeq : (@0 _ : List UInt8) → Set
  PMFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf PolicyMap) xs

  PMFields : (@0 _ : List UInt8) → Set
  PMFields xs = TLV Tag.OctetString  PMFieldsSeq xs

------------------------------------ Inhibit anyPolicy ---------------------------

  INAPFields : (@0 _ : List UInt8) → Set
  INAPFields xs = TLV Tag.OctetString Int xs

--------------------------------Extensions selection----------------------------------------

  module ExtensionOID where
    AKI : List UInt8
    AKI = # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 35 ]

    SKI : List UInt8
    SKI =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 14 ]

    KU : List UInt8
    KU =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 15 ]

    EKU : List UInt8
    EKU =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 37 ]

    BC : List UInt8
    BC =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 19 ]

    IAN : List UInt8
    IAN =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 18 ]

    SAN : List UInt8
    SAN =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 17 ]

    CPOL : List UInt8
    CPOL =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 32 ]

    CRLDIST : List UInt8
    CRLDIST =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 31 ]

    NC : List UInt8
    NC =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 30 ]

    PC : List UInt8
    PC =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 36 ]

    PM : List UInt8
    PM =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 33 ]

    INAP : List UInt8
    INAP =  # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ [ # 54 ]

    AIA : List UInt8
    AIA =  # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 1 ∷ [ # 1 ]

    Supported : List (List UInt8)
    Supported = AKI ∷ SKI ∷ KU ∷ EKU ∷ BC ∷ IAN ∷ SAN ∷ CPOL ∷ CRLDIST ∷ NC ∷ PC ∷ PM ∷ INAP ∷ [ AIA ] 

  record ExtensionFields (@0 P : List UInt8 → Set) (A : @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
    constructor mkExtensionFields
    field
      @0 {oex cex ocex} : List UInt8
      extnId : OID oex
      @0 extnId≡ : P oex -- oex ≡ lit
      crit : Option Boool cex
      extension : A ocex
      @0 bs≡ : bs ≡ oex ++ cex ++ ocex

  data SelectExtn : @0 List UInt8 → Set where
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
    Extension : (@0 _ : List UInt8) → Set
    Extension xs = TLV Tag.Sequence SelectExtn xs

    getBC : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC (mkTLV len (bcextn x) len≡ bs≡) = _ , (some x)
    getBC (mkTLV len _ len≡ bs≡) = _ , none

    getKU : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU (mkTLV len (kuextn x) len≡ bs≡) = _ , (some x)
    getKU (mkTLV len _ len≡ bs≡) = _ , none

    getSAN : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN (mkTLV len (sanextn x) len≡ bs≡) = _ , (some x)
    getSAN (mkTLV len _ len≡ bs≡) = _ , none

    getCRLDIST : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST (mkTLV len (crlextn x) len≡ bs≡) = _ , (some x)
    getCRLDIST (mkTLV len _ len≡ bs≡) = _ , none

    getCPOL : ∀ {@0 bs} → Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL (mkTLV len (cpextn x) len≡ bs≡) = _ , (some x)
    getCPOL (mkTLV len _ len≡ bs≡) = _ , none
  open Extension public using (Extension)

  module ExtensionsSeq where
    ExtensionsSeq : (@0 _ : List UInt8) → Set
    ExtensionsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf Extension) xs

    getBC : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getBC h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getKU : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getKU h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getSAN : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getSAN h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getCRLDIST : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getCRLDIST h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getCPOL : ∀ {@0 bs} → ExtensionsSeq bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL (mkTLV len (mk×ₚ x sndₚ₁ bs≡₁) len≡ bs≡) = helper x
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
      helper nil = _ , none
      helper (consIList h t bs≡) = case (Extension.getCPOL h) of λ where
        (─ .[] , none) → helper t
        y@(fst , some x) → y

    getExtensionsList : ∀ {@0 bs} → ExtensionsSeq bs → List (Exists─ (List UInt8) Extension)
    getExtensionsList (mkTLV len (mk×ₚ fstₚ₁ sndₚ₁ bs≡₁) len≡ bs≡) = helper fstₚ₁
      where
      helper : ∀ {@0 bs} → SequenceOf Extension bs → List (Exists─ (List UInt8) Extension)
      helper nil = []
      helper (consIList h t bs≡) = (_ , h) ∷ helper t
  open ExtensionsSeq public using (ExtensionsSeq)

  module Extensions where
    Extensions : (@0 _ : List UInt8) → Set
    Extensions xs = TLV Tag.AA3  ExtensionsSeq xs

    getBC : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC (mkTLV len val len≡ bs≡) = ExtensionsSeq.getBC val

    getKU : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU (mkTLV len val len≡ bs≡) = ExtensionsSeq.getKU val

    getSAN : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN (mkTLV len val len≡ bs≡) = ExtensionsSeq.getSAN val

    getCRLDIST : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCRLDIST val

    getCPOL : ∀ {@0 bs} → Extensions bs → Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL (mkTLV len val len≡ bs≡) = ExtensionsSeq.getCPOL val

    getExtensionsList : ∀ {@0 bs} → Extensions bs → List (Exists─ (List UInt8) Extension)
    getExtensionsList (mkTLV len val len≡ bs≡) = ExtensionsSeq.getExtensionsList val
  open Extensions public using (Extensions)

-----------------------------------------------------------------------------------------------

  record TBSCertFields (@0 bs : List UInt8) : Set where
    constructor mkTBSCertFields
    field
      @0 {ver ser sa i va u p u₁ u₂ e} : List UInt8
      version : Option Version ver
      serial  : Int ser
      signAlg : SignAlg sa
      issuer  : RDNSeq i
      validity : Validity va
      subject  : RDNSeq u
      pk       : PublicKey p
      pkBytes  : Singleton p -- TODO: eventually this should come from serialization
      issuerUID : Option IssUID u₁ -- if this takes a lot of time, this and the lower can be dropped
      subjectUID : Option SubUID u₂
      extensions : Option Extensions e
      @0 bs≡  : bs ≡ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

    getVersion : ℤ
    getVersion = elimOption{X = const ℤ} (ℤ.+ 0) (λ v → Version.getVal v) version

    getSerial : ℤ
    getSerial = Int.getVal serial

    getValidityStartTime getValidityEndTime : Exists─ (List UInt8) Time

    getValidityStartTime = Validity.getStartTime validity
    getValidityEndTime   = Validity.getEndTime validity

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

    -- getPublicKeyOIDbs : List UInt8
    -- getPublicKeyOIDbs = PublicKey.getPkAlgOIDbs pk

    getIssuerLen : ℕ
    getIssuerLen = RDN.getSeqLen issuer

    getSubjectLen :  ℕ
    getSubjectLen = RDN.getSeqLen subject

    getIssuer : Exists─ (List UInt8) RDNSeq
    getIssuer = _ , issuer

    getSubject : Exists─ (List UInt8) RDNSeq
    getSubject = _ , subject

    getSignAlg : Exists─ (List UInt8) SignAlg
    getSignAlg = _ , signAlg

    getBC : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC = elimOption (_ , none) (λ v → Extensions.getBC v) extensions

    getKU : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU = elimOption (_ , none) (λ v → Extensions.getKU v) extensions

    getSAN : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN = elimOption (_ , none) (λ v → Extensions.getSAN v) extensions

    getCRLDIST : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST = elimOption (_ , none) (λ v → Extensions.getCRLDIST v) extensions

    getCPOL : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL = elimOption (_ , none) (λ v → Extensions.getCPOL v) extensions

    getExtensionsList : List (Exists─ (List UInt8) Extension)
    getExtensionsList = elimOption [] (λ v → Extensions.getExtensionsList v) extensions
 
  TBSCert : (@0 _ : List UInt8) → Set
  TBSCert xs = TLV Tag.Sequence TBSCertFields xs

  ---------------------------------Certificate---------------------------------------------------

  record CertFields (@0 bs : List UInt8) : Set where
    constructor mkCertFields
    field
      @0 {t sa sig} : List UInt8
      tbs : TBSCert t
      tbsBytes : Singleton t    -- TODO: eventually this should come from serialization
      signAlg : SignAlg sa
      signature : BitString sig
      signatureBytes : Singleton sig
      @0 bs≡  : bs ≡ t ++ sa ++ sig

    getVersion : ℤ
    getVersion = TBSCertFields.getVersion (TLV.val tbs)

    getSerial : ℤ
    getSerial = TBSCertFields.getSerial (TLV.val tbs)

    getValidityStartTime getValidityEndTime : Exists─ (List UInt8) Time

    getValidityStartTime = TBSCertFields.getValidityStartTime ∘ TLV.val $ tbs
    getValidityEndTime   = TBSCertFields.getValidityEndTime  ∘ TLV.val $ tbs 

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

    getIssuer :  Exists─ (List UInt8) RDNSeq
    getIssuer = TBSCertFields.getIssuer (TLV.val tbs)

    getSubject :  Exists─ (List UInt8) RDNSeq
    getSubject = TBSCertFields.getSubject (TLV.val tbs)

    getIssUID : Exists─ (List UInt8) (Option IssUID)
    getIssUID = _ , (TBSCertFields.issuerUID (TLV.val tbs))

    getSubUID : Exists─ (List UInt8) (Option SubUID)
    getSubUID = _ , (TBSCertFields.subjectUID (TLV.val tbs))

    getTBSCertSignAlg : Exists─ (List UInt8) SignAlg
    getTBSCertSignAlg = TBSCertFields.getSignAlg (TLV.val tbs)
 
    getCertSignAlg : Exists─ (List UInt8) SignAlg
    getCertSignAlg =  _ , signAlg

    getBC : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
    getBC = TBSCertFields.getBC (TLV.val tbs)

    getKU : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
    getKU = TBSCertFields.getKU (TLV.val tbs)

    getSAN : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
    getSAN = TBSCertFields.getSAN (TLV.val tbs)

    getCRLDIST : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
    getCRLDIST = TBSCertFields.getCRLDIST (TLV.val tbs)

    getCPOL : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
    getCPOL = TBSCertFields.getCPOL (TLV.val tbs)

    getExtensions : Exists─ (List UInt8) (Option Extensions)
    getExtensions = _ , (TBSCertFields.extensions (TLV.val tbs))
    
    getExtensionsList : List (Exists─ (List UInt8) Extension)
    getExtensionsList = TBSCertFields.getExtensionsList (TLV.val tbs)

    getPublicKeyBytes : List UInt8
    getPublicKeyBytes = ↑ (TBSCertFields.pkBytes (TLV.val tbs))

  module Cert where
    Cert : (@0 _ : List UInt8) → Set
    Cert xs = TLV Tag.Sequence  CertFields xs

    module _ {@0 bs} (c : Cert bs) where
      getVersion : ℤ
      getVersion = CertFields.getVersion (TLV.val c)

      getSerial : ℤ
      getSerial = CertFields.getSerial (TLV.val c)

      getTBSBytes : List UInt8
      getTBSBytes = ↑ (CertFields.tbsBytes (TLV.val c))

      getValidityStartTime getValidityEndTime : Exists─ (List UInt8) Time

      getValidityStartTime = CertFields.getValidityStartTime ∘ TLV.val $ c
      getValidityEndTime   = CertFields.getValidityEndTime   ∘ TLV.val $ c

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

      getIssuer :  Exists─ (List UInt8) RDNSeq
      getIssuer = CertFields.getIssuer (TLV.val c)

      getSubject :  Exists─ (List UInt8) RDNSeq
      getSubject = CertFields.getSubject (TLV.val c)

      getIssUID : Exists─ (List UInt8) (Option IssUID)
      getIssUID = CertFields.getIssUID (TLV.val c)

      getSubUID : Exists─ (List UInt8) (Option SubUID)
      getSubUID = CertFields.getSubUID (TLV.val c)

      getTBSCertSignAlg : Exists─ (List UInt8) SignAlg
      getTBSCertSignAlg = CertFields.getTBSCertSignAlg (TLV.val c)

      getCertSignAlg : Exists─ (List UInt8) SignAlg
      getCertSignAlg = CertFields.getCertSignAlg (TLV.val c)

      -- getPublicKeyOIDbs : List UInt8
      -- getPublicKeyOIDbs = TBSCertFields.getPublicKeyOIDbs (TLV.val (CertFields.tbs (TLV.val c)))

      getBC : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.BC) BCFields))
      getBC = CertFields.getBC (TLV.val c)

      getKU : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.KU) KUFields))
      getKU = CertFields.getKU (TLV.val c)

      getSAN : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.SAN) SANFields))
      getSAN = CertFields.getSAN (TLV.val c)

      getCRLDIST : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CRLDIST) CRLDistFields))
      getCRLDIST = CertFields.getCRLDIST (TLV.val c)

      getCPOL : Exists─ (List UInt8) (Option (ExtensionFields (_≡ ExtensionOID.CPOL) CertPolFields))
      getCPOL = CertFields.getCPOL (TLV.val c)

      getExtensions : Exists─ (List UInt8) (Option Extensions)
      getExtensions = CertFields.getExtensions (TLV.val c)
 
      getExtensionsList : List (Exists─ (List UInt8) Extension)
      getExtensionsList = CertFields.getExtensionsList (TLV.val c)

      getPublicKeyBytes : List UInt8
      getPublicKeyBytes = CertFields.getPublicKeyBytes (TLV.val c)

      getSignatureBytes : List UInt8
      getSignatureBytes = ↑ CertFields.signatureBytes (TLV.val c)

      getSignatureValueBytes : List UInt8
      getSignatureValueBytes = ↑ (BitString.serializeValue (TLV.val (CertFields.signature (TLV.val c))))

  open Cert public using (Cert)

  module Chain where
    Chain : (@0 _ : List UInt8) → Set
    Chain = IListNonEmpty Cert
  open Chain public using (Chain)
