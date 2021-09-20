open import Aeres.Prelude

module Aeres.Data.X509 where
open import Aeres.Binary
open Base256

-------------------------------------------TAGS---------------------------------------------
module Tag where
  abstract

    Boolean : Dig
    Boolean = # 1
    
    Integer : Dig
    Integer = # 2

    Bitstring : Dig
    Bitstring = # 3

    Octetstring : Dig
    Octetstring = # 4

    Null : Dig
    Null = # 5

    ObjectIdentifier : Dig
    ObjectIdentifier = # 6

    Utctime : Dig
    Utctime = # 23

    Gentime : Dig
    Gentime = # 24

    Sequence : Dig
    Sequence = # 48
    
    Sett : Dig
    Sett = # 49

    Version : Dig
    Version = # 160

    IssUid : Dig
    IssUid = # 161

    SubUid : Dig
    SubUid = # 162

    Extensions : Dig
    Extensions = # 163

    Eighty : Dig
    Eighty = # 128

    EightyOne : Dig
    EightyOne = # 129

    EightyTwo : Dig
    EightyTwo = # 130

    A0 : Dig
    A0 = # 160

    A1 : Dig
    A1 = # 161

    A2 : Dig
    A2 = # 162
    
-----------------------------------------Length------------------------------------------
module Length where

  record Short (bs : List Dig) : Set where
    constructor mkShort
    field
      l : Dig
      @0 l<128 : toℕ l < 128
      @0 bs≡ : bs ≡ [ l ]
  open Short

  record Long (bs : List Dig) : Set where
    constructor mkLong
    field
      l : Dig
      @0 l>128 : 128 < toℕ l
      lₕ : Dig
      @0 lₕ≢0 : toℕ lₕ ≢ 0
      lₜ : List Dig
      @0 lₜLen : length lₜ ≡ toℕ l - 129
      @0 lₕₜMinRep : lₜ ≢ [] ⊎ toℕ lₕ ≥ 128
      @0 bs≡ : bs ≡ l ∷ lₕ ∷ lₜ
  open Long

  data Length : List Dig → Set where
    short : ∀ {@0 bs} → Short bs → Length bs
    long  : ∀ {@0 bs} → Long  bs → Length bs

  shortₛ : ∀ l → {@0 _ : True (toℕ l <? 128)} → Length [ l ]
  shortₛ l {l<128} = short (mkShort l (toWitness l<128) refl)

  longₛ : ∀ l lₕ lₜ →
          {@0 _ : True (128 <? toℕ l)}
          {@0 _ : False (toℕ lₕ ≟ 0)}
          {@0 _ : True (length lₜ ≟ (toℕ l - 129))}
          {@0 _ : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128)}
          → Length (l ∷ lₕ ∷ lₜ)
  longₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr} =
   long (mkLong l
          (toWitness l>128) lₕ
          (toWitnessFalse lₕ≢0) lₜ
          (toWitness lₜLen) (toWitness mr) refl)

  getLength : ∀ {@0 bs} → Length bs → ℕ
  getLength {bs} (short (mkShort l l<128 bs≡)) = toℕ l
  getLength {bs} (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen _ bs≡)) = go (reverse (lₕ ∷ lₜ))
    where
    go : List Dig → ℕ
    go [] = 0
    go (b ∷ bs') = toℕ b + 256 * go bs'

open Length public
  using  (Length ; getLength)
  hiding (module Length)

-------------------------------------------Generic---------------------------------------
module Generic where

  postulate
    StringValue : List Dig → Set
    IntegerValue : List Dig → Set
    OctetValue : List Dig → Set

  record OIDSub (bs : List Dig) : Set where
    constructor mkOIDSub
    field
      lₚ : List Dig
      @0 lₚ≥128 : All (λ d → toℕ d ≥ 128) lₚ
      lₑ   : Dig
      @0 lₑ<128 : toℕ lₑ < 128
      @0 leastDigs : maybe (λ d → toℕ d > 128) ⊤ (head lₚ)
      @0 bs≡ : bs ≡ lₚ ∷ʳ lₑ

  --private
  --  oidsub₁ : OIDSub (# 134 ∷ [ # 72 ])
  --  oidsub₁ = mkOIDSub [ # 134 ] (toWitness{Q = All.all ((128 ≤?_) ∘ toℕ) _} tt) (# 72) (toWitness{Q = 72 <? 128} tt) (toWitness{Q = 134 >? 128} tt) refl

  data OIDField : List Dig → Set

  record OIDFieldₐ (@0 bs : List Dig) : Set where
    inductive
    constructor mkOIDFieldₐ
    field
      @0 {bs₁} : List Dig
      @0 {bs₂} : List Dig
      sub  : OIDSub bs₁
      rest : OIDField bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data OIDField where
    [_]OID : ∀ {@0 bs} → OIDSub bs → OIDField bs
    cons : ∀ {@0 bs} → OIDFieldₐ bs → OIDField bs

  record OID (@0 bs : List Dig) : Set where
    constructor mkOid
    field
      @0 {l} : List Dig
      @0 {o} : List Dig
      len : Length l
      oid : OIDField o
      @0 len≡ : getLength len ≡ length o
      @0 bs≡ : bs ≡ Tag.ObjectIdentifier ∷ l ++ o

  record Int (bs : List Dig) : Set where
    constructor mkInt
    field
      @0 {l v} : List Dig
      len : Length l
      val : IntegerValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.Integer ∷ l ++ v

  record Boool (bs : List Dig) : Set where
    constructor mkBoool
    field
      @0 {l} : List Dig
      len : Length l
      v : Dig
      @0 len≡ : getLength len ≡ 1
      @0 bs≡ : bs ≡  Tag.Boolean ∷ l ++ (v ∷ [])

  data Option (A : List Dig → Set) : List Dig → Set where
    none : Option A []
    some : forall {xs} → A xs → Option A xs

------------------------------X.509-----------------------------------------------------------
module X509 where

  postulate
    SignParam : List Dig → Set
    PublicKey : List Dig → Set

  record SignAlg (bs : List Dig) : Set where
    constructor mkSignAlg
    field
      @0 {l o p} : List Dig
      len : Length l
      signOID : Generic.OID o
      param   : SignParam p
      @0 len≡ : getLength len ≡ length (o ++ p)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ o ++ p

  --------------------------TBSCert-----------------------------------------------------------------
  record Version (bs : List Dig) : Set where
    constructor mkVersion
    field
      @0 {l v} : List Dig
      len : Length l
      ver : Generic.Int v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.Version ∷ l ++ v

  record RDNSetSeq (bs : List Dig) : Set where
    constructor mkRDNSetSeq
    field
      @0 {l o v} : List Dig
      len : Length l
      oid : Generic.OID o
      val : Generic.StringValue v
      @0 len≡ : getLength len ≡ length (o ++ v)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ v


  data RDNSetElems : List Dig → Set

  record RDNSetElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkRDNSetElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      rdnss : RDNSetSeq bs₁
      rest  : RDNSetElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data RDNSetElems where
    _∷[] : ∀ {x} → RDNSetSeq x → RDNSetElems x
    cons : ∀ {x} → RDNSetElemsₐ x → RDNSetElems x

  record RDNSet (bs : List Dig) : Set where
    constructor mkRDNSet
    field
      @0 {l e} : List Dig
      len : Length l
      rdnSetElems : RDNSetElems e
      @0 len≡ : getLength len ≡ length e
      @0 bs≡  : bs ≡ Tag.Sett ∷ l ++ e

  data RDNSeqElems : List Dig → Set

  record RDNSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkRDNSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      rdnSet : RDNSet bs₁
      rest   : RDNSeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data RDNSeqElems where
    _∷[]  : ∀ {x} → RDNSet x → RDNSeqElems x
    cons : ∀ {x} → RDNSeqElemsₐ x → RDNSeqElems x

  record RDName (bs : List Dig) : Set where
    constructor mkRDName
    field
      @0 {l e} : List Dig
      len : Length l
      elems : RDNSeqElems e
      @0 len≡ : getLength len ≡ length e
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ e

  record IssUID (bs : List Dig) : Set where
    constructor mkIssUid
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.IssUid ∷ l ++ v

  record SubUID (bs : List Dig) : Set where
    constructor mkSubUid
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.SubUid ∷ l ++ v

  record UtcTime (bs : List Dig) : Set where
    constructor mkUtcTime
    field
      @0 {l} : List Dig
      @0 {y1 y2 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z} : Dig
      len : Length l
      @0 year : (0 ≤ ((toℕ y1 - 48) * 10 + (toℕ y2 - 48))) × (((toℕ y1 - 48) * 10 + (toℕ y2 - 48)) ≤ 99)
      @0 mon : (1 ≤ ((toℕ mn1 - 48) * 10 + (toℕ mn2 - 48))) × (((toℕ mn1 - 48) * 10 + (toℕ mn2 - 48)) ≤ 12)
      @0 day : (1 ≤ ((toℕ d1 - 48) * 10 + (toℕ d2 - 48))) × (((toℕ d1 - 48) * 10 + (toℕ d2 - 48)) ≤ 31)
      @0 hour : (0 ≤ ((toℕ h1 - 48) * 10 + (toℕ h2 - 48))) × (((toℕ h1 - 48) * 10 + (toℕ h2 - 48)) ≤ 23)
      @0 min : (0 ≤ ((toℕ mi1 - 48) * 10 + (toℕ mi2 - 48))) × (((toℕ mi1 - 48) * 10 + (toℕ mi2 - 48)) ≤ 59)
      @0 sec : (0 ≤ ((toℕ s1 - 48) * 10 + (toℕ s2 - 48))) × (((toℕ s1 - 48) * 10 + (toℕ s2 - 48)) ≤ 59)
      @0 last_byte : toℕ z ≡ 90
      @0 len≡ : getLength len ≡ length (y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ z ∷ [])
      @0 bs≡  : bs ≡ Tag.Utctime ∷ l ++ (y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ z ∷ [])

  record GenTime (bs : List Dig) : Set where
    constructor mkGenTime
    field
      @0 {l} : List Dig
      @0 {y1 y2 y3 y4 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z} : Dig
      len : Length l
      @0 year : (1 ≤ ((toℕ y1 - 48) * 1000 + (toℕ y2 - 48) * 100 + (toℕ y3 - 48) * 10 + (toℕ y4 - 48))) ×
        (((toℕ y1 - 48) * 1000 + (toℕ y2 - 48) * 100 + (toℕ y3 - 48) * 10 + (toℕ y4 - 48)) ≤ 9999)
      @0 mon : (1 ≤ ((toℕ mn1 - 48) * 10 + (toℕ mn2 - 48))) × (((toℕ mn1 - 48) * 10 + (toℕ mn2 - 48)) ≤ 12)
      @0 day : (1 ≤ ((toℕ d1 - 48) * 10 + (toℕ d2 - 48))) × (((toℕ d1 - 48) * 10 + (toℕ d2 - 48)) ≤ 31)
      @0 hour : (0 ≤ ((toℕ h1 - 48) * 10 + (toℕ h2 - 48))) × (((toℕ h1 - 48) * 10 + (toℕ h2 - 48)) ≤ 23)
      @0 min : (0 ≤ ((toℕ mi1 - 48) * 10 + (toℕ mi2 - 48))) × (((toℕ mi1 - 48) * 10 + (toℕ mi2 - 48)) ≤ 59)
      @0 sec : (0 ≤ ((toℕ s1 - 48) * 10 + (toℕ s2 - 48))) × (((toℕ s1 - 48) * 10 + (toℕ s2 - 48)) ≤ 59)
      @0 last_byte : toℕ z ≡ 90
      @0 len≡ : getLength len ≡ length (y1 ∷ y2 ∷ y3 ∷ y4 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ z ∷ [])
      @0 bs≡  : bs ≡ Tag.Utctime ∷ l ++ (y1 ∷ y2 ∷ y3 ∷ y4 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ z ∷ [])

  data Time : List Dig → Set where
    utctm : ∀ {@0 bs} → UtcTime bs → Time bs
    gentm  : ∀ {@0 bs} → GenTime  bs → Time bs

  record Validity (bs : List Dig) : Set where
    constructor mkValidity
    field
      @0 {l nb na} : List Dig
      len : Length l
      start : Time nb
      end : Time na
      @0 len≡ : getLength len ≡ length (nb ++ na)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ nb ++ na

-----------------------------------------Extensions------------------------------------------
  postulate
     AIAFields : List Dig → Set
     UNExtnFields : List Dig → Set

     Akiauthcertiss : List Dig → Set
     Othernamegen : List Dig → Set
     Rfcnamegen : List Dig → Set
     Dnsnamegen : List Dig → Set
     X400addgen : List Dig → Set
     Dirnamegen : List Dig → Set
     Edinamegen : List Dig → Set
     Urigen : List Dig → Set
     Ipaddgen : List Dig → Set
     Ridgen : List Dig → Set

     Qualifier : List Dig → Set

 ----------------------- aki extension -------------------
 
  record Akikeyid (bs : List Dig) : Set where
    constructor mkAkikeyid
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.Eighty ∷ l ++ v

  record Akiauthcertsn (bs : List Dig) : Set where
    constructor mkAkiauthcertsn
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.IntegerValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyTwo ∷ l ++ v

  record AKIFields (bs : List Dig) : Set where
    constructor mkAKIFields
    field
      @0 {l1 l2 akid ci csn} : List Dig
      len1 : Length l1
      len2 : Length l2
      akeyid : Generic.Option Akikeyid akid
      authcertiss : Generic.Option Akiauthcertiss ci
      authcertsn : Generic.Option Akiauthcertsn csn
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ akid ++ ci ++ csn)
      @0 len2≡ : getLength len2 ≡ length (akid ++ ci ++ csn)
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ akid ++ ci ++ csn
------------------------------------------------------------------------------------------
  record SKIFields (bs : List Dig) : Set where
    constructor mkSKIFields
    field
      @0 {l1 l2 skid} : List Dig
      len1 : Length l1
      len2 : Length l2
      skeyid : Generic.OctetValue skid
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ skid)
      @0 len2≡ : getLength len2 ≡ length skid
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Octetstring ∷ l2) ++ skid

  record KUFields (bs : List Dig) : Set where
    constructor mkKu
    field
      @0 {l1 l2 bits} : List Dig
      len1 : Length l1
      len2 : Length l2
      kubits : Generic.OctetValue bits
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ bits)
      @0 len2≡ : getLength len2 ≡ length bits
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Bitstring ∷ l2) ++ bits

----------------------------------- eku extension -----------------------------------
  data EkuSeqElems : List Dig → Set

  record EkuSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkEkuSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      extn : Generic.OID bs₁
      rest   : EkuSeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data EkuSeqElems where
    _∷[]  : ∀ {x} → Generic.OID x → EkuSeqElems x
    cons : ∀ {x} → EkuSeqElemsₐ x → EkuSeqElems x

  record EKUFields (bs : List Dig) : Set where
    constructor mkEku
    field
      @0 {l1 l2 elems} : List Dig
      len1 : Length l1
      len2 : Length l2
      seqelems : EkuSeqElems elems
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ elems)
      @0 len2≡ : getLength len2 ≡ length elems
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ elems
      
-------------------------------------------------------------------------------

  record BCFields (bs : List Dig) : Set where
    constructor mkBCFields
    field
      @0 {l1 l2 ca pl} : List Dig
      len1 : Length l1
      len2 : Length l2
      bcca : Generic.Boool ca
      bcpathlen : Generic.Option Generic.Int pl
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ ca ++ pl)
      @0 len2≡ : getLength len2 ≡ length (ca ++ pl)
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ ca ++ pl

-------------------------- ian/san alternative names extensions ------------------

  data Generalname : List Dig → Set where
    oname : ∀ {@0 bs} → Othernamegen bs → Generalname bs
    rfcname : ∀ {@0 bs} → Rfcnamegen bs → Generalname bs
    dnsname : ∀ {@0 bs} → Dnsnamegen bs → Generalname bs
    x400add : ∀ {@0 bs} → X400addgen bs → Generalname bs
    dirname : ∀ {@0 bs} → Dirnamegen bs → Generalname bs
    ediname : ∀ {@0 bs} → Edinamegen bs → Generalname bs
    uri : ∀ {@0 bs} → Urigen bs → Generalname bs
    ipadd : ∀ {@0 bs} → Ipaddgen bs → Generalname bs
    rid : ∀ {@0 bs} → Ridgen bs → Generalname bs
    
  data Generalnames : List Dig → Set

  record Generalnamesₐ (bs : List Dig) : Set where
    inductive
    constructor mkGeneralnamesₐ
    field
      @0 {bs₁ bs₂} : List Dig
      extn : Generalname bs₁
      rest   : Generalnames bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data Generalnames where
    _∷[]  : ∀ {x} → Generalname x → Generalnames x
    cons : ∀ {x} → Generalnamesₐ x → Generalnames x

  record IANFields (bs : List Dig) : Set where
    constructor mkIANFields
    field
      @0 {l iannames} : List Dig
      len : Length l
      iangens : Generalnames iannames
      @0 len≡ : getLength len ≡ length iannames
      @0 bs≡  : bs ≡ Tag.Octetstring ∷ l ++ iannames

  record SANFields (bs : List Dig) : Set where
    constructor mkSANFields
    field
      @0 {l sannames} : List Dig
      len : Length l
      sangens : Generalnames sannames
      @0 len≡ : getLength len ≡ length sannames
      @0 bs≡  : bs ≡ Tag.Octetstring ∷ l ++ sannames

------------------------- certificate policies -------------------------

  record Polqualinfo (bs : List Dig) : Set where
    constructor mkPolqualinfo
    field
      @0 {l pqlid ql} : List Dig
      len : Length l
      cpqlid : Generic.OID pqlid
      cql : Qualifier ql
      @0 len≡ : getLength len ≡ length (pqlid ++ ql)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ pqlid ++ ql

  record PolicyInformation (bs : List Dig) : Set where
    constructor mkPolicyInformation
    field
      @0 {l pid pql} : List Dig
      len : Length l
      cpid : Generic.OID pid
      cpql : Generic.Option Polqualinfo pql
      @0 len≡ : getLength len ≡ length (pid ++ pql)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ pid ++ pql

  data CertPolSeqElems : List Dig → Set

  record CertPolSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkCertPolSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      polinfo : PolicyInformation bs₁
      rest   : CertPolSeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data CertPolSeqElems where
    _∷[]  : ∀ {x} → PolicyInformation x → CertPolSeqElems x
    cons : ∀ {x} → CertPolSeqElemsₐ x → CertPolSeqElems x

  record CertPolFields (bs : List Dig) : Set where
    constructor mkCertPolFields
    field
      @0 {l1 l2 elems} : List Dig
      len1 : Length l1
      len2 : Length l2
      seqelems : CertPolSeqElems elems
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ elems)
      @0 len2≡ : getLength len2 ≡ length elems
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ elems

----------------------------- crl dist point extension --------------------------------

  record Crlissuer (bs : List Dig) : Set where
    constructor mkCrlissuer
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generalnames v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A2 ∷ l ++ v

  record Reasonsflag (bs : List Dig) : Set where
    constructor mkReasonsflag
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetValue v  -- TODO : make it BIT String
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyOne ∷ l ++ v

  record Fullname (bs : List Dig) : Set where
    constructor mkFullname
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generalnames v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A0 ∷ l ++ v

  record NameRTCrlissr (bs : List Dig) : Set where
    constructor mkNameRTCrlissr
    field
      @0 {l v} : List Dig
      len : Length l
      val : RDName v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A1 ∷ l ++ v

  data Distpointname : List Dig → Set where
    fullname : ∀ {@0 bs} → Fullname bs → Distpointname bs
    nameRTCrlissr : ∀ {@0 bs} → NameRTCrlissr bs → Distpointname bs
      
  record Distpoint (bs : List Dig) : Set where
    constructor mkDistpoint
    field
      @0 {l dp rsn issr} : List Dig
      len : Length l
      crldp : Generic.Option Distpointname dp
      crldprsn : Generic.Option Reasonsflag rsn
      crlissr : Generic.Option Crlissuer issr
      @0 len≡ : getLength len ≡ length (dp ++ rsn ++ issr)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ dp ++ rsn ++ issr

  data Seqcrldist : List Dig → Set

  record Seqcrldistₐ (bs : List Dig) : Set where
    inductive
    constructor mkSeqcrldistₐ
    field
      @0 {bs₁ bs₂} : List Dig
      extn : Distpoint bs₁
      rest   : Seqcrldist bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data Seqcrldist where
    _∷[]  : ∀ {x} → Distpoint x → Seqcrldist x
    cons : ∀ {x} → Seqcrldistₐ x → Seqcrldist x

  record CRLDistFields (bs : List Dig) : Set where
    constructor mkCRLDistFields
    field
      @0 {l dps} : List Dig
      len : Length l
      crldps : Seqcrldist dps
      @0 len≡ : getLength len ≡ length dps
      @0 bs≡  : bs ≡ Tag.Octetstring ∷ l ++ dps

--------------------------------Extensions selection----------------------------------------

  module ExtensionOID where
    AKI : List Dig
    AKI = # 2 ∷ # 5 ∷ # 29 ∷ [ # 35 ]

    SKI : List Dig
    SKI = # 2 ∷ # 5 ∷ # 29 ∷ [ # 14 ]

    KU : List Dig
    KU = # 2 ∷ # 5 ∷ # 29 ∷ [ # 15 ]

    EKU : List Dig
    EKU = # 2 ∷ # 5 ∷ # 29 ∷ [ # 37 ]

    BC : List Dig
    BC = # 2 ∷ # 5 ∷ # 29 ∷ [ # 19 ]

    IAN : List Dig
    IAN = # 2 ∷ # 5 ∷ # 29 ∷ [ # 18 ]

    SAN : List Dig
    SAN = # 2 ∷ # 5 ∷ # 29 ∷ [ # 17 ]

    CPOL : List Dig
    CPOL = # 2 ∷ # 5 ∷ # 29 ∷ [ # 32 ]

    CRLDIST : List Dig
    CRLDIST = # 2 ∷ # 5 ∷ # 29 ∷ [ # 31 ]

    AIA : List Dig
    AIA = # 1 ∷ # 3 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 1 ∷ [ # 1 ]

  data Selectextn : List Dig →  List Dig → Set where
    akiextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.AKI) → AKIFields bs2 → Selectextn bs1 bs2
    skiextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.SKI) → SKIFields bs2 → Selectextn bs1 bs2
    kuextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.KU) → KUFields bs2 → Selectextn bs1 bs2
    ekuextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.EKU) → EKUFields bs2 → Selectextn bs1 bs2
    bcextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.BC) → BCFields bs2 → Selectextn bs1 bs2
    ianextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.IAN) → IANFields bs2 → Selectextn bs1 bs2
    sanextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.SAN) → SANFields bs2 → Selectextn bs1 bs2
    cpextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.CPOL) → CertPolFields bs2 → Selectextn bs1 bs2
    crlextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.CRLDIST) → CRLDistFields bs2 → Selectextn bs1 bs2
    aiaextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.AIA) → AIAFields bs2 → Selectextn bs1 bs2
    unextn : ∀ {@0 bs1 bs2} → UNExtnFields bs2 → Selectextn bs1 bs2

  record Extension (bs : List Dig) : Set where
    constructor mkExtension
    field
      @0 {l oex cex ocex} : List Dig
      len : Length l
      oidextn : Generic.OID oex
      critical : Generic.Option Generic.Boool cex
      octetextn :  Selectextn oex ocex
      @0 len≡ : getLength len ≡ length (oex ++ cex ++ ocex)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ oex ++ cex ++ ocex

  data ExtensionsSeqElems : List Dig → Set

  record ExtensionsSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkExtensionsSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      extn : Extension bs₁
      rest   : ExtensionsSeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data ExtensionsSeqElems where
    _∷[]  : ∀ {x} → Extension x → ExtensionsSeqElems x
    cons : ∀ {x} → ExtensionsSeqElemsₐ x → ExtensionsSeqElems x

  record ExtensionsSeq (bs : List Dig) : Set where
    constructor mkExtensionsSeq
    field
      @0 {l exs} : List Dig
      len : Length l
      elems :  ExtensionsSeqElems exs
      @0 len≡ : getLength len ≡ length exs
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ exs

  record Extensions (bs : List Dig) : Set where
    constructor mkExtensions
    field
      @0 {l e} : List Dig
      len : Length l
      elem :  ExtensionsSeq e
      @0 len≡ : getLength len ≡ length e
      @0 bs≡  : bs ≡ Tag.Extensions ∷ l ++ e

-----------------------------------------------------------------------------------------------

  record TBSCert (bs : List Dig) : Set where
    constructor mkTBSCert
    field
      @0 {l ver ser sa i va u p u₁ u₂ e} : _
      len : Length l
      version : Generic.Option Version ver
      serial  : Generic.Int ser
      signAlg : SignAlg sa
      issuer  : RDName i
      validity : Validity va
      subject  : RDName u
      pk       : PublicKey p
      issuerUID : Generic.Option IssUID u₁
      subjectUID : Generic.Option SubUID u₂
      extensions : Generic.Option Extensions e
      @0 len≡ : getLength len ≡ length (ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

  ---------------------------------Certificate---------------------------------------------------
  record Signature (bs : List Dig) : Set where
    constructor mkSig
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.Bitstring ∷ l ++ v

  record Cert (bs : List Dig) : Set where
    constructor mkCert
    field
      @0 {l t sa sig} : List Dig
      len : Length l
      tbs : TBSCert t
      signAlg : SignAlg sa
      signature : Signature sig
      @0 len≡ : getLength len ≡ length (t ++ sa ++ sig)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ t ++ sa ++ sig
