{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Data.X509 where

open import Aeres.Binary
open Base256
open import Aeres.Grammar.Definitions Dig

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

    Eighty : Dig
    Eighty = # 128

    EightyOne : Dig
    EightyOne = # 129

    EightyTwo : Dig
    EightyTwo = # 130

    EightyThree : Dig
    EightyThree = # 131

    EightyFour : Dig
    EightyFour = # 132

    EightyFive : Dig
    EightyFive = # 133

    EightySix : Dig
    EightySix = # 134

    EightySeven : Dig
    EightySeven = # 135

    EightyEight : Dig
    EightyEight = # 136

    A0 : Dig
    A0 = # 160

    A1 : Dig
    A1 = # 161

    A2 : Dig
    A2 = # 162

    A3 : Dig
    A3 = # 163

    A4 : Dig
    A4 = # 164

    A5 : Dig
    A5 = # 165

    A6 : Dig
    A6 = # 166

    --- directory string tags
    BMPString : Dig
    BMPString = # 30

    UniversalString : Dig
    UniversalString = # 28

    PrintableString : Dig
    PrintableString = # 19

    TeletexString : Dig
    TeletexString = # 20

    UTF8String : Dig
    UTF8String = # 12

    IA5String : Dig
    IA5String = # 22

    VisibleString : Dig
    VisibleString = # 26
-----------------------------------------Length------------------------------------------
module Length where

  record Short (bs : List Dig) : Set where
    constructor mkShort
    field
      l : Dig
      @0 l<128 : toℕ l < 128
      @0 bs≡ : bs ≡ [ l ]
  open Short

  MinRep : Dig → List Dig → Set
  MinRep lₕ lₜ =
    if ⌊ lₜ ≟ [] ⌋ then toℕ lₕ ≥ 128 else ⊤

  MinRep-elim
    : ∀ {ℓ} lₕ lₜ (P : Dig → List Dig → Set ℓ) →
      (lₜ ≡ [] → toℕ lₕ ≥ 128 → P lₕ lₜ) →
      (lₜ ≢ [] → P lₕ lₜ) →
      MinRep lₕ lₜ → P lₕ lₜ
  MinRep-elim lₕ lₜ P pf₁ pf₂ mr
    with lₜ ≟ []
  ... | no  lₜ≢[] = pf₂ lₜ≢[]
  ... | yes lₜ≡[] = pf₁ lₜ≡[] mr

  record Long (bs : List Dig) : Set where
    constructor mkLong
    field
      l : Dig
      @0 l>128 : 128 < toℕ l
      lₕ : Dig
      @0 lₕ≢0 : toℕ lₕ > 0
      lₜ : List Dig
      @0 lₜLen : length lₜ ≡ toℕ l - 129
      @0 lₕₜMinRep : MinRep lₕ lₜ
      @0 bs≡ : bs ≡ l ∷ lₕ ∷ lₜ
  open Long

  data Length : List Dig → Set where
    short : ∀ {@0 bs} → Short bs → Length bs
    long  : ∀ {@0 bs} → Long  bs → Length bs

  shortₛ : ∀ l → {@0 _ : True (toℕ l <? 128)} → Length [ l ]
  shortₛ l {l<128} = short (mkShort l (toWitness l<128) refl)

  mkLongₛ : ∀ l lₕ lₜ →
          {@0 _ : True (128 <? toℕ l)}
          {@0 _ : True (toℕ lₕ >? 0)}
          {@0 _ : True (length lₜ ≟ (toℕ l - 129))}
          {@0 _ : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128)}
          → Long (l ∷ lₕ ∷ lₜ)
  mkLongₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr} =
   (mkLong l
          (toWitness l>128) lₕ
          (toWitness lₕ≢0) lₜ
          (toWitness lₜLen) (go mr) {- (toWitness mr) -} refl)
   where
   go : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128) → if ⌊ lₜ ≟ [] ⌋ then toℕ lₕ ≥ 128 else ⊤
   go mr
     with toWitness mr
   ... | inj₁ lₜ≢[]
     with lₜ ≟ []
   ... | no  _ = tt
   ... | yes lₜ≡[] = contradiction lₜ≡[] lₜ≢[]
   go mr | inj₂ y
     with lₜ ≟ []
   ... | no _ = tt
   ... | yes lₜ≡[] = y

  longₛ : ∀ l lₕ lₜ →
        {@0 _ : True (128 <? toℕ l)}
        {@0 _ : True (toℕ lₕ >? 0)}
        {@0 _ : True (length lₜ ≟ (toℕ l - 129))}
        {@0 _ : True (lₜ ≠ [] ⊎-dec toℕ lₕ ≥? 128)}
            → Length (l ∷ lₕ ∷ lₜ)
  longₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr} =
    long (mkLongₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} {mr})

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

  record TLV (t : Dig) (A : List Dig → Set) (@0 bs : List Dig) : Set where
    constructor mkTLV
    field
      @0 {l v} : List Dig
      len : Length l
      val : A v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ t ∷ l ++ v

  postulate
    OctetString : List Dig → Set

  record IntegerValue (@0 bs : List Dig) : Set where
    constructor mkIntegerValue
    field
      val : ℤ
      @0 bs≡ : twosComplement bs ≡ val

  record Int (@0 bs : List Dig) : Set where
    constructor mkInt
    field
      @0 {l v} : List Dig
      len : Length l
      val : IntegerValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.Integer ∷ l ++ v

  BitstringUnusedBits : Dig → List Dig → Set
  BitstringUnusedBits bₕ [] = bₕ ≡ # 0
  BitstringUnusedBits bₕ (_ ∷ _) = ⊤

  record BitstringValue (@0 bs : List Dig) : Set where
    constructor mkBitstringValue
    field
      bₕ : Dig
      @0 bₕ<8 : toℕ bₕ < 8
      bₜ : List Dig
      @0 unusedBits : BitstringUnusedBits bₕ bₜ
      @0 bs≡ : bs ≡ bₕ ∷ bₜ

  Bitstring : (@0 _ : List Dig) → Set
  Bitstring xs = TLV Tag.Bitstring BitstringValue xs

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

  record Boool (@0 bs : List Dig) : Set where
    constructor mkBoool
    field
      @0 {l} : List Dig
      len : Length l
      v : Dig
      @0 len≡ : getLength len ≡ 1
      @0 bs≡ : bs ≡  Tag.Boolean ∷ l ++ (v ∷ [])

------------------------------X.509-----------------------------------------------------------

module X509 where

  postulate
    IA5StringValue : List Dig → Set

  module SOID where
    --TODO : add other RSA signature algorithms
    Md5Rsa : List Dig
    Md5Rsa = # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 4 ]
    
    Sha1Rsa : List Dig
    Sha1Rsa =  # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 5 ]

    RsaPss : List Dig
    RsaPss =  # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 10 ]
    
    Sha256Rsa : List Dig
    Sha256Rsa = # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 11 ]

    Sha384Rsa : List Dig
    Sha384Rsa =  # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 12 ]

    Sha512Rsa : List Dig
    Sha512Rsa = # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 13 ]

    Sha224Rsa : List Dig
    Sha224Rsa = # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 14 ]

  -- RSA explicit null param case covered here
  -- TODO : add cases for other RSA signature algorithms
  data SignParam : List Dig →  List Dig → Set where
    md5rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Md5Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha1rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha1Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    rsapssp : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.RsaPss) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha256rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha256Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha384rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha384Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha512rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha512Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha224rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha224Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    _ : ∀ {@0 bs1 bs2} → Generic.OctetString bs2 → SignParam bs1 bs2

  record SignAlg (bs : List Dig) : Set where
    constructor mkSignAlg
    field
      @0 {l o p} : List Dig
      len : Length l
      signOID : Generic.OID o
      param   : SignParam o p -- RSA implicit null param case covered here; why "Option" not working here???
      @0 len≡ : getLength len ≡ length (o ++ p)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ o ++ p

 --------------- RDNSeq -------------------------------------

  record TeletexString (bs : List Dig) : Set where 
    constructor mkTeletexString
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.TeletexString ∷ l ++ v

  record PrintableString (bs : List Dig) : Set where 
    constructor mkPrintableString
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.PrintableString ∷ l ++ v

  record UniversalString (bs : List Dig) : Set where 
    constructor mkUniversalString
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.UniversalString ∷ l ++ v

  record UTF8String (bs : List Dig) : Set where 
    constructor mkUTF8String
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.UTF8String ∷ l ++ v

  record BMPString (bs : List Dig) : Set where 
    constructor mkBMPString
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.BMPString ∷ l ++ v

  record IA5String (bs : List Dig) : Set where 
    constructor mkIA5String
    field
      @0 {l v} : List Dig
      len : Length l
      val : IA5StringValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.IA5String ∷ l ++ v

  record VisibleString (bs : List Dig) : Set where 
    constructor mkVisibleString
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.VisibleString ∷ l ++ v
  
  data DirectoryString : List Dig → Set where
    teletexString : ∀ {@0 bs} → TeletexString bs → DirectoryString bs
    printableString : ∀ {@0 bs} → PrintableString bs → DirectoryString bs
    universalString : ∀ {@0 bs} → UniversalString bs → DirectoryString bs
    utf8String : ∀ {@0 bs} → UTF8String bs → DirectoryString bs
    bmpString : ∀ {@0 bs} → BMPString bs → DirectoryString bs

  data DisplayText : List Dig → Set where
    ia5String : ∀ {@0 bs} → IA5String bs → DisplayText bs
    visibleString : ∀ {@0 bs} → VisibleString bs → DisplayText bs
    bmpString : ∀ {@0 bs} → BMPString bs → DisplayText bs
    utf8String : ∀ {@0 bs} → UTF8String bs → DisplayText bs
 
  record RDNSetSeq (bs : List Dig) : Set where
    constructor mkRDNSetSeq
    field
      @0 {l o v} : List Dig
      len : Length l
      oid : Generic.OID o
      val : DirectoryString v
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

  record RDNSeq (bs : List Dig) : Set where
    constructor mkRDNSeq
    field
      @0 {l e} : List Dig
      len : Length l
      elems : RDNSeqElems e
      @0 len≡ : getLength len ≡ length e
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ e

----------------------- Generalnames --------------------

  --- we do not support OtherName since very rarely used
  record OtherName (bs : List Dig) : Set where 
    constructor mkOtherName
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v -- abstracted
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A0 ∷ l ++ v

  record RfcName (bs : List Dig) : Set where 
    constructor mkRfcName
    field
      @0 {l v} : List Dig
      len : Length l
      val : IA5StringValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyOne ∷ l ++ v

  record DnsName (bs : List Dig) : Set where 
    constructor mkDnsName
    field
      @0 {l v} : List Dig
      len : Length l
      val : IA5StringValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyTwo ∷ l ++ v

  --- we do not support X400Address since very rarely used
  record X400Address (bs : List Dig) : Set where 
    constructor mkX400Address
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v -- abstracted
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A3 ∷ l ++ v

  record DirName (bs : List Dig) : Set where 
    constructor mkDirName
    field
      @0 {l v} : List Dig
      len : Length l
      val : RDNSeqElems v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A4 ∷ l ++ v

  --- we do not support EdipartyName since very rarely used
  record EdipartyName (bs : List Dig) : Set where 
    constructor mkEdipartyName
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v --abstracted
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A5 ∷ l ++ v

  record URI (bs : List Dig) : Set where 
    constructor mkURI
    field
      @0 {l v} : List Dig
      len : Length l
      val : IA5StringValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightySix ∷ l ++ v

  record IpAddress (bs : List Dig) : Set where 
    constructor mkIpAddress
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightySeven ∷ l ++ v

  record RegID (bs : List Dig) : Set where 
    constructor mkRegID
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OIDField v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyEight ∷ l ++ v
  
  data Generalname : List Dig → Set where
    oname : ∀ {@0 bs} → OtherName bs → Generalname bs
    rfcname : ∀ {@0 bs} → RfcName bs → Generalname bs
    dnsname : ∀ {@0 bs} → DnsName bs → Generalname bs
    x400add : ∀ {@0 bs} → X400Address bs → Generalname bs
    dirname : ∀ {@0 bs} → DirName bs → Generalname bs
    ediname : ∀ {@0 bs} → EdipartyName bs → Generalname bs
    uri : ∀ {@0 bs} → URI bs → Generalname bs
    ipadd : ∀ {@0 bs} → IpAddress bs → Generalname bs
    rid : ∀ {@0 bs} → RegID bs → Generalname bs
    
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

  --------------------------TBSCert-----------------------------------------------------------------
  record Version (@0 bs : List Dig) : Set where
    constructor mkVersion
    field
      @0 {l v} : List Dig
      len : Length l
      ver : Generic.Int v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A0 ∷ l ++ v

  record IssUID (@0 bs : List Dig) : Set where
    constructor mkIssUid
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.BitstringValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyOne ∷ l ++ v

  record SubUID (@0 bs : List Dig) : Set where
    constructor mkSubUid
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.BitstringValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyTwo ∷ l ++ v

--------------------------------------------------------- Validity --------------------------------
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
      @0 bs≡  : bs ≡ Tag.Gentime ∷ l ++ (y1 ∷ y2 ∷ y3 ∷ y4 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ z ∷ [])

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

  record PublicKey (bs : List Dig) : Set where
    constructor mkPublicKey
    field
      @0 {l alg pk} : List Dig
      len : Length l
      algrithm : SignAlg alg
      pubkey : Generic.Bitstring pk
      @0 len≡ : getLength len ≡ length (alg ++ pk)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ alg ++ pk

-----------------------------------------Extensions------------------------------------------
 ----------------------- aki extension -------------------
 
  record AKIKeyId (@0 bs : List Dig) : Set where
    constructor mkAKIKeyId
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.OctetString v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.Eighty ∷ l ++ v

  record AKIAuthCertIssuer (@0 bs : List Dig) : Set where
    constructor mkAKIAuthCertIssuer
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generalnames v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A1 ∷ l ++ v

  record AKIAuthCertSN (@0 bs : List Dig) : Set where
    constructor mkAKIAuthCertSN
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.IntegerValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyTwo ∷ l ++ v

  record AKIFields (@0 bs : List Dig) : Set where
    constructor mkAKIFields
    field
      @0 {l1 l2 akid ci csn} : List Dig
      len1 : Length l1
      len2 : Length l2
      akeyid : Option AKIKeyId akid
      authcertiss : Option AKIAuthCertIssuer ci
      authcertsn : Option AKIAuthCertSN csn
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
      skeyid : Generic.OctetString skid
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ skid)
      @0 len2≡ : getLength len2 ≡ length skid
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Octetstring ∷ l2) ++ skid

  record KUFields (bs : List Dig) : Set where
    constructor mkKu
    field
      @0 {l bitstr} : List Dig
      len : Length l
      kubitstr : Generic.Bitstring bitstr
      @0 len≡ : getLength len ≡ length bitstr
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l) ++ bitstr

----------------------------------- eku extension -----------------------------------
  data EkuSeqElems : List Dig → Set

  record EkuSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkEkuSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      ekuid : Generic.OID bs₁
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

  record BCFields (@0 bs : List Dig) : Set where
    constructor mkBCFields
    field
      @0 {l1 l2 ca pl} : List Dig
      len1 : Length l1
      len2 : Length l2
      bcca : Option Generic.Boool ca
      bcpathlen : Option Generic.Int pl
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ ca ++ pl)
      @0 len2≡ : getLength len2 ≡ length (ca ++ pl)
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ ca ++ pl

-------------------------- ian/san alternative names extensions ------------------
  record IANFields (bs : List Dig) : Set where
    constructor mkIANFields
    field
      @0 {l1 l2 iannames} : List Dig
      len1 : Length l1
      len2 : Length l2
      iangens : Generalnames iannames
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ iannames)
      @0 len2≡ : getLength len2 ≡ length iannames
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ iannames

  record SANFields (bs : List Dig) : Set where
    constructor mkSANFields
    field
      @0 {l1 l2 sannames} : List Dig
      len1 : Length l1
      len2 : Length l2
      sangens : Generalnames sannames
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ sannames)
      @0 len2≡ : getLength len2 ≡ length sannames
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ sannames

------------------------- certificate policies -------------------------
  module PQOID where
    CPSURI : List Dig
    CPSURI = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 1 ]

    USERNOTICE : List Dig
    USERNOTICE = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ [ # 2 ]

  data IntegerSeqElems : List Dig → Set

  record IntegerSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkIntegerSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      intnum : Generic.Int bs₁
      rest   : IntegerSeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data IntegerSeqElems where
    _∷[]  : ∀ {x} → Generic.Int x → IntegerSeqElems x
    cons : ∀ {x} → IntegerSeqElemsₐ x → IntegerSeqElems x

  record IntegerSeq (bs : List Dig) : Set where
    constructor mkIntegerSeq
    field
      @0 {l elems} : List Dig
      len : Length l
      seqelems : IntegerSeqElems elems
      @0 len≡ : getLength len ≡ length elems
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ elems

  record NoticeReference (@0 bs : List Dig) : Set where
    constructor mkNoticeReference
    field
      @0 {l org nn} : List Dig
      len : Length l
      organiztion : DisplayText org
      noticenums : IntegerSeq nn
      @0 len≡ : getLength len ≡ length (org ++ nn)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ org ++ nn

  record UserNotice (@0 bs : List Dig) : Set where
    constructor mkUserNotice
    field
      @0 {l nr et} : List Dig
      len : Length l
      noticeRef : Option NoticeReference nr
      expText : Option DisplayText et
      @0 len≡ : getLength len ≡ length (nr ++ et)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ nr ++ et

  data Qualifier : List Dig →  List Dig → Set where
    cpsuri : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ PQOID.CPSURI) → IA5String bs2 → Qualifier bs1 bs2
    unotice : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ PQOID.USERNOTICE) → UserNotice bs2 → Qualifier bs1 bs2
    
  data PolicyQualifierId : List Dig → Set where
    cpsuriid : ∀ {@0 bs} → (@0 _ : bs ≡ PQOID.CPSURI) → PolicyQualifierId bs
    unoticeid : ∀ {@0 bs} → (@0 _ : bs ≡ PQOID.USERNOTICE) → PolicyQualifierId bs
    
  record PolicyQualifierInfo (@0 bs : List Dig) : Set where
    constructor mkPolicyQualifierInfo
    field
      @0 {l pqlid ql} : List Dig
      len : Length l
      cpqlid : PolicyQualifierId pqlid
      cql : Qualifier pqlid ql
      @0 len≡ : getLength len ≡ length (pqlid ++ ql)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ pqlid ++ ql

  data PolicyQualifiersSeqElems : List Dig → Set

  record PolicyQualifiersSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkPolicyQualifiersSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      extn : PolicyQualifierInfo bs₁
      rest   : PolicyQualifiersSeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data PolicyQualifiersSeqElems where
    _∷[]  : ∀ {x} → PolicyQualifierInfo x → PolicyQualifiersSeqElems x
    cons : ∀ {x} → PolicyQualifiersSeqElemsₐ x → PolicyQualifiersSeqElems x

  record PolicyQualifiersSeq (bs : List Dig) : Set where
    constructor mkPolicyQualifiersSeq
    field
      @0 {l elems} : List Dig
      len : Length l
      seqelems : PolicyQualifiersSeqElems elems
      @0 len≡ : getLength len ≡ length elems
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ elems

  record PolicyInformation (bs : List Dig) : Set where
    constructor mkPolicyInformation
    field
      @0 {l pid pqls} : List Dig
      len : Length l
      cpid : Generic.OID pid
      cpqls : Option PolicyQualifiersSeq pqls
      @0 len≡ : getLength len ≡ length (pid ++ pqls)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ pid ++ pqls

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

  record CrlIssuer (@0 bs : List Dig) : Set where
    constructor mkCrlIssuer
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generalnames v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A2 ∷ l ++ v

  record ReasonFlags (@0 bs : List Dig) : Set where
    constructor mkReasonFlags
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generic.BitstringValue v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.EightyOne ∷ l ++ v

  record FullName (bs : List Dig) : Set where
    constructor mkFullName
    field
      @0 {l v} : List Dig
      len : Length l
      val : Generalnames v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A0 ∷ l ++ v

  record NameRTCrlIssuer (bs : List Dig) : Set where
    constructor mkNameRTCrlIssuer
    field
      @0 {l v} : List Dig
      len : Length l
      val : RDNSeq v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.A1 ∷ l ++ v

  data DistPointNameChoice : (@0 _ : List Dig) → Set where
    fullname : ∀ {@0 bs} → FullName bs → DistPointNameChoice bs
    nameRTCrlissr : ∀ {@0 bs} → NameRTCrlIssuer bs → DistPointNameChoice bs

  record DistPointName (bs : List Dig) : Set where
    constructor mkDistPointName
    field
      @0 {l dpname} : List Dig
      len : Length l
      dpnamechoice : DistPointNameChoice dpname
      @0 len≡ : getLength len ≡ length dpname
      @0 bs≡  : bs ≡ Tag.A0 ∷ l ++ dpname
      
  record DistPoint (bs : List Dig) : Set where
    constructor mkDistPoint
    field
      @0 {l dp rsn issr} : List Dig
      len : Length l
      crldp : Option DistPointName dp
      crldprsn : Option ReasonFlags rsn
      crlissr : Option CrlIssuer issr
      @0 len≡ : getLength len ≡ length (dp ++ rsn ++ issr)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ dp ++ rsn ++ issr

  data CRLSeqElems : List Dig → Set

  record CRLSeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkCRLSeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      extn : DistPoint bs₁
      rest   : CRLSeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data CRLSeqElems where
    _∷[]  : ∀ {x} → DistPoint x → CRLSeqElems x
    cons : ∀ {x} → CRLSeqElemsₐ x → CRLSeqElems x

  record CRLDistFields (bs : List Dig) : Set where
    constructor mkCRLDistFields
    field
      @0 {l1 l2 elems} : List Dig
      len1 : Length l1
      len2 : Length l2
      seqelems : CRLSeqElems elems
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ elems)
      @0 len2≡ : getLength len2 ≡ length elems
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ elems
      
----------------------------------------- Authority Info access -----------------
  module ACMOID where
    CAISSUERS : List Dig
    CAISSUERS = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 2 ]

    OCSP : List Dig
    OCSP = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 1 ]

  data AccessMethod : List Dig → Set where
    caissid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.CAISSUERS) → AccessMethod bs
    ocspid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.OCSP) → AccessMethod bs

  record AccessDesc (bs : List Dig) : Set where
    constructor mkAccessDesc
    field
      @0 {l acm acl} : List Dig
      len : Length l
      acmethod : AccessMethod acm
      aclocation : Generalname acl
      @0 len≡ : getLength len ≡ length (acm ++ acl)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ acm ++ acl

  data AIASeqElems : List Dig → Set

  record AIASeqElemsₐ (bs : List Dig) : Set where
    inductive
    constructor mkAIASeqElemsₐ
    field
      @0 {bs₁ bs₂} : List Dig
      extn : AccessDesc bs₁
      rest   : AIASeqElems bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data AIASeqElems where
    _∷[]  : ∀ {x} → AccessDesc x → AIASeqElems x
    cons : ∀ {x} → AIASeqElemsₐ x → AIASeqElems x
    
  record AIAFields (bs : List Dig) : Set where
    constructor mkAIAFields
    field
      @0 {l1 l2 elems} : List Dig
      len1 : Length l1
      len2 : Length l2
      seqelems : AIASeqElems elems
      @0 len1≡ : getLength len1 ≡ 1 + length (l2 ++ elems)
      @0 len2≡ : getLength len2 ≡ length elems
      @0 bs≡  : bs ≡ (Tag.Octetstring ∷ l1) ++ (Tag.Sequence ∷ l2) ++ elems

----------------------------- unknown extension ----------------------

  record UknwnExtnFields (bs : List Dig) : Set where
    constructor mkUknwnExtnFields
    field
      @0 {l os} : List Dig
      len : Length l
      ocstr : Generic.OctetString os
      @0 len≡ : getLength len ≡ length os
      @0 bs≡  : bs ≡ Tag.Octetstring ∷ l ++ os 

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

  data SelectExtn : List Dig →  List Dig → Set where
    akiextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.AKI) → AKIFields bs2 → SelectExtn bs1 bs2
    skiextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.SKI) → SKIFields bs2 → SelectExtn bs1 bs2
    kuextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.KU) → KUFields bs2 → SelectExtn bs1 bs2
    ekuextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.EKU) → EKUFields bs2 → SelectExtn bs1 bs2
    bcextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.BC) → BCFields bs2 → SelectExtn bs1 bs2
    ianextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.IAN) → IANFields bs2 → SelectExtn bs1 bs2
    sanextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.SAN) → SANFields bs2 → SelectExtn bs1 bs2
    cpextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.CPOL) → CertPolFields bs2 → SelectExtn bs1 bs2
    crlextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.CRLDIST) → CRLDistFields bs2 → SelectExtn bs1 bs2
    aiaextn : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ ExtensionOID.AIA) → AIAFields bs2 → SelectExtn bs1 bs2
    _ : ∀ {@0 bs1 bs2} → UknwnExtnFields bs2 → SelectExtn bs1 bs2

  record Extension (bs : List Dig) : Set where
    constructor mkExtension
    field
      @0 {l oex cex ocex} : List Dig
      len : Length l
      oidextn : Generic.OID oex
      critical : Option Generic.Boool cex
      octetextn :  SelectExtn oex ocex
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

  record Extensions (@0 bs : List Dig) : Set where
    constructor mkExtensions
    field
      @0 {l e} : List Dig
      len : Length l
      elem :  ExtensionsSeq e
      @0 len≡ : getLength len ≡ length e
      @0 bs≡  : bs ≡ Tag.A3 ∷ l ++ e

-----------------------------------------------------------------------------------------------

  record TBSCert (bs : List Dig) : Set where
    constructor mkTBSCert
    field
      @0 {l ver ser sa i va u p u₁ u₂ e} : _
      len : Length l
      version : Option Version ver
      serial  : Generic.Int ser
      signAlg : SignAlg sa
      issuer  : RDNSeq i
      validity : Validity va
      subject  : RDNSeq u
      pk       : PublicKey p
      issuerUID : Option IssUID u₁
      subjectUID : Option SubUID u₂
      extensions : Option Extensions e
      @0 len≡ : getLength len ≡ length (ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

  ---------------------------------Certificate---------------------------------------------------

  record Cert (bs : List Dig) : Set where
    constructor mkCert
    field
      @0 {l t sa sig} : List Dig
      len : Length l
      tbs : TBSCert t
      signAlg : SignAlg sa
      signature : Generic.Bitstring sig
      @0 len≡ : getLength len ≡ length (t ++ sa ++ sig)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ t ++ sa ++ sig
