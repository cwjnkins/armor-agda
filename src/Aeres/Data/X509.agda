{-# OPTIONS --subtyping --inversion-max-depth=1000 #-}

open import Aeres.Prelude

module Aeres.Data.X509 where

open import Aeres.Binary
open Base256
open import Aeres.Grammar.Definitions Dig

-------------------------------------------TAGS---------------------------------------------
module Tag where
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

  record Short (@0 bs : List Dig) : Set where
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

  record Long (@0 bs : List Dig) : Set where
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

  data Length : (@0 _ : List Dig) → Set where
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

  -- TODO: extensions encoded as octet strings need to be tupled together with proofs
  -- they can be parsed into supported structures
  OctetstringValue :  (@0 _ : List Dig) → Set
  OctetstringValue =  Singleton

  Octetstring : (@0 _ : List Dig) → Set
  Octetstring xs = TLV Tag.Octetstring OctetstringValue xs

  --Integers----------------------------------------

  record IntegerValue (@0 bs : List Dig) : Set where
    constructor mkIntegerValue
    field
      val : ℤ
      @0 bs≡ : twosComplement bs ≡ val

  Int : (@0 _ : List Dig) → Set
  Int xs = TLV Tag.Integer IntegerValue xs

  --Sequences (of one type)-------------------------
  data SeqElems (A : List Dig → Set) : (@0 _ : List Dig) → Set

  record SeqElemsₐ (A : List Dig → Set) (@0 bs : List Dig) : Set where
    inductive
    constructor mkSeqElems
    field
      @0 {bs₁ bs₂} : List Dig
      h : A bs₁
      t : SeqElems A bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data SeqElems A where
    _∷[] : ∀ {@0 xs} → A xs → SeqElems A xs
    cons : ∀ {@0 xs} → SeqElemsₐ A xs → SeqElems A xs

  Seq : (A : List Dig → Set) → (@0 _ : List Dig) → Set
  Seq A = TLV Tag.Sequence (SeqElems A)

  --Integer sequences-------------------------------

  IntegerSeq : (@0 _ : List Dig) → Set
  IntegerSeq xs = TLV Tag.Sequence (SeqElems Int) xs

  BitstringUnusedBits : Dig → List Dig → Set
  BitstringUnusedBits bₕ [] = bₕ ≡ # 0
  BitstringUnusedBits bₕ (_ ∷ _) = ⊤

  record BitstringValue (@0 bs : List Dig) : Set where
    constructor mkBitstringValue
    field
      bₕ : Dig
      @0 bₕ<8 : toℕ bₕ < 8
      bₜ : List Dig         -- TODO : change to List bool and handle padding properly
      @0 unusedBits : BitstringUnusedBits bₕ bₜ
      @0 bs≡ : bs ≡ bₕ ∷ bₜ

  Bitstring : (@0 _ : List Dig) → Set
  Bitstring xs = TLV Tag.Bitstring BitstringValue xs

  OIDLeastDigs : List Dig → Set
  OIDLeastDigs = maybe (Fin._> # 128) ⊤ ∘ head

  oidLeastDigs? : ∀ bs → Dec (OIDLeastDigs bs)
  oidLeastDigs? [] = yes tt
  oidLeastDigs? (x ∷ bs) = (# 128) Fin.<? x

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


  -- --private
  -- --  oidsub₁ : OIDSub (# 134 ∷ [ # 72 ])
  -- --  oidsub₁ = mkOIDSub [ # 134 ] (toWitness{Q = All.all ((128 ≤?_) ∘ toℕ) _} tt) (# 72) (toWitness{Q = 72 <? 128} tt) (toWitness{Q = 134 >? 128} tt) refl

  OID : (@0 _ : List Dig) → Set
  OID = TLV Tag.ObjectIdentifier (SeqElems OIDSub)

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

  record MonthDayHourMinSecFields (@0 bs : List Dig) : Set where
    constructor mkMDHMSFields
    field
      @0 {mo₁ mo₂ d₁ d₂ h₁ h₂ mi₁ mi₂ s₁ s₂} : Dig

      mon : Singleton (asciiNum (mo₁ ∷ [ mo₂ ]))
      @0 monRange  :   mo₁ ≡ # 0 × InRange '0' '9' mo₂
                     ⊎ mo₁ ≡ # 1 × InRange '0' '2' mo₂

      -- TODO: where do we check valid dom? (Feb, leap year, etc)
      day : Singleton (asciiNum (d₁ ∷ [ d₂ ]))
      @0 dayRange  :   InRange '0' '2' d₁ × InRange '0' '9' d₂
                     ⊎ toℕ d₁ ≡ toℕ '3' × InRange '0' '1' d₂

      hour : Singleton (asciiNum (h₁ ∷ [ h₂ ]))
      @0 hourRange :   InRange '0' '1' h₁ × InRange '0' '9' h₂
                     ⊎ toℕ h₁ ≡ toℕ '2' × InRange '0' '3' h₂

      min : Singleton (asciiNum (mi₁ ∷ [ mi₂ ]))
      @0 minRange : InRange '0' '5' mi₁ × InRange '0' '9' mi₂

      sec : Singleton (asciiNum (s₁ ∷ [ s₂ ]))
      @0 secRange : InRange '0' '5' s₁ × InRange '0' '9' s₂

      @0 bs≡ : bs ≡ mo₁ ∷ mo₂ ∷ d₁ ∷ d₂ ∷ h₁ ∷ h₂ ∷ mi₁ ∷ mi₂ ∷ s₁ ∷ [ s₂ ]

  record UtcTimeFields (@0 bs : List Dig) : Set where
    constructor mkUtcTimeFields
    field
      @0 {y1 y2 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z} : Dig

      year : Singleton (asciiNum (y1 ∷ [ y2 ]))
      @0 yearRange : All (InRange '0' '9') (y1 ∷ [ y2 ])

      mmddhhmmss : MonthDayHourMinSecFields (mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ [ s2 ])

      @0 term : z ≡ # toℕ 'Z'
      @0 bs≡  : bs ≡ y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ [ z ]

  UtcTime : (@0 _ : List Dig) → Set
  UtcTime xs = TLV Tag.Utctime UtcTimeFields xs

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
  GenTime = TLV Tag.Gentime GenTimeFields

  -- TODO: semantic checks
  -- CAs conforming to this profile MUST always encode certificate validity
  -- dates through the year 2049 as UTCTime; certificate validity dates in 2050
  -- or later MUST be encoded as GeneralizedTime. Conforming applications MUST
  -- be able to process validity dates that are encoded in either UTCTime or
  -- GeneralizedTime.

  data Time : List Dig → Set where
    utctm : ∀ {@0 bs} → UtcTime bs → Time bs
    gentm  : ∀ {@0 bs} → GenTime  bs → Time bs

------------------------------X.509-----------------------------------------------------------

module X509 where

  -- TODO: double-check with Joy
  record IA5StringValue (@0 bs : List Dig) : Set where
    constructor mkIA5StringValue
    field
      str : Generic.OctetstringValue bs
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

  -- RSA explicit null param case covered here
  -- TODO : add cases for other RSA signature algorithms
  -- TODO: The current definition fails the "Unambiguous" property
  data SignParam : List Dig →  List Dig → Set where
    md5rsap    : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Md5Rsa)    → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha1rsap   : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha1Rsa)   → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    rsapssp    : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.RsaPss)    → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha256rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha256Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha384rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha384Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha512rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha512Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    sha224rsap : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ SOID.Sha224Rsa) → (@0 _ : bs2 ≡ # 5 ∷ [ # 0 ]) → SignParam bs1 bs2
    _ : ∀ {@0 bs1 bs2} → Generic.OctetstringValue bs2 → SignParam bs1 bs2

  record SignAlgFields (bs : List Dig) : Set where
    constructor mkSignAlgFields
    field
      @0 {o p} : List Dig
      signOID : Generic.OID o
      param : Option Generic.Octetstring p
--      wparam : Option (SignParam o) p -- RSA implicit null param case covered here
      @0 bs≡  : bs ≡ o ++ p

  SignAlg : (@0 _ : List Dig) → Set
  SignAlg xs = Generic.TLV Tag.Sequence SignAlgFields xs

 --------------- RDNSeq -------------------------------------

  TeletexString : (@0 _ : List Dig) → Set
  TeletexString xs = Generic.TLV Tag.TeletexString  Generic.OctetstringValue xs

  PrintableString : (@0 _ : List Dig) → Set
  PrintableString xs = Generic.TLV Tag.PrintableString  Generic.OctetstringValue xs

  UniversalString : (@0 _ : List Dig) → Set
  UniversalString xs = Generic.TLV Tag.UniversalString  Generic.OctetstringValue xs

  UTF8String : (@0 _ : List Dig) → Set
  UTF8String xs = Generic.TLV Tag.UTF8String  Generic.OctetstringValue xs

  BMPString : (@0 _ : List Dig) → Set
  BMPString xs = Generic.TLV Tag.BMPString  Generic.OctetstringValue xs

  IA5String : (@0 _ : List Dig) → Set
  IA5String xs = Generic.TLV Tag.IA5String  IA5StringValue xs

  VisibleString : (@0 _ : List Dig) → Set
  VisibleString xs = Generic.TLV Tag.VisibleString  Generic.OctetstringValue xs

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

  -- TODO: these fields can come in any order!
  record RDNATVFields (@0 bs : List Dig) : Set where
    constructor mkRDNATVFields
    field
      @0 {o v} : List Dig
      oid : Generic.OID o
      val : DirectoryString v
      @0 bs≡  : bs ≡ o ++ v

  RDNATV : (@0 _ : List Dig) → Set
  RDNATV xs = Generic.TLV Tag.Sequence RDNATVFields xs

  RDN : (@0 _ : List Dig) → Set
  RDN xs = Generic.TLV Tag.Sett (Generic.SeqElems RDNATV) xs

  RDNSeq : (@0 _ : List Dig) → Set
  RDNSeq = Generic.Seq RDN

----------------------- Generalnames --------------------

  --- we do not support OtherName since very rarely used
  OtherName : (@0 _ : List Dig) → Set
  OtherName xs = Generic.TLV Tag.A0 Generic.OctetstringValue xs --abstracted

  RfcName : (@0 _ : List Dig) → Set
  RfcName xs = Generic.TLV Tag.EightyOne IA5StringValue xs

  DnsName : (@0 _ : List Dig) → Set
  DnsName xs = Generic.TLV Tag.EightyTwo IA5StringValue xs

  --- we do not support X400Address since very rarely used
  X400Address : (@0 _ : List Dig) → Set
  X400Address xs = Generic.TLV Tag.A3 Generic.OctetstringValue xs --abstracted

  DirName : (@0 _ : List Dig) → Set
  DirName xs = Generic.TLV Tag.A4 (Generic.SeqElems RDN) xs

  --- we do not support EdipartyName since very rarely used
  EdipartyName : (@0 _ : List Dig) → Set
  EdipartyName xs = Generic.TLV Tag.A5 Generic.OctetstringValue xs --abstracted

  URI : (@0 _ : List Dig) → Set
  URI xs = Generic.TLV Tag.EightySix IA5StringValue xs

  IpAddress : (@0 _ : List Dig) → Set
  IpAddress xs = Generic.TLV Tag.EightySeven Generic.OctetstringValue xs

  RegID : (@0 _ : List Dig) → Set
  RegID xs = Generic.TLV Tag.EightyEight (Generic.SeqElems Generic.OIDSub) xs

  data GeneralName : List Dig → Set where
    oname : ∀ {@0 bs} → OtherName bs → GeneralName bs
    rfcname : ∀ {@0 bs} → RfcName bs → GeneralName bs
    dnsname : ∀ {@0 bs} → DnsName bs → GeneralName bs
    x400add : ∀ {@0 bs} → X400Address bs → GeneralName bs
    dirname : ∀ {@0 bs} → DirName bs → GeneralName bs
    ediname : ∀ {@0 bs} → EdipartyName bs → GeneralName bs
    uri : ∀ {@0 bs} → URI bs → GeneralName bs
    ipadd : ∀ {@0 bs} → IpAddress bs → GeneralName bs
    rid : ∀ {@0 bs} → RegID bs → GeneralName bs

  GeneralNamesElems = Generic.SeqElems GeneralName
  GeneralNames = Generic.TLV Tag.Sequence GeneralNamesElems

  --------------------------TBSCert-----------------------------------------------------------------

  Version : (@0 _ : List Dig) → Set
  Version xs = Generic.TLV Tag.A0 Generic.Int xs

  IssUID : (@0 _ : List Dig) → Set
  IssUID xs = Generic.TLV Tag.EightyOne Generic.BitstringValue xs

  SubUID : (@0 _ : List Dig) → Set
  SubUID xs = Generic.TLV Tag.EightyTwo Generic.BitstringValue xs

--------------------------------------------------------- Validity --------------------------------
  record ValidityFields (@0 bs : List Dig) : Set where
    constructor mkValidityFields
    field
      @0 {nb na} : List Dig
      start : Generic.Time nb
      end : Generic.Time na
      @0 bs≡  : bs ≡ nb ++ na

  Validity : (@0 _ : List Dig) → Set
  Validity xs = Generic.TLV Tag.Sequence ValidityFields xs

  record PublicKeyFields (@0 bs : List Dig) : Set where
    constructor mkPublicKeyFields
    field
      @0 {alg pk} : List Dig
      signalg : SignAlg alg
      pubkey : Generic.Bitstring pk
      @0 bs≡  : bs ≡ alg ++ pk

  PublicKey : (@0 _ : List Dig) → Set
  PublicKey xs = Generic.TLV Tag.Sequence PublicKeyFields xs

-----------------------------------------Extensions------------------------------------------
 ----------------------- aki extension -------------------

  AKIKeyId : (@0 _ : List Dig) → Set
  AKIKeyId xs = Generic.TLV Tag.Eighty Generic.OctetstringValue xs

  AKIAuthCertIssuer : (@0 _ : List Dig) → Set
  AKIAuthCertIssuer xs = Generic.TLV Tag.A1 GeneralNamesElems xs

  AKIAuthCertSN : (@0 _ : List Dig) → Set
  AKIAuthCertSN xs = Generic.TLV Tag.EightyTwo  Generic.IntegerValue xs

  record AKIFieldsSeqFields (@0 bs : List Dig) : Set where
    constructor mkAKIFieldsSeqFields
    field
      @0 {akid ci csn} : List Dig
      akeyid : Option AKIKeyId akid
      authcertiss : Option AKIAuthCertIssuer ci
      authcertsn : Option AKIAuthCertSN csn
      @0 bs≡  : bs ≡ akid ++ ci ++ csn

  AKIFieldsSeq : (@0 _ : List Dig) → Set
  AKIFieldsSeq xs = Generic.TLV Tag.Sequence  AKIFieldsSeqFields xs

  AKIFields : (@0 _ : List Dig) → Set
  AKIFields xs = Generic.TLV Tag.Octetstring  AKIFieldsSeq xs
------------------------------------------------------------------------------------------

  SKIFields : (@0 _ : List Dig) → Set
  SKIFields xs = Generic.TLV Tag.Octetstring  Generic.Octetstring xs

  KUFields : (@0 _ : List Dig) → Set
  KUFields xs = Generic.TLV Tag.Octetstring  Generic.Bitstring xs

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

  EKUFieldsSeq : (@0 _ : List Dig) → Set
  EKUFieldsSeq xs = Generic.TLV Tag.Sequence  EkuSeqElems xs

  EKUFields : (@0 _ : List Dig) → Set
  EKUFields xs = Generic.TLV Tag.Octetstring  EKUFieldsSeq xs

-------------------------------------------------------------------------------

  record BCFieldsSeqFields (@0 bs : List Dig) : Set where
    constructor mkBCFieldsSeqFields
    field
      @0 {ca pl} : List Dig
      bcca : Option Generic.Boool ca
      bcpathlen : Option Generic.Int pl
      @0 bs≡  : bs ≡ ca ++ pl

  BCFieldsSeq : (@0 _ : List Dig) → Set
  BCFieldsSeq xs = Generic.TLV Tag.Sequence  BCFieldsSeqFields xs

  BCFields : (@0 _ : List Dig) → Set
  BCFields xs = Generic.TLV Tag.Octetstring  BCFieldsSeq xs

-------------------------- ian/san alternative names extensions ------------------
  IANFieldsSeq : (@0 _ : List Dig) → Set
  IANFieldsSeq = GeneralNames -- Generic.TLV Tag.Sequence GeneralNamesElems

  IANFields : (@0 _ : List Dig) → Set
  IANFields xs = Generic.TLV Tag.Octetstring IANFieldsSeq xs

  SANFieldsSeq : (@0 _ : List Dig) → Set
  SANFieldsSeq = GeneralNames -- Generic.TLV Tag.Sequence GeneralNamesElems

  SANFields : (@0 _ : List Dig) → Set
  SANFields xs = Generic.TLV Tag.Octetstring SANFieldsSeq xs

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
      organiztion : DisplayText org
      noticenums : Generic.IntegerSeq nn
      @0 bs≡  : bs ≡ org ++ nn

  NoticeReference : (@0 _ : List Dig) → Set
  NoticeReference xs = Generic.TLV Tag.Sequence NoticeReferenceFields xs

  record UserNoticeFields (@0 bs : List Dig) : Set where
    constructor mkUserNoticeFields
    field
      @0 {nr et} : List Dig
      noticeRef : Option NoticeReference nr
      expText : Option DisplayText et
      @0 bs≡  : bs ≡ nr ++ et

  UserNotice : (@0 _ : List Dig) → Set
  UserNotice xs = Generic.TLV Tag.Sequence UserNoticeFields xs

  data Qualifier : List Dig →  List Dig → Set where
    cpsuri : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ PQOID.CPSURI) → IA5String bs2 → Qualifier bs1 bs2
    unotice : ∀ {@0 bs1 bs2} → (@0 _ : bs1 ≡ PQOID.USERNOTICE) → UserNotice bs2 → Qualifier bs1 bs2

  data PolicyQualifierId : List Dig → Set where
    cpsuriid : ∀ {@0 bs} → (@0 _ : bs ≡ PQOID.CPSURI) → PolicyQualifierId bs
    unoticeid : ∀ {@0 bs} → (@0 _ : bs ≡ PQOID.USERNOTICE) → PolicyQualifierId bs

  record PolicyQualifierInfoFields (@0 bs : List Dig) : Set where
    constructor mkPolicyQualifierInfoFields
    field
      @0 {pqlid ql} : List Dig
      cpqlid : PolicyQualifierId pqlid
      cql : Qualifier pqlid ql
      @0 bs≡  : bs ≡ pqlid ++ ql

  PolicyQualifierInfo : (@0 _ : List Dig) → Set
  PolicyQualifierInfo xs = Generic.TLV Tag.Sequence PolicyQualifierInfoFields xs

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

  PolicyQualifiersSeq : (@0 _ : List Dig) → Set
  PolicyQualifiersSeq xs = Generic.TLV Tag.Sequence PolicyQualifiersSeqElems xs

  record PolicyInformationFields (bs : List Dig) : Set where
    constructor mkPolicyInformationFields
    field
      @0 {pid pqls} : List Dig
      cpid : Generic.OID pid
      cpqls : Option PolicyQualifiersSeq pqls
      @0 bs≡  : bs ≡ pid ++ pqls

  PolicyInformation : (@0 _ : List Dig) → Set
  PolicyInformation xs = Generic.TLV Tag.Sequence PolicyInformationFields xs

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

  CertPolFieldsSeq : (@0 _ : List Dig) → Set
  CertPolFieldsSeq xs = Generic.TLV Tag.Sequence  CertPolSeqElems xs

  CertPolFields : (@0 _ : List Dig) → Set
  CertPolFields xs = Generic.TLV Tag.Octetstring  CertPolFieldsSeq xs

----------------------------- crl dist point extension --------------------------------

  CrlIssuer : (@0 _ : List Dig) → Set
  CrlIssuer xs = Generic.TLV Tag.A2 GeneralNamesElems xs

  ReasonFlags : (@0 _ : List Dig) → Set
  ReasonFlags xs = Generic.TLV Tag.EightyOne Generic.BitstringValue xs

  FullName : (@0 _ : List Dig) → Set
  FullName xs = Generic.TLV Tag.A0 GeneralNamesElems xs

  NameRTCrlIssuer : (@0 _ : List Dig) → Set
  NameRTCrlIssuer xs = Generic.TLV Tag.A1 RDNSeq xs

  data DistPointNameChoice : (@0 _ : List Dig) → Set where
    fullname : ∀ {@0 bs} → FullName bs → DistPointNameChoice bs
    nameRTCrlissr : ∀ {@0 bs} → NameRTCrlIssuer bs → DistPointNameChoice bs

  DistPointName : (@0 _ : List Dig) → Set
  DistPointName xs = Generic.TLV Tag.A0  DistPointNameChoice xs

  record DistPointFields (bs : List Dig) : Set where
    constructor mkDistPointFields
    field
      @0 {dp rsn issr} : List Dig
      crldp : Option DistPointName dp
      crldprsn : Option ReasonFlags rsn
      crlissr : Option CrlIssuer issr
      @0 bs≡  : bs ≡ dp ++ rsn ++ issr

  DistPoint : (@0 _ : List Dig) → Set
  DistPoint xs = Generic.TLV Tag.Sequence DistPointFields xs

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

  CRLDistFieldsSeq : (@0 _ : List Dig) → Set
  CRLDistFieldsSeq xs = Generic.TLV Tag.Sequence  CRLSeqElems xs

  CRLDistFields : (@0 _ : List Dig) → Set
  CRLDistFields xs = Generic.TLV Tag.Octetstring  CRLDistFieldsSeq xs

----------------------------------------- Authority Info access -----------------
  module ACMOID where
    CAISSUERS : List Dig
    CAISSUERS = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 2 ]

    OCSP : List Dig
    OCSP = # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 1 ]

  data AccessMethod : List Dig → Set where
    caissid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.CAISSUERS) → AccessMethod bs
    ocspid : ∀ {@0 bs} → (@0 _ : bs ≡ ACMOID.OCSP) → AccessMethod bs

  record AccessDescFields (bs : List Dig) : Set where
    constructor mkAccessDescFields
    field
      @0 {acm acl} : List Dig
      acmethod : AccessMethod acm
      aclocation : GeneralName acl
      @0 bs≡  : bs ≡ acm ++ acl

  AccessDesc : (@0 _ : List Dig) → Set
  AccessDesc xs = Generic.TLV Tag.Sequence  AccessDescFields xs

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
 
  AIAFieldsSeq : (@0 _ : List Dig) → Set
  AIAFieldsSeq xs = Generic.TLV Tag.Sequence  AIASeqElems xs

  AIAFields : (@0 _ : List Dig) → Set
  AIAFields xs = Generic.TLV Tag.Octetstring  AIAFieldsSeq xs

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
    _ : ∀ {@0 bs1 bs2} → Generic.Octetstring bs2 → SelectExtn bs1 bs2

  record ExtensionFields (bs : List Dig) : Set where
    constructor mkExtensionFields
    field
      @0 {oex cex ocex} : List Dig
      oidextn : Generic.OID oex
      critical : Option Generic.Boool cex
      octetextn :  SelectExtn oex ocex
      @0 bs≡  : bs ≡ oex ++ cex ++ ocex

  Extension : (@0 _ : List Dig) → Set
  Extension xs = Generic.TLV Tag.Sequence ExtensionFields xs

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

  ExtensionsSeq : (@0 _ : List Dig) → Set
  ExtensionsSeq xs = Generic.TLV Tag.Sequence  ExtensionsSeqElems xs

  Extensions : (@0 _ : List Dig) → Set
  Extensions xs = Generic.TLV Tag.A3  ExtensionsSeq xs

-----------------------------------------------------------------------------------------------

  record TBSCertFields (bs : List Dig) : Set where
    constructor mkTBSCertFields
    field
      @0 {ver ser sa i va u p u₁ u₂ e} : List Dig
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
      @0 bs≡  : bs ≡ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

  TBSCert : (@0 _ : List Dig) → Set
  TBSCert xs = Generic.TLV Tag.Sequence TBSCertFields xs

  ---------------------------------Certificate---------------------------------------------------

  record CertFields (bs : List Dig) : Set where
    constructor mkCertFields
    field
      @0 {t sa sig} : List Dig
      tbs : TBSCert t
      signAlg : SignAlg sa
      signature : Generic.Bitstring sig
      @0 bs≡  : bs ≡ t ++ sa ++ sig

  Cert : (@0 _ : List Dig) → Set
  Cert xs = Generic.TLV Tag.Sequence  CertFields xs
