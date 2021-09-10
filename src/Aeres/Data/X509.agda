open import Aeres.Prelude

module Aeres.Data.X509 where

open import Aeres.Binary
open Base256

module Tag where
  abstract
    Null : Dig
    Null = # 5

    ObjectIdentifier : Dig
    ObjectIdentifier = # 6

    Sequence : Dig
    Sequence = # 48

    Sett : Dig
    Sett = # 49

    Version : Dig
    Version = # 160

    Integer : Dig
    Integer = # 2

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
      @0 lₕₜLen : length (lₕ ∷ lₜ) ≡ toℕ l - 128
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
          {@0 _ : True (length (lₕ ∷ lₜ) ≟ (toℕ l - 128))}
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

  instance
    SizedLength : ∀ {@0 bs} → Sized (Length bs)
    Sized.sizeOf SizedLength (short _) = 1
    Sized.sizeOf SizedLength (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen _ bs≡)) = 2 + length lₜ

  private
    lₗ : Length (# 129 ∷ [ # 201 ])
    lₗ = longₛ (# 129) (# 201) []

open Length public
  using  (Length ; getLength)
  hiding (module Length)

-- Length = Length.Length
-- getLength = Length.getLength

module Generic where

  record OIDSub (bs : List Dig) : Set where
    constructor mkOIDSub
    field
      lₚ : List Dig
      @0 lₚ≥128 : All (λ d → toℕ d ≥ 128) lₚ
      lₑ   : Dig
      @0 lₑ<128 : toℕ lₑ < 128
      @0 leastDigs : maybe (λ d → toℕ d > 128) ⊤ (head lₚ)
      @0 bs≡ : bs ≡ lₚ ∷ʳ lₑ

  instance
    SizedOIDSub : ∀ {@0 bs} → Sized (OIDSub bs)
    Sized.sizeOf SizedOIDSub (mkOIDSub lₚ lₚ≥128 lₑ l₃<128 leastDigs bs≡) =
      length (lₚ ∷ʳ lₑ)

  private
    oidsub₁ : OIDSub (# 134 ∷ [ # 72 ])
    oidsub₁ = mkOIDSub [ # 134 ] (toWitness{Q = All.all ((128 ≤?_) ∘ toℕ) _} tt) (# 72) (toWitness{Q = 72 <? 128} tt) (toWitness{Q = 134 >? 128} tt) refl

  postulate
    -- OIDField : List Dig → Set
    StringValue : List Dig → Set

  postulate
    instance
      SizedStringValue : ∀ {x} → Sized (StringValue x)

  data OIDField : List Dig → Set

  record OIDFieldₐ (bs : List Dig) : Set where
    inductive
    constructor cons
    field
      @0 {bs₁} : List Dig
      @0 {bs₂} : List Dig
      sub  : OIDSub bs₁
      rest : OIDField bs₂
      @0 bs≡ : bs ≡ bs₁ ++ bs₂

  data OIDField where
    [_]OID : ∀ {@0 bs} → OIDSub bs → OIDField bs
    cons : ∀ {@0 bs} → OIDFieldₐ bs → OIDField bs

  record OID (bs : List Dig) : Set where
    constructor mkOid
    field
      @0 {l} : List Dig
      @0 {o} : List Dig
      len : Length l
      oid : OIDField o
      @0 len≡ : getLength len ≡ length o
      @0 bs≡ : bs ≡ Tag.ObjectIdentifier ∷ l ++ o

--------------------------------------------------

  postulate
    Integer : List Dig → Set

  record Int (bs : List Dig) : Set where
    constructor mkInt
    field
      @0 {l v} : List Dig
      len : Length l
      val : Integer v
      @0 len≡ : getLength len ≡ length v
      @0 bs≡  : bs ≡ Tag.Integer ∷ l ++ v


module X509 where

  postulate
    SignParam : List Dig → Set
    Signature : List Dig → Set
    Validity : List Dig → Set
    PublicKey : List Dig → Set
    UID : List Dig → Set
    Extensions : List Dig → Set

  postulate
    instance
      SizedSignature : ∀ {sig} → Sized (Signature sig)
      -- SizedSignOID : ∀ {oid} → Sized (SignOID oid)
      SizedSignParam : ∀ {param} → Sized (SignParam param)
      SizedValidity : ∀ {x} → Sized (Validity x)
      SizedPublicKey : ∀ {x} → Sized (PublicKey x)
      SizedUid : ∀ {x} → Sized (UID x)
      SizedExtensions : ∀ {x} → Sized (Extensions x)

  record SignAlg (bs : List Dig) : Set where
    constructor mkSignAlg
    field
      @0 {l o p} : List Dig
      len : Length l
      signOID : Generic.OID o
      param   : SignParam p
      @0 len≡ : getLength len ≡ length (o ++ p)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ o ++ p

--------------------------  TBSCert  -----------------------------------------------------------------

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

  record TBSCert (bs : List Dig) : Set where
    constructor mkTBSCert
    field
      @0 {l ver ser sa i va u p u₁ u₂ e} : _
      len : Length l
      version : Version ver
      serial  : Generic.Int ser
      signAlg : SignAlg sa
      issuer  : RDName i
      validity : Validity va
      subject  : RDName u
      pk       : PublicKey p
      issuerUID : UID u₁
      subjectUID : UID u₂
      extensions : Extensions e
      @0 len≡ : getLength len ≡ length (ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e)
      @0 bs≡  : bs ≡ Tag.Sequence ∷ l ++ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

---------------------------------------------------------------------------------------------

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
