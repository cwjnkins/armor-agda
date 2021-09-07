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

    VersionTag : Dig
    VersionTag = # 160

    Integer : Dig
    Integer = # 2

module Length where

  record Short (bs : List Dig) : Set where
    constructor mkShort
    field
      l : Dig
      @0 l<128 : toℕ l < 128
      @0 bs≡ : bs ≡ [ l ]

  record Long (bs : List Dig) : Set where
    constructor mkLong
    field
      l : Dig
      @0 l>128 : 128 < toℕ l
      lₕ : Dig
      @0 lₕ≢0 : toℕ lₕ ≢ 0
      lₜ : List Dig
      @0 lₜLen : length (lₕ ∷ lₜ) ≡ toℕ l - 128
      @0 bs≡ : bs ≡ l ∷ lₕ ∷ lₜ

  data Length : List Dig → Set where
    short : ∀ {@0 bs} → Short bs → Length bs
    long  : ∀ {@0 bs} → Long  bs → Length bs

  shortₛ : ∀ l → {@0 _ : True (toℕ l <? 128)} → Length [ l ]
  shortₛ l {l<128} = short (mkShort l (toWitness l<128) refl)

  longₛ : ∀ l lₕ lₜ → {@0 _ : True (128 <? toℕ l)} {@0 _ : False (toℕ lₕ ≟ 0)} {@0 _ : True (length (lₕ ∷ lₜ) ≟ (toℕ l - 128))}
          → Length (l ∷ lₕ ∷ lₜ)
  longₛ l lₕ lₜ {l>128} {lₕ≢0} {lₜLen} = long (mkLong l (toWitness l>128) lₕ (toWitnessFalse lₕ≢0) lₜ (toWitness lₜLen) refl)

  getLength : ∀ {@0 bs} → Length bs → ℕ
  getLength {bs} (short (mkShort l l<128 bs≡)) = toℕ l
  getLength {bs} (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen bs≡)) = go (reverse (lₕ ∷ lₜ))
    where
    go : List Dig → ℕ
    go [] = 0
    go (b ∷ bs') = toℕ b + 256 * go bs'

  instance
    SizedLength : ∀ {@0 bs} → Sized (Length bs)
    Sized.sizeOf SizedLength (short _) = 1
    Sized.sizeOf SizedLength (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen bs≡)) = 1 + length lₜ

  private
    lₗ : Length (# 129 ∷ [ # 201 ])
    lₗ = longₛ (# 129) (# 201) []

open Length using (Length ; getLength ; shortₛ ; longₛ)

module Generic where

  record OIDSub (bs : List Dig) : Set where
    constructor mkOIDSub
    field
      lₚ : List Dig
      @0 lₚ≥128 : All (λ d → toℕ d ≥ 128) lₚ
      lₑ   : Dig
      @0 l₃<128 : toℕ lₑ < 128
      @0 leastDigs : maybe (λ d → toℕ d > 128) ⊤ (head lₚ)
      @0 bs≡ : bs ≡ lₚ ∷ʳ lₑ

  instance
    SizedOIDSub : ∀ {@0 bs} → Sized (OIDSub bs)
    Sized.sizeOf SizedOIDSub (mkOIDSub lₚ lₚ≥128 lₑ l₃<128 leastDigs bs≡) =
      length (lₚ ∷ʳ lₑ)

  private
    oidsub₁ : OIDSub (# 134 ∷ [ # 72 ])
    oidsub₁ = mkOIDSub [ # 134 ] (toWitness{Q = All.all ((128 ≤?_) ∘ toℕ) _} tt) (# 72) (toWitness{Q = 72 <? 128} tt) (toWitness{Q = 134 >? 128} tt) refl

  -- data OIDSubPrefix : ℕ → List Dig → Set where
  --   []  : OIDSubPrefix 0 []
  --   consOIDSubPrefix
  --     : ∀ {n ds} → OIDSubPrefix n ds
  --       → (b : Dig) → (b>128 : True (toℕ b >? 128))
  --       → OIDSubPrefix (toℕ b - 128 + 128 * n) (ds ∷ʳ b)

--   instance
--     SizedOIDSubPrefix : ∀ {n ds} → Sized (OIDSubPrefix n ds)
--     Sized.sizeOf SizedOIDSubPrefix [] = 0
--     Sized.sizeOf SizedOIDSubPrefix (consOIDSubPrefix x b b>128) =
--       1 + Sized.sizeOf SizedOIDSubPrefix x

--   data OIDSub : ℕ → List Dig → Set where
--     mkOIDSub : ∀ {n ds} → OIDSubPrefix n ds
--                → (b : Dig) → (b<128 : True (toℕ b <? 128))
--                → OIDSub (toℕ b + 128 * n) (ds ∷ʳ b)

--   instance
--     SizedOIDSub : ∀ {n ds} → Sized (OIDSub n ds)
--     Sized.sizeOf SizedOIDSub (mkOIDSub x b b<128) = 1 + sizeOf x

--   private
--     test₁ : OIDSub 255 (# 129 ∷ [ # 127 ])
--     test₁ = mkOIDSub (consOIDSubPrefix [] (# 129) _) (# 127) _

  postulate
    OIDField : List Dig → Set
    Integer : List Dig → Set
    StringValue : List Dig → Set
  -- data OIDField : List Dig → Set where
  --   oid1 : (bs : List Dig) (b : Dig)
  --          → {!!}
  --          → OIDField (bs ++ [ b ])

  postulate
    instance
      SizedOIDField : ∀ {oid} → Sized (OIDField oid)
      SizedInteger : ∀ {x} → Sized (Integer x)
      SizedStringValue : ∀ {x} → Sized (StringValue x)

  data OID : List Dig → Set where
    mkOID : ∀ {len} {oid} (l : Length len)
            → (o : OIDField oid)
            → (getLength l ≡ length oid)
            → OID (Tag.ObjectIdentifier ∷ len ++ oid)

  instance
    SizedOID : ∀ {oid} → Sized (OID oid)
    Sized.sizeOf SizedOID (mkOID l o x) = getLength l

  data Int : List Dig → Set where
    mkInt : ∀ {len value} → (l : Length len) → (val : Integer value)
                → (len≡ : getLength l ≡ length value)
                → Int (Tag.Integer ∷ len ++ value)

  instance
    SizedInt : ∀ {x}  → Sized (Int x)
    Sized.sizeOf SizedInt (mkInt l x len≡) = 1 + sizeOf l + getLength l


module X509 where

  postulate
    SignParam : List Dig → Set
    Signature : List Dig → Set
    Validity : List Dig → Set
    PublicKey : List Dig → Set
    Uid : List Dig → Set
    Extensions : List Dig → Set

  data SignOID : List Dig → Set

  postulate
    instance
      SizedSignature : ∀ {sig} → Sized (Signature sig)
      SizedSignOID : ∀ {oid} → Sized (SignOID oid)
      SizedSignParam : ∀ {param} → Sized (SignParam param)
      SizedValidity : ∀ {x} → Sized (Validity x)
      SizedPublicKey : ∀ {x} → Sized (PublicKey x)
      SizedUid : ∀ {x} → Sized (Uid x)
      SizedExtensions : ∀ {x} → Sized (Extensions x)

  data SignOID where
    mkSignOID : ∀ {len oid} (l : Length len)
                → (o : Generic.OID oid)
                → (getLength l ≡ length oid)
                → SignOID (Tag.ObjectIdentifier ∷ len ++ oid)

  data SignAlgField : (oid param : List Dig) → Set where
    mkSignAlgField :
      ∀ {oid param} → SignOID oid → SignParam param
      → SignAlgField oid param

  instance
    SizedSignAlgField : ∀ {oid param} → Sized (SignAlgField oid param)
    Sized.sizeOf SizedSignAlgField (mkSignAlgField oid param) =
      sizeOf oid + sizeOf param

  data SignAlg : List Dig → Set where
    mkSignAlg : ∀ {len oid param} → (l : Length len)
                → (sa : SignAlgField oid param)
                → (len≡ : getLength l ≡ length (oid ++ param))
                → SignAlg (Tag.Sequence ∷ len ++ oid ++ param)

  instance
    SizedSignAlg : ∀ {sa}  → Sized (SignAlg sa)
    Sized.sizeOf SizedSignAlg (mkSignAlg l sa len≡) = 1 + sizeOf l + getLength l

--------------------------  TBSCert  -----------------------------------------------------------------
  data Version : List Dig → Set where
    mkVersion : ∀ {len vibs} → (l : Length len) → (vf : Generic.Int vibs)
                → (len≡ : getLength l ≡ length vibs)
                → Version (Tag.VersionTag ∷ len ++ vibs)

  instance
    SizedVersion : ∀ {x}  → Sized (Version x)
    Sized.sizeOf SizedVersion (mkVersion l x len≡) = 1 + sizeOf l + getLength l

  data RDNAttrbt : List Dig → Set where
    mkRDNAttrbt
      : ∀ {oid value}
        → Generic.OID oid → Generic.StringValue value
        → RDNAttrbt (oid ++ value)

  instance
    postulate
      SizedRDNAttrbt : ∀ {bs} → Sized (RDNAttrbt bs)

  data RDNSetSeq : List Dig → Set where
    mkRDNSetSeq : ∀{len attrbt} → (l : Length len) → (rdnattrbt : RDNAttrbt attrbt)
                → (len≡ : getLength l ≡ length attrbt)
                → RDNSetSeq(Tag.Sequence ∷ len ++ attrbt)

  instance
    postulate
      SizedRDNSetSeq : ∀ {x}  → Sized (RDNSetSeq x)


  data RDNSetElems : List Dig → Set where
    _∷[] : ∀ {x} →  RDNSetSeq x → RDNSetElems x
    _∷_ : ∀{x y} →  RDNSetSeq x → RDNSetElems y → RDNSetElems (x ++ y)

  instance
    postulate
      SizedRDNSetElems : ∀ {x} → Sized (RDNSetElems x)

  data RDNSet : List Dig → Set where
    mkRDNSet : ∀ {len elems} → (l : Length len) → (rdnsetelems : RDNSetElems elems)
                → (len≡ : getLength l ≡ length elems)
                → RDNSet(Tag.Sett ∷ len ++ elems)

  instance
    postulate
      SizedRDNSet : ∀ {x} → Sized (RDNSet x)

  data RDNSeqElems : List Dig → Set where
    _∷[] : ∀{x} →  RDNSet x → RDNSeqElems x
    _∷_ : ∀{x y} →  RDNSet x → RDNSeqElems y → RDNSeqElems (x ++ y)

  instance
    postulate
      SizedRDNSeqElems : ∀ {x} → Sized (RDNSeqElems x)

  data RDName : List Dig → Set where
    mkRDName : ∀ {len seqelems} → (l : Length len) → (elems : RDNSeqElems seqelems)
                → (len≡ : getLength l ≡ length seqelems)
                → RDName(Tag.Sequence ∷ len ++ seqelems)

  instance
    SizedRDName : ∀ {x}  → Sized (RDName x)
    Sized.sizeOf SizedRDName (mkRDName l x len≡) = 1 + sizeOf l + getLength l


  data TBSCertField : List Dig → Set where
    mkTBSCertField
      : ∀ {ver ser satbs iss valid sub pk issuid subuid extns}
        → Version ver → Generic.Int ser → SignAlg satbs → RDName iss → Validity valid
        → RDName sub → PublicKey pk → Uid issuid → Uid subuid → Extensions extns
        → TBSCertField (ver ++ ser ++ satbs ++ iss ++ valid ++ sub ++ pk ++ issuid ++ subuid ++ extns)

  instance
    SizedTBSCertField : ∀ {tbsf} → Sized (TBSCertField tbsf)
    Sized.sizeOf SizedTBSCertField (mkTBSCertField ver ser satbs iss valid sub pk issuid subuid extns) =
      sizeOf ver + sizeOf ser + sizeOf satbs + sizeOf iss + sizeOf valid + sizeOf sub + sizeOf pk
      + sizeOf issuid + sizeOf subuid + sizeOf extns

  data TBSCert : List Dig → Set where
    mkTBSCert : ∀ {len tbsbs} → (l : Length len) → (tbsf : TBSCertField tbsbs)
                → (len≡ : True $ length tbsbs ≟ getLength l)
                → TBSCert(Tag.Sequence ∷ len ++ tbsbs)

  instance
    SizedTBSCert : ∀ {x} → Sized (TBSCert x)
    Sized.sizeOf SizedTBSCert (mkTBSCert l x len≡) = 1 + sizeOf l + getLength l

---------------------------------------------------------------------------------------------
  data CertField : List Dig → Set where
    mkCertField
      : ∀ {tbs sa sig}
        → TBSCert tbs → SignAlg sa → Signature sig
        → CertField (tbs ++ sa ++ sig)

  instance
    SizedCertField : ∀ {@0 bs} → Sized (CertField bs)
    Sized.sizeOf SizedCertField (mkCertField tbs sa sig) =
      sizeOf tbs + sizeOf sa + sizeOf sig

  data Cert : List Dig → Set where
    mkCert : ∀ {@0 len cbs} → (l : Length len) → (cf : CertField cbs)
             → (@0 len≡ : length cbs ≡ getLength l)
             → Cert (Tag.Sequence ∷ len ++ cbs)

  instance
    SizedCert : ∀ {@0 bs} → Sized (Cert bs)
    Sized.sizeOf (SizedCert {.(Tag.Sequence ∷ len ++ cbs)}) (mkCert{len}{cbs} l cf len≡) =
      1 + sizeOf l + sizeOf cf

  private
    test₁ : ¬ Cert []
    test₁ ()
