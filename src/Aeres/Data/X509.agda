open import Aeres.Prelude

module Aeres.Data.X509 where

open import Aeres.Binary
open Base256

module Tag where
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


data Length : List Dig → Set where
  short : (l : Dig) → (l<128 : True (toℕ l <? 128))
          → Length [ l ]
  long  : (lₕ : Dig) → (l>128 : True (128 <? toℕ lₕ))
          → (lₜ : Vec Dig (toℕ lₕ - 128))
          → Length (lₕ ∷ Vec.toList lₜ)
  -- TODO: ensure least number of bits used (no leading zeros)

getLength : ∀ {ds} → Length ds → ℕ
getLength {.(l ∷ [])} (short l l<128) = toℕ l
getLength {.(lₕ ∷ Vec.toList lₜ)} (long lₕ l>128 lₜ) = go (Vec.reverse lₜ)
  where
  go : ∀ {n} → Vec Dig n → ℕ
  go [] = 0
  go (x ∷ ds) = toℕ x + 256 * go ds

instance
  SizedLength : ∀ {len} → Sized (Length len)
  Sized.sizeOf SizedLength (short l l<128) = 1
  Sized.sizeOf SizedLength (long lₕ l>128 lₜ) = 1 + (toℕ lₕ - 128)

LengthIs : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Sized A ⦄ {len} → (a : A) (l : Length len) → Set
LengthIs a l = True (sizeOf a ≟ getLength l)

private
  module LengthTest where
    lₛ : Length [ # 38 ]
    lₛ = short (# 38) _

    lₗ : Length (# 129 ∷ [ # 201 ])
    lₗ = long (# 129) _ Vec.[ # 201 ]

    test₁ : getLength lₛ ≡ 38
    test₁ = refl

    test₂ : getLength lₗ ≡ 201
    test₂ = refl

module Generic where

  data OIDSubPrefix : ℕ → List Dig → Set where
    []  : OIDSubPrefix 0 []
    consOIDSubPrefix
      : ∀ {n ds} → OIDSubPrefix n ds
        → (b : Dig) → (b>128 : True (toℕ b >? 128))
        → OIDSubPrefix (toℕ b - 128 + 128 * n) (ds ∷ʳ b)

  instance
    SizedOIDSubPrefix : ∀ {n ds} → Sized (OIDSubPrefix n ds)
    Sized.sizeOf SizedOIDSubPrefix [] = 0
    Sized.sizeOf SizedOIDSubPrefix (consOIDSubPrefix x b b>128) =
      1 + Sized.sizeOf SizedOIDSubPrefix x

  data OIDSub : ℕ → List Dig → Set where
    mkOIDSub : ∀ {n ds} → OIDSubPrefix n ds
               → (b : Dig) → (b<128 : True (toℕ b <? 128))
               → OIDSub (toℕ b + 128 * n) (ds ∷ʳ b)

  instance
    SizedOIDSub : ∀ {n ds} → Sized (OIDSub n ds)
    Sized.sizeOf SizedOIDSub (mkOIDSub x b b<128) = 1 + sizeOf x

  private
    test₁ : OIDSub 255 (# 129 ∷ [ # 127 ])
    test₁ = mkOIDSub (consOIDSubPrefix [] (# 129) _) (# 127) _

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
            → LengthIs o l
            → OID (Tag.ObjectIdentifier ∷ len ++ oid)

  instance
    SizedOID : ∀ {oid} → Sized (OID oid)
    Sized.sizeOf SizedOID (mkOID l o x) = getLength l

  data Int : List Dig → Set where
    mkInt : ∀ {len value} → (l : Length len) → (val : Integer value)
                → (len≡ : LengthIs val l)
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
                → LengthIs o l
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
                → (len≡ : LengthIs sa l)
                → SignAlg (Tag.Sequence ∷ len ++ oid ++ param)

  instance
    SizedSignAlg : ∀ {sa}  → Sized (SignAlg sa)
    Sized.sizeOf SizedSignAlg (mkSignAlg l sa len≡) = 1 + sizeOf l + getLength l

--------------------------  TBSCert  -----------------------------------------------------------------
  data Version : List Dig → Set where
    mkVersion : ∀ {len vibs} → (l : Length len) → (vf : Generic.Int vibs)
                → (len≡ : LengthIs vf l)
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
                → (len≡ : LengthIs rdnattrbt l)
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
                → (len≡ : LengthIs rdnsetelems l)
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
                → (len≡ : LengthIs elems l)
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
    SizedCertField : ∀ {bs} → Sized (CertField bs)
    Sized.sizeOf SizedCertField (mkCertField tbs sa sig) =
      sizeOf tbs + sizeOf sa + sizeOf sig

  data Cert : List Dig → Set where
    mkCert : ∀ {len cbs} → (l : Length len) → (cf : CertField cbs)
             → (len≡ : LengthIs cf l)
             → Cert (Tag.Sequence ∷ len ++ cbs)

  private
    test₁ : ¬ Cert []
    test₁ ()

