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
  -- data OIDField : List Dig → Set where
  --   oid1 : (bs : List Dig) (b : Dig)
  --          → {!!}
  --          → OIDField (bs ++ [ b ])

  postulate
    instance
      SizedOIDField : ∀ {oid} → Sized (OIDField oid)

  data OID : List Dig → Set where
    mkOID : ∀ {len} {oid} (l : Length len)
            → (o : OIDField oid)
            → LengthIs o l
            → OID (Tag.ObjectIdentifier ∷ len ++ oid)

  instance
    SizedOID : ∀ {oid} → Sized (OID oid)
    Sized.sizeOf SizedOID (mkOID l o x) = getLength l

module X509 where

  postulate
    TBSCert : List Dig → Set
    SignParam : List Dig → Set
    Signature : List Dig → Set

  data SignOID : List Dig → Set

  postulate
    instance
      SizedTBSCert : ∀ {tbs} → Sized (TBSCert tbs)
      SizedSignature : ∀ {sig} → Sized (Signature sig)
      SizedSignOID : ∀ {oid} → Sized (SignOID oid)
      SizedSignParam : ∀ {param} → Sized (SignParam param)

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

