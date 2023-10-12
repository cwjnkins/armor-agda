{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.TCB
  hiding (equivalent)
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Option.TCB
import      Aeres.Grammar.Sum.TCB
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.PublicKey.Alg.EC.Params.TCB where

open Aeres.Grammar.Definitions.Iso          UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Option.TCB               UInt8
open Aeres.Grammar.Seq.TCB                  UInt8
open Aeres.Grammar.Sum.TCB                  UInt8

FieldID : (@0 _ : List UInt8) → Set
FieldID xs = TLV Tag.Sequence OctetStringValue xs

RawFieldID : Raw FieldID
RawFieldID = RawTLV _ RawOctetStringValue

record EcParamsFields (@0 bs : List UInt8) : Set where
  constructor mkEcParamsFields
  field
    @0 {f c b o cf} : List UInt8
    version : Singleton (# 2 ∷ # 1 ∷ [ # 1 ])
    fieldID : FieldID f
    curve : Curve c
    base : OctetString b
    order : Int o
    cofactor : Option Int cf
    @0 bs≡  : bs ≡ Singleton.x version ++ f ++ c ++ b ++ o ++ cf

EcParamsFieldsRep : @0 List UInt8 → Set
EcParamsFieldsRep =
   &ₚ (&ₚ (&ₚ (&ₚ (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ])  FieldID) Curve) OctetString) Int) (Option Int)

private
  abstract
    @0 equiv≡₁ : ∀ {@0 bs₂ bs₃ bs₄ bs₅ bs₆} → (@0 xs : _)
               → xs ≡ (# 2 ∷ # 1 ∷ # 1 ∷ (((bs₂ ++ bs₃) ++ bs₄) ++ bs₅) ++ bs₆)
               → _≡_{A = List UInt8}
                   xs
                   (# 2 ∷ # 1 ∷ # 1 ∷ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆)
    equiv≡₁ xs xs≡ = trans xs≡ ((cong (λ x → # 2 ∷ # 1 ∷ # 1 ∷ x) (solve (++-monoid UInt8))))

    @0 equiv≡₂ : ∀ {@0 bs₂ bs₃ bs₄ bs₅ bs₆} → (@0 xs : _)
                 → xs ≡ (# 2 ∷ # 1 ∷ # 1 ∷ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆)
                 → _≡_{A = List UInt8}
                     xs
                   (# 2 ∷ # 1 ∷ # 1 ∷ (((bs₂ ++ bs₃) ++ bs₄) ++ bs₅) ++ bs₆)
    equiv≡₂ xs xs≡ = trans xs≡ (cong (λ x → # 2 ∷ # 1 ∷ # 1 ∷ x) (solve (++-monoid UInt8)))

equivalent : Equivalent EcParamsFieldsRep EcParamsFields
proj₁ equivalent{xs} (mk&ₚ{bs₂ = bs₆} (mk&ₚ{bs₂ = bs₅} (mk&ₚ{bs₂ = bs₄} (mk&ₚ{bs₂ = bs₃} (mk&ₚ{bs₂ = bs₂} refl fieldID refl) curve refl) base refl) order refl) cofactor bs≡) =
  mkEcParamsFields self fieldID curve base order cofactor (equiv≡₁{bs₂}{bs₃} xs bs≡)
proj₂ equivalent{xs} (mkEcParamsFields{f}{c}{b}{o}{cf} self fieldID curve base order cofactor bs≡) =
  mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl fieldID refl) curve refl) base refl) order refl) cofactor
    (equiv≡₂{f}{c} xs bs≡)

RawEcParamsFieldsRep : Raw EcParamsFieldsRep
RawEcParamsFieldsRep =
  Raw&ₚ (Raw&ₚ (Raw&ₚ (Raw&ₚ (Raw&ₚ RawSubSingleton RawFieldID) RawCurve) RawOctetString) RawInt) (RawOption RawInt)

RawEcParamsFields : Raw EcParamsFields
RawEcParamsFields = Iso.raw equivalent RawEcParamsFieldsRep

EcParams : @0 List UInt8 → Set
EcParams xs = TLV Tag.Sequence EcParamsFields xs

RawEcParams : Raw EcParams
RawEcParams = RawTLV _ RawEcParamsFields

data EcPkAlgParams : @0 List UInt8 → Set where
  ecparams : ∀ {@0 bs} → EcParams bs → EcPkAlgParams bs
  namedcurve : ∀ {@0 bs} → OID bs → EcPkAlgParams bs
  implicitlyCA : ∀ {@0 bs} → Null bs → EcPkAlgParams bs

EcPkAlgParamsRep : @0 List UInt8 → Set
EcPkAlgParamsRep = Sum EcParams (Sum OID Null)

equivalent : Equivalent EcPkAlgParamsRep EcPkAlgParams
proj₁ equivalent (Sum.inj₁ x) = ecparams x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = namedcurve x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ x)) = implicitlyCA x
proj₂ equivalent (ecparams x) = inj₁ x
proj₂ equivalent (namedcurve x) = inj₂ (inj₁ x)
proj₂ equivalent (implicitlyCA x) = inj₂ (inj₂ x)

