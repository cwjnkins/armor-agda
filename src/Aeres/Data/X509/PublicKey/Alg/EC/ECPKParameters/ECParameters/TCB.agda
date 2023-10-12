{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.Curve.TCB
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

module Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.TCB where

open Aeres.Grammar.Definitions.Iso          UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Option.TCB               UInt8
open Aeres.Grammar.Seq.TCB                  UInt8
open Aeres.Grammar.Sum.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- ECParameters ::= SEQUENCE {
--    version   ECPVer,          -- version is always 1
--    fieldID   FieldID,         -- identifies the finite field over
--                               -- which the curve is defined
--    curve     Curve,           -- coefficients a and b of the
--                               -- elliptic curve
--    base      ECPoint,         -- specifies the base point P
--                               -- on the elliptic curve
--    order     INTEGER,         -- the order n of the base point
--    cofactor  INTEGER OPTIONAL -- The integer h = #E(Fq)/n
--    }
-- 
-- ECPVer ::= INTEGER {ecpVer1(1)}
-}

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

