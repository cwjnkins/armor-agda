{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.PublicKey.Alg.EC.Params.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option  UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning

module Fields where
  Rep = &ₚ (&ₚ (&ₚ (&ₚ (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ])  FieldID) Curve) OctetString) Int) (Option Int)

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

  equivalent : Equivalent Rep EcParamsFields
  proj₁ equivalent{xs} (mk&ₚ{bs₂ = bs₆} (mk&ₚ{bs₂ = bs₅} (mk&ₚ{bs₂ = bs₄} (mk&ₚ{bs₂ = bs₃} (mk&ₚ{bs₂ = bs₂} refl fieldID refl) curve refl) base refl) order refl) cofactor bs≡) =
    mkEcParamsFields self fieldID curve base order cofactor (equiv≡₁{bs₂}{bs₃} xs bs≡)
  proj₂ equivalent{xs} (mkEcParamsFields{f}{c}{b}{o}{cf} self fieldID curve base order cofactor bs≡) =
    mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl fieldID refl) curve refl) base refl) order refl) cofactor
      (equiv≡₂{f}{c} xs bs≡)
  
  iso : Iso Rep EcParamsFields
  proj₁ iso = equivalent
  proj₁ (proj₂ iso){xs} a@(mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl fieldID refl) curve refl) base refl) order refl) cofactor refl) = ‼
    subst₀ (λ e → mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl fieldID refl) curve refl) base refl) order refl) cofactor e ≡ a) (≡-unique refl _) refl
  proj₂ (proj₂ iso) a@(mkEcParamsFields self fieldID curve base order cofactor refl) =
    subst₀ (λ e → mkEcParamsFields self fieldID curve base order cofactor e ≡ a)
      (‼ (≡-unique refl _))
      refl

  @0 unambiguous : Unambiguous EcParamsFields
  unambiguous = Iso.unambiguous iso
    (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (λ where refl refl → refl) (λ where _ refl refl → refl)
      (TLV.unambiguous OctetString.unambiguous))
        (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting)
      (TLV.unambiguous Curve.unambiguous))
        (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting)
      (TLV.unambiguous OctetString.unambiguous))
        (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting)
      (TLV.unambiguous λ {xs} → Int.unambiguous{xs}))
        (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting)
      (Unambiguous.option₁ (TLV.unambiguous λ {xs} → Int.unambiguous{xs}) TLV.nonempty))

Rep : @0 List UInt8 → Set
Rep =  Sum EcParams (Sum OID Null)

equivalent : Equivalent Rep EcPkAlgParams
proj₁ equivalent (Sum.inj₁ x) = ecparams x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = namedcurve x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ x)) = implicitlyCA x
proj₂ equivalent (ecparams x) = inj₁ x
proj₂ equivalent (namedcurve x) = inj₂ (inj₁ x)
proj₂ equivalent (implicitlyCA x) = inj₂ (inj₂ x)

iso : Iso Rep EcPkAlgParams
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ x)) = refl
proj₂ (proj₂ iso) (ecparams x) = refl
proj₂ (proj₂ iso) (namedcurve x) = refl
proj₂ (proj₂ iso) (implicitlyCA x) = refl

@0 len≥1 : ∀ {@0 bs} → EcPkAlgParams bs → length bs ≥ 1
len≥1 (ecparams (mkTLV len val len≡ refl))   = s≤s z≤n
len≥1 (namedcurve (mkTLV len val len≡ refl)) = s≤s z≤n
len≥1 (implicitlyCA (mkTLV len refl len≡ refl)) = s≤s z≤n

@0 nonnesting : NonNesting EcPkAlgParams
nonnesting =
  equivalent-nonnesting equivalent
    (nonnestingSum
      TLV.nonnesting 
      (nonnestingSum TLV.nonnesting TLV.nonnesting
        (TLV.noconfusion (λ ())))
      (NoConfusion.sumₚ{A = EcParams}
        (TLV.noconfusion (λ ()))
        (TLV.noconfusion λ ())))

@0 unambiguous : Unambiguous EcPkAlgParams
unambiguous =
  Iso.unambiguous iso
    (unambiguousSum
      (TLV.unambiguous Fields.unambiguous)
      (unambiguousSum
        OID.unambiguous (TLV.unambiguous (λ where refl refl → refl))
        (TLV.noconfusion λ ()))
      (NoConfusion.sumₚ{A = EcParams}
        (TLV.noconfusion λ ()) (TLV.noconfusion λ ())))
