{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.IA5String.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV as TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X690-DER.Strings.IA5String.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Data.X690-DER.Strings.IA5String.TCB.IA5StringValue
  using (size)

@0 unambiguous : Unambiguous IA5StringValue
unambiguous (mkIA5StringValue self all<128) (mkIA5StringValue self all<129) =
  subst₀ (λ x → _ ≡ mkIA5StringValue self x)
    (T-unique all<128 all<129) refl

@0 nonmalleable : NonMalleable RawIA5StringValue
nonmalleable (mkIA5StringValue self all<128) (mkIA5StringValue self all<129) refl = 
  case (‼ T-unique all<128 all<129) of λ where
    refl → ‼ refl

sizeUnique : ∀ {@0 bs} → (a₁ a₂ : IA5StringValue bs) → size a₁ ≡ size a₂
sizeUnique (mkIA5StringValue self all<128) (mkIA5StringValue self all<129) = refl

Rep : @0 List UInt8 → Set
Rep = Σₚ OctetStringValue λ _ str → Erased (True (All.all? (Fin._<? (# 128)) (↑ str)))

equiv : Equivalent Rep IA5StringValue
proj₁ equiv (mk×ₚ fstₚ₁ (─ sndₚ₁)) = mkIA5StringValue fstₚ₁ sndₚ₁
proj₂ equiv (mkIA5StringValue str all<128) = mk×ₚ str (─ all<128)

iso   : Iso Rep IA5StringValue
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk×ₚ fstₚ₁ sndₚ₁) = refl
proj₂ (proj₂ iso) (mkIA5StringValue str all<128) = refl

instance
  IA5StringEq : Eq (Exists─ _ IA5StringValue)
  IA5StringEq =
    Iso.isoEq iso
      (Parallel.eqΣₚ it
        λ a →
          record
            { _≟_ = λ where
              (─ x) (─ y) → yes (cong ─_ (‼ T-unique x y))
            })

  IA5StringEq≋ : Eq≋ IA5StringValue
  IA5StringEq≋ = Eq⇒Eq≋ it

@0 nonmalleableIA5String : NonMalleable RawIA5String
nonmalleableIA5String = TLV.nonmalleable nonmalleable
