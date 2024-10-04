open import Armor.Binary
open import Armor.Data.X509.CRL.Version.TCB
import      Armor.Data.X690-DER.Int.Properties as Int
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.Properties as Parallel'
open import Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.Version.Properties where

open Armor.Grammar.Definitions UInt8
private
  module Parallel = Parallel' UInt8

instance
  eqDecodedVersion : Eq DecodedVersion
  Eq._≟_ eqDecodedVersion = λ where
   v1 v1 → yes refl
   v1 v2 → no λ ()
   v2 v1 → no λ ()
   v2 v2 → yes refl

@0 nosubstrings : NoSubstrings Version
nosubstrings = Parallel.nosubstrings₁ TLV.nosubstrings

@0 unambiguous : Unambiguous Version
unambiguous = Parallel.unambiguous Int.unambiguous
  λ v → erased-unique (∈-unique (toWitness{Q = List.unique? _≟_ supportedVersions} tt))

@0 nonmalleable : NonMalleable RawVersion
nonmalleable a₁@(mk×ₚ v₁ (─ v₁∈)) a₂@(mk×ₚ v₂ (─ v₂∈)) =
  case (uneraseDec v₁∈ (_ ∈? _) ,′ uneraseDec v₂∈ (_ ∈? _))
  ret (λ where (z₁ , z₂) → toRawVersion v₁ z₁ ≡ toRawVersion v₂ z₂ → _≡_{A = Exists─ _ Version}(─ _ , a₁) (─ _ , a₂))
  of λ where
  (here v₁≡ , here v₂≡) eq →
      case ‼ Int.nonmalleable v₁ v₂ (trans v₁≡ (sym v₂≡)) ret (const _) of λ where
        refl → case ‼ unambiguous a₁ a₂ ret (const _) of λ where
          refl → refl
  (here px , there (here px₁)) ()
  (there (here px) , here px₁) ()
  (there (here v₁≡) , there (here v₂≡)) eq →
    case ‼ Int.nonmalleable v₁ v₂ (trans v₁≡ (sym v₂≡)) ret (const _) of λ where
        refl → case ‼ unambiguous a₁ a₂ ret (const _) of λ where
          refl → refl 
