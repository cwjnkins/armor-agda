{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.TCB
import      Armor.Data.X690-DER.Int.Properties as Int
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.TLV.Properties as TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.Properties as Parallel'
open import Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.Properties where

open Armor.Grammar.Definitions UInt8
private
  module Parallel = Parallel' UInt8

@0 nosubstrings : NoSubstrings ReasonCodeFieldsEnum
nosubstrings = Parallel.nosubstrings₁ TLV.nosubstrings

@0 unambiguous' : Unambiguous ReasonCodeFieldsEnum
unambiguous' = Parallel.unambiguous (TLV.unambiguous Int.unambiguousValue)
    λ v → erased-unique (∈-unique (toWitness{a? = List.unique? _≟_ supportedCodes} tt))

@0 unambiguous : Unambiguous ReasonCodeFields
unambiguous = TLV.unambiguous unambiguous'

@0 nonmalleable : NonMalleable RawReasonCodeFields
nonmalleable = TLV.nonmalleable nm
  where
  nm : NonMalleable RawReasonCodeFieldsEnum
  nm a₁@(mk×ₚ v₁ (─ v₁∈)) a₂@(mk×ₚ v₂ (─ v₂∈)) =
    case (uneraseDec v₁∈ (_ ∈? _) ,′ uneraseDec v₂∈ (_ ∈? _))
    ret (λ where (z₁ , z₂) → toRawReasonCodeFieldsEnum v₁ z₁ ≡ toRawReasonCodeFieldsEnum v₂ z₂ → _≡_{A = Exists─ _ ReasonCodeFieldsEnum}(─ _ , a₁) (─ _ , a₂))
    of λ where
      (here px , here px₁) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (here px , there (here px₁)) ()
      (here px , there (there (here px₁))) ()
      (here px , there (there (there (here px₁)))) ()
      (here px , there (there (there (there (here px₁))))) ()
      (here px , there (there (there (there (there (here px₁)))))) ()
      (here px , there (there (there (there (there (there (here px₁))))))) ()
      (here px , there (there (there (there (there (there (there (here px₁)))))))) ()
      (here px , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (here px , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (here px₁) , here px) ()
      (there (there (here px₁)) , here px) ()
      (there (there (there (here px₁))) , here px) ()
      (there (there (there (there (here px₁)))) , here px) ()
      (there (there (there (there (there (here px₁))))) , here px) ()
      (there (there (there (there (there (there (here px₁)))))) , here px) ()
      (there (there (there (there (there (there (there (here px₁))))))) , here px) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , here px) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , here px) ()
      (there (here px) , there (here px₁)) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (here px) , there (there (here px₁))) ()
      (there (here px) , there (there (there (here px₁)))) ()
      (there (here px) , there (there (there (there (here px₁))))) ()
      (there (here px) , there (there (there (there (there (here px₁)))))) ()
      (there (here px) , there (there (there (there (there (there (here px₁))))))) ()
      (there (here px) , there (there (there (there (there (there (there (here px₁)))))))) ()
      (there (here px) , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (there (here px) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (here px₁)) , there (here px)) ()
      (there (there (there (here px₁))) , there (here px)) ()
      (there (there (there (there (here px₁)))) , there (here px)) ()
      (there (there (there (there (there (here px₁))))) , there (here px)) ()
      (there (there (there (there (there (there (here px₁)))))) , there (here px)) ()
      (there (there (there (there (there (there (there (here px₁))))))) , there (here px)) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , there (here px))()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (here px)) ()
      (there (there (here px)) , there (there (here px₁))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (there (here px)) , there (there (there (here px₁)))) ()
      (there (there (here px)) , there (there (there (there (here px₁))))) ()
      (there (there (here px)) , there (there (there (there (there (here px₁)))))) ()
      (there (there (here px)) , there (there (there (there (there (there (here px₁))))))) ()
      (there (there (here px)) , there (there (there (there (there (there (there (here px₁)))))))) ()
      (there (there (here px)) , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (there (there (here px)) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (there (here px₁))) , there (there (here px))) ()
      (there (there (there (there (here px₁)))) , there (there (here px))) ()
      (there (there (there (there (there (here px₁))))) , there (there (here px))) ()
      (there (there (there (there (there (there (here px₁)))))) , there (there (here px))) ()
      (there (there (there (there (there (there (there (here px₁))))))) , there (there (here px))) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , there (there (here px))) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (there (here px))) ()
      (there (there (there (here px))) , there (there (there (here px₁)))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (there (there (here px))) , there (there (there (there (here px₁))))) ()
      (there (there (there (here px))) , there (there (there (there (there (here px₁)))))) ()
      (there (there (there (here px))) , there (there (there (there (there (there (here px₁))))))) ()
      (there (there (there (here px))) , there (there (there (there (there (there (there (here px₁)))))))) ()
      (there (there (there (here px))) , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (there (there (there (here px))) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (there (there (here px₁)))) , there (there (there (here px)))) ()
      (there (there (there (there (there (here px₁))))) , there (there (there (here px)))) ()
      (there (there (there (there (there (there (here px₁)))))) , there (there (there (here px)))) ()
      (there (there (there (there (there (there (there (here px₁))))))) , there (there (there (here px)))) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , there (there (there (here px)))) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (there (there (here px)))) ()
      (there (there (there (there (here px)))) , there (there (there (there (here px₁))))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (there (there (there (here px)))) , there (there (there (there (there (here px₁)))))) ()
      (there (there (there (there (here px)))) , there (there (there (there (there (there (here px₁))))))) ()
      (there (there (there (there (here px)))) , there (there (there (there (there (there (there (here px₁)))))))) ()
      (there (there (there (there (here px)))) , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (there (there (there (there (here px)))) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (there (there (there (here px₁))))) , there (there (there (there (here px))))) ()
      (there (there (there (there (there (there (here px₁)))))) , there (there (there (there (here px))))) ()
      (there (there (there (there (there (there (there (here px₁))))))) , there (there (there (there (here px))))) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , there (there (there (there (here px))))) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (there (there (there (here px))))) ()
      (there (there (there (there (there (here px))))) , there (there (there (there (there (here px₁)))))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (there (there (there (there (here px))))) , there (there (there (there (there (there (here px₁))))))) ()
      (there (there (there (there (there (here px))))) , there (there (there (there (there (there (there (here px₁)))))))) ()
      (there (there (there (there (there (here px))))) , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (there (there (there (there (there (here px))))) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (there (there (there (there (here px₁)))))) , there (there (there (there (there (here px)))))) ()
      (there (there (there (there (there (there (there (here px₁))))))) , there (there (there (there (there (here px)))))) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , there (there (there (there (there (here px)))))) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (there (there (there (there (here px)))))) ()
      (there (there (there (there (there (there (here px)))))) , there (there (there (there (there (there (here px₁))))))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (there (there (there (there (there (here px)))))) , there (there (there (there (there (there (there (here px₁)))))))) ()
      (there (there (there (there (there (there (here px)))))) , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (there (there (there (there (there (there (here px)))))) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (there (there (there (there (there (here px₁))))))) , there (there (there (there (there (there (here px))))))) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , there (there (there (there (there (there (here px))))))) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (there (there (there (there (there (here px))))))) ()
      (there (there (there (there (there (there (there (here px))))))) , there (there (there (there (there (there (there (here px₁)))))))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (there (there (there (there (there (there (here px))))))) , there (there (there (there (there (there (there (there (here px₁))))))))) ()
      (there (there (there (there (there (there (there (here px))))))) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (there (there (there (there (there (there (here px₁)))))))) , there (there (there (there (there (there (there (here px)))))))) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (there (there (there (there (there (there (here px)))))))) ()
      (there (there (there (there (there (there (there (there (here px)))))))) , there (there (there (there (there (there (there (there (here px₁))))))))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
      (there (there (there (there (there (there (there (there (here px)))))))) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) ()
      (there (there (there (there (there (there (there (there (there (here px₁))))))))) , there (there (there (there (there (there (there (there (here px))))))))) ()
      (there (there (there (there (there (there (there (there (there (here px))))))))) , there (there (there (there (there (there (there (there (there (here px₁)))))))))) eq →
        case  ‼ Int.[ Tag.Enum ]nonmalleable v₁ v₂ (trans px (sym px₁)) ret (const _) of λ where
          refl → case ‼ unambiguous' a₁ a₂ ret (const _) of λ where
            refl → refl
