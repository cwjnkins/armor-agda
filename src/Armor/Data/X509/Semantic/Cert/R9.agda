{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.R9.TCB
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
open import Armor.Prelude
import      Data.List.Membership.Propositional as List
import      Data.List.Membership.Propositional.Properties as List

module Armor.Data.X509.Semantic.Cert.R9 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

r9 : ∀ {@0 bs} (c : Cert bs) → Dec (R9 c)
r9 c =
  case Cert.getKU c ret (λ ku → Dec (R9' (proj₂ ku))) of λ where
    (─ _ , none) → yes tt
    (─ _ , some ku) → case Any.any? (λ bf → T? (assertsKUBitField ku bf)) allFields of λ where
      (no ¬asserts) → no λ where
        (bf , asserts) →
          contradiction
            (List.lose{xs = allFields} (allFieldsProp bf) asserts)
            ¬asserts
      (yes someAsserts) →
        let (bf , _ , bfAsserted) = Data.List.Membership.Propositional.find{xs = allFields} someAsserts in
        yes (bf , bfAsserted)
  where
  import Data.List.Membership.Propositional
  bits : ∀ {@0 bs} → (ku : ExtensionFieldKU bs) → List Bool
  bits ku = ↑ BitStringValue.bits (TLV.val (TLV.val (ExtensionFields.extension ku)))

  allFields = tabulate{n = 9} id

  @0 allFieldsProp : (bf : Extension.KUFields.BitField) → bf ∈ allFields
  allFieldsProp bf
    with lookup-tabulate id bf
  ... | lookup∈
    with ‼ cast≡ bf (sym (length-tabulate id))
    where
    cast≡ : ∀ {n} (i : Fin n) (eq : n ≡ n) → Fin.cast eq i ≡ i
    cast≡ Fin.zero _ = refl
    cast≡ (Fin.suc i) refl = icong{f = Fin.suc} (cast≡ i refl)
  ... | c≡
    with (Fin.cast (sym (length-tabulate id)) bf)
  allFieldsProp bf | lookup∈ | refl | ._ =
    subst (_∈ allFields) lookup∈ (List.∈-lookup {xs = allFields} bf)
