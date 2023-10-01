{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree
open import Aeres.Data.X509.Extension.NC.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

Rep = &ₚ (Option PermittedSubtrees) (Option ExcludedSubtrees)

equivalent : Equivalent Rep NCFieldsSeqFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ refl) = mkNCFieldsSeqFields fstₚ₁ sndₚ₁ refl
proj₂ equivalent (mkNCFieldsSeqFields permt excld refl) = mk&ₚ permt excld refl

iso : Iso Rep NCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkNCFieldsSeqFields permt excld refl) = refl

@0 unambiguous : Unambiguous NCFieldsSeqFields
unambiguous = Iso.unambiguous iso
                (Unambiguous.option₂&₁
                  (TLV.unambiguous
                    (SequenceOf.Bounded.unambiguous
                      (TLV.unambiguous GeneralSubtree.unambiguous) TLV.nonempty TLV.nosubstrings))
                  TLV.nosubstrings
                  TLV.nonempty
                  (TLV.unambiguous
                    (SequenceOf.Bounded.unambiguous
                      (TLV.unambiguous GeneralSubtree.unambiguous)  TLV.nonempty TLV.nosubstrings))
                  TLV.nonempty (TLV.noconfusion λ ()))
