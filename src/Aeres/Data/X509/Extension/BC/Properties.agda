{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.BC.TCB
open import Aeres.Data.X690-DER.Boool
open import Aeres.Data.X690-DER.Default
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.BC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

Rep = &ₚ (Default Boool falseBoool) (Option Int)

equivalent : Equivalent Rep BCFieldsSeqFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkBCFieldsSeqFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkBCFieldsSeqFields bcca bcpathlen bs≡) = mk&ₚ bcca bcpathlen bs≡

iso : Iso Rep BCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkBCFieldsSeqFields bcca bcpathlen bs≡) = refl

postulate
  @0 unambiguous : Unambiguous BCFields
-- unambiguous =
--   TLV.unambiguous (TLV.unambiguous (Iso.unambiguous iso
--     (Seq.unambiguous (Default.unambiguous _ Boool.unambiguous TLV.nonempty) {!!}
--       (Option.unambiguous Int.unambiguous TLV.nonempty))))

@0 nonmalleable : NonMalleable RawBCFields
nonmalleable =
  TLV.nonmalleable (TLV.nonmalleable
    (Iso.nonmalleable iso RawBCFieldsSeqFieldsRep
      (Seq.nonmalleable (Default.nonmalleable _ Boool.nonmalleable)
                        (Option.nonmalleable _ Int.nonmalleable))))
