{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PC.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PC.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

iso : Iso PCFieldsSeqFieldsRep PCFieldsSeqFields
proj₁ iso = equivalentPCFieldsSeqFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkPCFieldsSeqFields require inhibit refl) = refl

@0 unambiguous : Unambiguous PCFields
unambiguous = TLV.unambiguous (TLV.unambiguous
  (Iso.unambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous λ {xs} → Int.unambiguous{xs}) TLV.nosubstrings TLV.nonempty
      (TLV.unambiguous λ {xs} → Int.unambiguous{xs}) TLV.nonempty (TLV.noconfusion λ ()))))

@0 nonmalleable : NonMalleable RawPCFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
  (Iso.nonmalleable iso
    RawPCFieldsSeqFieldsRep
    (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable Int.nonmalleableVal))
      (Option.nonmalleable _ (TLV.nonmalleable Int.nonmalleableVal)))))
