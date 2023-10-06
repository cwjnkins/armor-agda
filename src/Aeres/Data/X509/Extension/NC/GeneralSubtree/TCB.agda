{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.GeneralName.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Option
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.GeneralSubtree.TCB where

open Aeres.Grammar.Option UInt8
open Aeres.Grammar.Definitions              UInt8
open Aeres.Grammar.Seq.TCB UInt8

MinBaseDistance : @0 List UInt8 → Set
MinBaseDistance xs = TLV Tag.A80 IntegerValue xs

MaxBaseDistance : @0 List UInt8 → Set
MaxBaseDistance xs = TLV Tag.A81 IntegerValue xs

record GeneralSubtreeFields (@0 bs : List UInt8) : Set where
  constructor mkGeneralSubtreeFields
  field
    @0 {bse minb maxb} : List UInt8
    base : GeneralName bse
    minimum : Option MinBaseDistance minb
    maximum : Option MaxBaseDistance maxb
    @0 bs≡  : bs ≡ bse ++ minb ++ maxb

GeneralSubtree : @0 List UInt8 → Set
GeneralSubtree xs = TLV Tag.Sequence GeneralSubtreeFields xs

GeneralSubtrees : @0 List UInt8 → Set
GeneralSubtrees xs = (NonEmptySequenceOf GeneralSubtree) xs

GeneralSubtreeFieldsRep = &ₚ GeneralName (&ₚ (Option MinBaseDistance) (Option MaxBaseDistance))

equivalentGeneralSubtreeFields : Equivalent GeneralSubtreeFieldsRep GeneralSubtreeFields
proj₁ equivalentGeneralSubtreeFields (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = mkGeneralSubtreeFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalentGeneralSubtreeFields (mkGeneralSubtreeFields base minimum maximum refl) = (mk&ₚ base (mk&ₚ minimum maximum refl) refl)

RawGeneralSubtreeFieldsRep : Raw GeneralSubtreeFieldsRep
RawGeneralSubtreeFieldsRep = Raw&ₚ RawGeneralName
                              (Raw&ₚ (RawOption (RawTLV _ RawIntegerValue))
                                      (RawOption (RawTLV _ RawIntegerValue)))

RawGeneralSubtreeFields : Raw GeneralSubtreeFields
RawGeneralSubtreeFields = Iso.raw equivalentGeneralSubtreeFields RawGeneralSubtreeFieldsRep

RawGeneralSubtrees : Raw GeneralSubtrees
RawGeneralSubtrees = RawBoundedSequenceOf (RawTLV _ RawGeneralSubtreeFields) 1
