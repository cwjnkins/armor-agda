{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.OIDSub     as OIDSubProps
import      Aeres.Data.X509.Properties.SequenceOf as SeqProps
import Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.OID where

open Base256
open Aeres.Grammar.Definitions Dig

module OID' where
  @0 unambiguous : Unambiguous OID
  unambiguous =
    TLV.unambiguous
      (SeqProps.BoundedSequenceOf.unambiguous
        OIDSubProps.unambiguous OIDSubProps.nonempty OIDSubProps.nonnesting)

module OIDSeq where
  @0 unambiguous : Unambiguous (SequenceOf OID)
  unambiguous = SeqProps.unambiguous OID'.unambiguous TLV.nonempty TLV.nonnesting

@0 unambiguous : _
unambiguous = OID'.unambiguous

instance
  OIDEq : Eq (Exists─ (List UInt8) OID)
  (OIDEq Eq.≟ (─ x , snd)) (─ x₁ , snd₁)
    with snd ≋? snd₁
  ... | no ¬p = no λ where
    refl → contradiction ≋-refl ¬p
  ... | yes (mk≋ refl refl) = yes refl
