{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.GeneralName  as GNProps
import      Aeres.Data.X509.Properties.RDNATVFields as RDNATVProps
import      Aeres.Data.X509.Properties.RDNSeq       as RDNProps
import      Aeres.Data.X509.Properties.SequenceOf   as SeqProps
import      Aeres.Data.X509.Properties.TLV          as TLVProps
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.DistPointNameChoice where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum         Dig

nonnesting : NonNesting X509.DistPointNameChoice
nonnesting x (X509.fullname x₁) (X509.fullname x₂) = ‼ TLVProps.nonnesting x x₁ x₂
nonnesting x (X509.fullname x₁) (X509.nameRTCrlissr x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.nameRTCrlissr x₁) (X509.fullname x₂) = ⊥-elim (TLVProps.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.nameRTCrlissr x₁) (X509.nameRTCrlissr x₂) = ‼ TLVProps.nonnesting x x₁ x₂


equivalent : Equivalent (Sum X509.FullName X509.NameRTCrlIssuer) X509.DistPointNameChoice
proj₁ equivalent (Sum.inj₁ x) = X509.fullname x
proj₁ equivalent (Sum.inj₂ x) = X509.nameRTCrlissr x
proj₂ equivalent (X509.fullname x) = Sum.inj₁ x
proj₂ equivalent (X509.nameRTCrlissr x) = Sum.inj₂ x

iso : Iso (Sum X509.FullName X509.NameRTCrlIssuer) X509.DistPointNameChoice
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl
proj₂ (proj₂ iso) (X509.fullname x) = refl
proj₂ (proj₂ iso) (X509.nameRTCrlissr x) = refl

@0 unambiguous : Unambiguous X509.DistPointNameChoice
unambiguous =
  isoUnambiguous iso
    (unambiguousSum
      (TLVProps.unambiguous GNProps.GeneralNamesElems.unambiguous)
      (TLVProps.unambiguous
        (SeqProps.BoundedSequenceOf.unambiguous (TLVProps.unambiguous RDNATVProps.unambiguous)
          TLVProps.nonempty TLVProps.nonnesting))
      (TLVProps.noconfusion λ ()))
