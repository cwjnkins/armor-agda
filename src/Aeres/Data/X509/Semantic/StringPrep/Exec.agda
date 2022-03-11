{-# OPTIONS --subtyping --sized-types #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList as IList
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.UTF8.Parser
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.Combine

module Aeres.Data.X509.Semantic.StringPrep.Exec where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig


Compare : ∀ {@0 bs₁ bs₂} → X509.DirectoryString bs₁ → X509.DirectoryString bs₂ → Set
Compare (X509.teletexString x) (X509.teletexString x₁) = ⊥
Compare (X509.teletexString x) (X509.printableString x₁) = ⊥
Compare (X509.teletexString x) (X509.universalString x₁) = ⊥
Compare (X509.teletexString x) (X509.utf8String x₁) = ⊥
Compare (X509.teletexString x) (X509.bmpString x₁) = ⊥
Compare (X509.printableString x) (X509.teletexString x₁) = ⊥
Compare (X509.printableString x) (X509.printableString x₁) = {!!}
Compare (X509.printableString x) (X509.universalString x₁) = {!!}
Compare (X509.printableString x) (X509.utf8String x₁) = {!!}
Compare (X509.printableString x) (X509.bmpString x₁) = {!!}
Compare (X509.universalString x) (X509.teletexString x₁) = ⊥
Compare (X509.universalString x) (X509.printableString x₁) = {!!}
Compare (X509.universalString x) (X509.universalString x₁) = {!!}
Compare (X509.universalString x) (X509.utf8String x₁) = {!!}
Compare (X509.universalString x) (X509.bmpString x₁) = {!!}
Compare (X509.utf8String x) (X509.teletexString x₁) = ⊥
Compare (X509.utf8String x) (X509.printableString x₁) = {!!}
Compare (X509.utf8String x) (X509.universalString x₁) = {!!}
Compare (X509.utf8String x) (X509.utf8String x₁) = {!!}
Compare (X509.utf8String x) (X509.bmpString x₁) = {!!}
Compare (X509.bmpString x) (X509.teletexString x₁) = ⊥
Compare (X509.bmpString x) (X509.printableString x₁) = {!!}
Compare (X509.bmpString x) (X509.universalString x₁) = {!!}
Compare (X509.bmpString x) (X509.utf8String x₁) = {!!}
Compare (X509.bmpString x) (X509.bmpString x₁) = {!!}


Transcode : ∀ {@0 bs} → X509.DirectoryString bs → Exists─ (List UInt8) UTF8
Transcode (X509.teletexString x) = _ , nil
Transcode (X509.printableString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV len (X509.mkIA5StringValue (singleton x refl) all<128) len≡ bs≡₁) sndₚ₁ bs≡)) = helper x all<128
  where
  helper : (ss : List UInt8) → @0 All (Fin._< # 128) ss → Exists─ (List UInt8) UTF8
  helper [] All.[] = _ , nil
  helper (x ∷ ss) (px All.∷ x₁) = _ , (cons (IList.mkIListCons (utf81 (mkUTF8Char1 x px refl)) (proj₂ (helper ss x₁)) refl))
Transcode (X509.universalString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = _ , val
Transcode (X509.utf8String (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = _ , val
Transcode (X509.bmpString (Aeres.Grammar.Definitions.mk×ₚ (mkTLV {v = v} len val len≡ refl) sndₚ₁ refl)) = _ , val


-- CaseFoldingNFKC : ∀ {@0 bs} → UTF8 bs → Exists─ (List UInt8) UTF8
-- CaseFoldingNFKC x = {!!}
