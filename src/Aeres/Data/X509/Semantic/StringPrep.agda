{-# OPTIONS --subtyping #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.UTF8.TCB

module Aeres.Data.X509.Semantic.StringPrep where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig


-- StringPrepCompare : ∀ {@0 bs₁ bs₂} → X509.DirectoryString bs₁ → X509.DirectoryString bs₂ → Set
-- StringPrepCompare a@(X509.teletexString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.printableString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.utf8String x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.printableString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.printableString x) b@(X509.printableString x₁) = {!!}
-- StringPrepCompare a@(X509.printableString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.printableString x) b@(X509.utf8String x₁) = {!!}
-- StringPrepCompare a@(X509.printableString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.printableString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.utf8String x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.utf8String x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.utf8String x) b@(X509.printableString x₁) = {!!}
-- StringPrepCompare a@(X509.utf8String x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.utf8String x) b@(X509.utf8String x₁) = {!!}
-- StringPrepCompare a@(X509.utf8String x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.printableString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.utf8String x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b


-- Transcode : ∀ {@0 bs} → X509.DirectoryString bs → List Dig
-- Transcode (X509.teletexString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = {!!}
-- Transcode (X509.printableString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = x
-- Transcode (X509.universalString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = {!!}
-- Transcode (X509.utf8String (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = x
-- Transcode (X509.bmpString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = {!!}
