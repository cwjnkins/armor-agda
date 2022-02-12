{-# OPTIONS --subtyping #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Chain where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig

CCP2Seq : ∀ {@0 bs} → Generic.SequenceOf X509.Cert bs → Set  
CCP2Seq Generic.nil = ⊤
CCP2Seq (Generic.cons (Generic.mkSequenceOf h Generic.nil bs≡)) = ⊤
CCP2Seq (Generic.cons (Generic.mkSequenceOf h (Generic.cons x) bs≡)) = X509.Cert.getVersion h ≡ ℤ.+ 2 × CCP2Seq (Generic.cons x)

CCP2 : ∀ {@0 bs} → X509.Chain bs → Set
CCP2 (Aeres.Grammar.Definitions.mk×ₚ (Generic.cons (Generic.mkSequenceOf h t bs≡₁)) sndₚ₁ bs≡) = CCP2Seq t

ccp2 : ∀ {@0 bs} (c : X509.Chain bs) → Dec (CCP2 c)
ccp2 (Aeres.Grammar.Definitions.mk×ₚ (Generic.cons (Generic.mkSequenceOf h t bs≡₁)) sndₚ₁ bs≡) = helper t
  where
  helper : ∀ {@0 bs} → (c : Generic.SequenceOf X509.Cert bs) → Dec (CCP2Seq c)  
  helper Generic.nil = yes tt
  helper (Generic.cons (Generic.mkSequenceOf h Generic.nil bs≡)) = yes tt
  helper (Generic.cons (Generic.mkSequenceOf h (Generic.cons x) bs≡)) = (X509.Cert.getVersion h ≟ ℤ.+ 2) ×-dec helper (Generic.cons x)
