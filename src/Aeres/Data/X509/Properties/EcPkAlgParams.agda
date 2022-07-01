{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Aeres.Binary

module Aeres.Data.X509.Properties.EcPkAlgParams where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning

Rep : @0 List UInt8 → Set
Rep =  Sum X509.EcParams (Sum OID (_≡ X509.ExpNull))

equivalent : Equivalent Rep X509.EcPkAlgParams
proj₁ equivalent (Sum.inj₁ x) = X509.ecparams x
proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = X509.namedcurve x
proj₁ equivalent (Sum.inj₂ (Sum.inj₂ x)) = X509.implicitlyCA x
proj₂ equivalent (X509.ecparams x) = inj₁ x
proj₂ equivalent (X509.namedcurve x) = inj₂ (inj₁ x)
proj₂ equivalent (X509.implicitlyCA x) = inj₂ (inj₂ x)

@0 len≥1 : ∀ {@0 bs} → X509.EcPkAlgParams bs → length bs ≥ 1
len≥1 (X509.ecparams (mkTLV len val len≡ refl))   = s≤s z≤n
len≥1 (X509.namedcurve (mkTLV len val len≡ refl)) = s≤s z≤n
len≥1 (X509.implicitlyCA refl)                    = s≤s z≤n
