{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64
open import Aeres.Prelude

module Aeres.Test.Base64.Base64 where

-- Valid encodings
-- ---------------------------------------------------------------------
-- [[file:../../../assets/sample_certs/Valid/facebook-com-chain.pem]]
str₁ = String.toList "MIIGojCCBYqgAwIBAgIQDExz59mxj/jzZTsZ0IhCATANBgkqhkiG9w0BAQsFADBw"

str₂ = String.toList "e8LRPohzN0fTgGV+cUy2G+6S0tz7Dg=="

str₃ = String.toList "cPUeybQ="

test₁ : Base64Str str₁
test₁ = toWitness{Q = Base64.Str.b64Str? str₁} tt

test₂ : Base64Str str₂
test₂ = toWitness{Q = Base64.Str.b64Str? str₂} tt

test₃ : Base64Str str₃
test₃ = toWitness{Q = Base64.Str.b64Str? str₃} tt

-- Invalid encodings
-- ---------------------------------------------------------------------

-- Bad char
str₄ = String.toList "RVYgUm9vdCBDQTCCASIwDQYJKoZIh*cNAQEBBQADggEP"

test₄ : ¬ Base64Str str₄
test₄ = toWitnessFalse{Q = Base64.Str.b64Str? str₄} tt

-- Bad length (no pad)
str₅ = String.toList "e8LRPohzN0fTgGV+cUy2G+6S0tz7Dg"

test₅ : ¬ Base64Str str₅
test₅ = toWitnessFalse{Q = Base64.Str.b64Str? str₅} tt

-- Bad final char when pad present
str₆ = String.toList "cPUeybB="

test₆ : ¬ Base64Str str₆
test₆ = toWitnessFalse{Q = Base64.Str.b64Str? str₆} tt
