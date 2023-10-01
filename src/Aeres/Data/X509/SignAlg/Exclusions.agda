{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X509.SignAlg.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs          as OIDs
import      Aeres.Data.X509.SignAlg.ECDSA.TCB         as ECDSA
import      Aeres.Data.X509.SignAlg.ECDSA.Properties  as ECDSA
import      Aeres.Data.X509.SignAlg.DSA.Properties    as DSA
import      Aeres.Data.X509.SignAlg.DSA.TCB           as DSA
import      Aeres.Data.X509.SignAlg.RSA.Properties    as RSA
import      Aeres.Data.X509.SignAlg.RSA.TCB           as RSA
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
open import Relation.Nullary.Negation
  using (¬?)

module Aeres.Data.X509.SignAlg.Exclusions where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

@0 noConfusion-DSA-ECDSA : NoConfusion DSA.Supported ECDSA.Supported
noConfusion-DSA-ECDSA xs₁++ys₁≡xs₂++ys₂ dsa' ecda =
  DefinedByOID.noConfusionParam _
    (λ where
      o (mk×ₚ _ o∈DSA) (mk×ₚ _ o∈ECDSA) →
        let
          all : All (_∉ ECDSA.supportedSignAlgOIDs) DSA.supportedSignAlgOIDs
          all = toWitness{Q = All.all? (λ x → ¬? (x ∈? ECDSA.supportedSignAlgOIDs)) DSA.supportedSignAlgOIDs} tt
        in
        contradiction{P = (-, TLV.val o) ∈ ECDSA.supportedSignAlgOIDs}
          (toWitness o∈ECDSA)
          (All.lookup all (toWitness o∈DSA)))
    xs₁++ys₁≡xs₂++ys₂
    (DSA.erase dsa')
    (ECDSA.erase ecda)

@0 noConfusion-DSA-RSA : NoConfusion DSA.Supported RSA.Supported
noConfusion-DSA-RSA xs₁++ys₁≡xs₂++ys₂ dsa' rsa' =
  DefinedByOID.noConfusionParam _
    (λ where
      o (mk×ₚ _ o∈DSA) (mk×ₚ _ o∈RSA) →
        let
          all : All (_∉ RSA.supportedSignAlgOIDs) DSA.supportedSignAlgOIDs
          all = toWitness{Q = All.all? (λ x → ¬? (x ∈? RSA.supportedSignAlgOIDs)) DSA.supportedSignAlgOIDs} tt
        in
        contradiction{P = (-, TLV.val o) ∈ RSA.supportedSignAlgOIDs}
          (toWitness o∈RSA)
          (All.lookup all (toWitness o∈DSA)))
    xs₁++ys₁≡xs₂++ys₂
    (DSA.erase dsa')
    (RSA.erase rsa')

@0 noConfusion-ECDSA-RSA : NoConfusion ECDSA.Supported RSA.Supported
noConfusion-ECDSA-RSA xs₁++ys₁≡xs₂++ys₂  ecda' rsa' =
  DefinedByOID.noConfusionParam _
    (λ where
      o (mk×ₚ _ o∈ECDSA) (mk×ₚ _ o∈RSA) →
        let
          all : All (_∉ RSA.supportedSignAlgOIDs) ECDSA.supportedSignAlgOIDs
          all = toWitness{Q = All.all? (λ x → ¬? (x ∈? RSA.supportedSignAlgOIDs)) ECDSA.supportedSignAlgOIDs} tt
        in
        contradiction{P = (-, TLV.val o) ∈ RSA.supportedSignAlgOIDs}
          (toWitness o∈RSA)
          (All.lookup all (toWitness o∈ECDSA)))
    xs₁++ys₁≡xs₂++ys₂
    (ECDSA.erase ecda')
    (RSA.erase rsa')

@0 noConfusion-DSA-Unsupported : NoConfusion DSA.Supported UnsupportedSignAlg
noConfusion-DSA-Unsupported xs₁++ys₁≡xs₂++ys₂ dsa' un =
  DefinedByOID.noConfusionParam _
    (λ where
      o (mk×ₚ _ o∈?) (mk×ₚ _ o∉?) →
        contradiction
          (Any.++⁺ˡ{xs = DSA.supportedSignAlgOIDs}{ys = ECDSA.supportedSignAlgOIDs ++ RSA.supportedSignAlgOIDs} (toWitness o∈?))
          (toWitnessFalse o∉?))
    xs₁++ys₁≡xs₂++ys₂ (DSA.erase dsa') un


@0 noConfusion-ECDSA-Unsupported : NoConfusion ECDSA.Supported UnsupportedSignAlg
noConfusion-ECDSA-Unsupported xs₁++ys₁≡xs₂++ys₂  ecda' un =
  DefinedByOID.noConfusionParam _
    (λ where
      o (mk×ₚ _ o∈?) (mk×ₚ _ o∉?) →
        contradiction
          (Any.++⁺ʳ DSA.supportedSignAlgOIDs (Any.++⁺ˡ{ys = RSA.supportedSignAlgOIDs} (toWitness o∈?)))
          (toWitnessFalse o∉?))
    xs₁++ys₁≡xs₂++ys₂ (ECDSA.erase ecda') un

@0 noConfusion-RSA-Unsupported : NoConfusion RSA.Supported UnsupportedSignAlg
noConfusion-RSA-Unsupported xs₁++ys₁≡xs₂++ys₂ rsa' un =
  DefinedByOID.noConfusionParam _
    (λ where
      o (mk×ₚ _ o∈?) (mk×ₚ _ o∉?) →
        contradiction
          (Any.++⁺ʳ DSA.supportedSignAlgOIDs (Any.++⁺ʳ ECDSA.supportedSignAlgOIDs (toWitness o∈?)))
          (toWitnessFalse o∉?))
    xs₁++ys₁≡xs₂++ys₂ (RSA.erase rsa') un

