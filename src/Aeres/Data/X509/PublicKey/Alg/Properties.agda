{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
import      Aeres.Data.X509.HashAlg.Properties     as HashAlg
open import Aeres.Data.X509.PublicKey.Alg.TCB
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Alg.EC
open import Aeres.Data.X509.PublicKey.Alg.RSA
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

@0 noConfusion-RSA-EC : NoConfusion RSA EC
noConfusion-RSA-EC =
  TLV.noconfusionVal λ where
    {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mkAlgIDFields{a}{p} algOID (mk×ₚ _ ≋-refl refl) bs≡) (mkAlgIDFields{a'}{p'} algOID₁ (mk×ₚ _ ≋-refl refl) bs≡₁) →
      let
        @0 algOID≋ : _≋_{A = OID} algOID algOID₁
        algOID≋ =
          mk≋
            (TLV.nonnesting
              (a ++ p ++ ys₁ ≡⟨ sym (++-assoc a p ys₁) ⟩
              (a ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
              xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
              xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
              (a' ++ p') ++ ys₂ ≡⟨ ++-assoc a' p' _ ⟩
              a' ++ p' ++ ys₂ ∎)
              algOID algOID₁)
            (OID.unambiguous _ _)
      in
      contradiction{P = _≋_{A = OID} algOID algOID₁}
        algOID≋
        λ where (mk≋ refl ())
  where
  open ≡-Reasoning

@0 noConfusion-RSA-Unsupported : NoConfusion RSA UnsupportedPublicKeyAlg
noConfusion-RSA-Unsupported =
  TLV.noconfusionVal λ where
    {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mkAlgIDFields{a}{p} algOID (mk×ₚ _ ≋-refl refl) bs≡) (mk&ₚ{a'}{p'} (mk×ₚ o o∉ refl) sndₚ₁ bs≡₁) →
      let
        @0 ++≡ : a ++ p ++ ys₁ ≡ a' ++ p' ++ ys₂
        ++≡ = begin
          a ++ p ++ ys₁ ≡⟨ sym (++-assoc a p ys₁) ⟩
          (a ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
          xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
          xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
          (a' ++ p') ++ ys₂ ≡⟨ ++-assoc a' p' _ ⟩
          a' ++ p' ++ ys₂ ∎

        o≋ : _≋_{A = OID} algOID o
        o≋ =
          mk≋
            (TLV.nonnesting ++≡ algOID o)
            (OID.unambiguous _ _)
      in
      contradiction
        (case o≋ ret (const _) of λ where
          ≋-refl → toWitness{Q = _ ∈? _} tt)
        (toWitnessFalse o∉)
  where
  open ≡-Reasoning


@0 noConfusion-EC-Unsupported : NoConfusion EC UnsupportedPublicKeyAlg
noConfusion-EC-Unsupported =
  TLV.noconfusionVal λ where
    {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mkAlgIDFields{a}{p} algOID (mk×ₚ _ ≋-refl refl) bs≡) (mk&ₚ{a'}{p'} (mk×ₚ o o∉ refl) sndₚ₁ bs≡₁) →
      let
        @0 ++≡ : a ++ p ++ ys₁ ≡ a' ++ p' ++ ys₂
        ++≡ = begin
          a ++ p ++ ys₁ ≡⟨ sym (++-assoc a p ys₁) ⟩
          (a ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
          xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
          xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
          (a' ++ p') ++ ys₂ ≡⟨ ++-assoc a' p' _ ⟩
          a' ++ p' ++ ys₂ ∎

        o≋ : _≋_{A = OID} algOID o
        o≋ =
          mk≋
            (TLV.nonnesting ++≡ algOID o)
            (OID.unambiguous _ _)
      in
      contradiction
        (case o≋ ret (const _) of λ where
          ≋-refl → toWitness{Q = _ ∈? _} tt)
        (toWitnessFalse o∉)
  where
  open ≡-Reasoning

@0 nonnesting : NonNesting PublicKeyAlg
nonnesting =
 nonnestingSum
    TLV.nonnesting
    (nonnestingSum
      TLV.nonnesting
      TLV.nonnesting
      noConfusion-EC-Unsupported)
    (NoConfusion.sumₚ{A = RSA}
      noConfusion-RSA-EC
      noConfusion-RSA-Unsupported)

@0 unambiguous : Unambiguous PublicKeyAlg
unambiguous =
  unambiguousSum
    RSA.unambiguous
    (unambiguousSum EC.unambiguous
      (TLV.unambiguous{t = Tag.Sequence}
        (unambiguous&ₚᵈ
          (unambiguousΣₚ OID.unambiguous (λ a → T-unique))
          (nonnestingΣₚ₁ TLV.nonnesting)
          λ a → uniqueSingleton))
      noConfusion-EC-Unsupported)
    (NoConfusion.sumₚ{A = RSA}
      noConfusion-RSA-EC
      noConfusion-RSA-Unsupported)
