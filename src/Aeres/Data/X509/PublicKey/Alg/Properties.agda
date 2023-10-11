{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.HashAlg.Properties     as HashAlg
open import Aeres.Data.X509.PublicKey.Alg.TCB
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Alg.EC
open import Aeres.Data.X509.PublicKey.Alg.RSA
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

@0 noConfusion-RSA-EC : NoConfusion RSA EC
noConfusion-RSA-EC =
  TLV.noconfusionVal λ where
    {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mkOIDDefinedFields{a}{p} algOID (mk×ₚ _ ≋-refl) bs≡) (mkOIDDefinedFields{a'}{p'} algOID₁ (mk×ₚ _ ≋-refl) bs≡₁) →
      let
        @0 algOID≋ : _≋_{A = OID} algOID algOID₁
        algOID≋ =
          mk≋
            (TLV.nosubstrings
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
    {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mkOIDDefinedFields{a}{p} algOID (mk×ₚ _ ≋-refl) bs≡) (mkOIDDefinedFields{a'}{p'} o (mk×ₚ sndₚ₁ o∉) bs≡₁) →
      let
        @0 ++≡ : Erased (a ++ p ++ ys₁ ≡ a' ++ p' ++ ys₂)
        ++≡ = ─ (begin
          a ++ p ++ ys₁ ≡⟨ sym (++-assoc a p ys₁) ⟩
          (a ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
          xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
          xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
          (a' ++ p') ++ ys₂ ≡⟨ ++-assoc a' p' _ ⟩
          a' ++ p' ++ ys₂ ∎)

        o≋ : _≋_{A = OID} algOID o
        o≋ =
          mk≋
            (TLV.nosubstrings (¡ ++≡) algOID o)
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
    {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mkOIDDefinedFields{a}{p} algOID (mk×ₚ _ ≋-refl) bs≡) (mkOIDDefinedFields{a'}{p'} o (mk×ₚ sndₚ₁ o∉) bs≡₁) →
      let
        ++≡ : Erased (a ++ p ++ ys₁ ≡ a' ++ p' ++ ys₂)
        ++≡ = ─ (begin
          a ++ p ++ ys₁ ≡⟨ sym (++-assoc a p ys₁) ⟩
          (a ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
          xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
          xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
          (a' ++ p') ++ ys₂ ≡⟨ ++-assoc a' p' _ ⟩
          a' ++ p' ++ ys₂ ∎)

        o≋ : _≋_{A = OID} algOID o
        o≋ =
          mk≋
            (TLV.nosubstrings (¡ ++≡) algOID o)
            (OID.unambiguous _ _)
      in
      contradiction
        (case o≋ ret (const _) of λ where
          ≋-refl → toWitness{Q = _ ∈? _} tt)
        (toWitnessFalse o∉)
  where
  open ≡-Reasoning

@0 nosubstrings : NoSubstrings PublicKeyAlg
nosubstrings =
 Sum.nosubstrings
    TLV.nosubstrings
    (Sum.nosubstrings
      TLV.nosubstrings
      TLV.nosubstrings
      noConfusion-EC-Unsupported)
    (NoConfusion.sumₚ{A = RSA}
      noConfusion-RSA-EC
      noConfusion-RSA-Unsupported)

@0 unambiguous : Unambiguous PublicKeyAlg
unambiguous =
  Sum.unambiguous{A = RSA}
    RSA.unambiguous
    (Sum.unambiguous{A = EC} EC.unambiguous
      (TLV.unambiguous
        (DefinedByOID.unambiguous
          UnsupportedParam λ o →
            Parallel.unambiguous×ₚ OctetString.unambiguous T-unique))
      noConfusion-EC-Unsupported)
    (NoConfusion.sumₚ{A = RSA} noConfusion-RSA-EC noConfusion-RSA-Unsupported)

@0 nonmalleableUnsupportedParam : NonMalleable₁ RawUnsupportedParam
nonmalleableUnsupportedParam p₁ p₂ eq =
  Parallel.nonmalleable₁ RawOctetStringValue OctetString.nonmalleableValue
    (λ _ → T-unique) p₁ p₂ eq

@0 nonmalleableUnsupported : NonMalleable RawUnsupportedPublicKeyAlg
nonmalleableUnsupported = DefinedByOID.nonmalleable UnsupportedParam _ λ {bs} {o} → nonmalleableUnsupportedParam{bs}{o}

@0 nonmalleable : NonMalleable RawPublicKeyAlg
nonmalleable = Sum.nonmalleable RSA.nonmalleable (Sum.nonmalleable EC.nonmalleable nonmalleableUnsupported)
