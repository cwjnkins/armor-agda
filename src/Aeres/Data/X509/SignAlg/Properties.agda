{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Length
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Data.X509.HashAlg.Properties as HashAlg
open import Aeres.Data.X509.HashAlg.TCB
open import Aeres.Data.X509.SignAlg.Exclusions
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
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any
open import Relation.Nullary.Negation
  using (¬?)

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module Aeres.Data.X509.SignAlg.Properties where

@0 unambiguousUnsupported : Unambiguous UnsupportedSignAlg
unambiguousUnsupported =
  TLV.unambiguous
    (DefinedByOID.unambiguous
      UnsupportedParam
      (λ o → Parallel.unambiguous×ₚ OctetString.unambiguousValue T-unique))

private
  @0 ua₂ : Unambiguous (Sum RSA.Supported UnsupportedSignAlg)
  ua₂ =
    Sum.unambiguous{A = RSA.Supported}{B = UnsupportedSignAlg}
      RSA.Supported.unambiguous
      unambiguousUnsupported
      noConfusion-RSA-Unsupported

  @0 nc₂ : NoConfusion ECDSA.Supported (Sum RSA.Supported UnsupportedSignAlg)
  nc₂ =
    Sum.noconfusion{A = ECDSA.Supported}{B = RSA.Supported}{C = UnsupportedSignAlg}
      noConfusion-ECDSA-RSA
      noConfusion-ECDSA-Unsupported

  @0 ua₁ : Unambiguous (Sum ECDSA.Supported (Sum RSA.Supported UnsupportedSignAlg))
  ua₁ =
    Sum.unambiguous{A = ECDSA.Supported}{B = Sum RSA.Supported UnsupportedSignAlg}
      ECDSA.unambiguous ua₂ nc₂

  @0 nc₁ : NoConfusion DSA.Supported (Sum ECDSA.Supported (Sum RSA.Supported UnsupportedSignAlg))
  nc₁ =
    Sum.noconfusion{A = DSA.Supported}{B = ECDSA.Supported}{C = Sum RSA.Supported UnsupportedSignAlg}
      noConfusion-DSA-ECDSA
      (Sum.noconfusion{A = DSA.Supported}{B = RSA.Supported}{C = UnsupportedSignAlg}
        noConfusion-DSA-RSA
        noConfusion-DSA-Unsupported)

Rep : @0 List UInt8 → Set
Rep =
   Sum DSA.Supported
  (Sum ECDSA.Supported
  (Sum RSA.Supported
       UnsupportedSignAlg))

equiv : Equivalent Rep SignAlg
proj₁ equiv (inj₁ x) = dsa x
proj₁ equiv (inj₂ (inj₁ x)) = ecdsa x
proj₁ equiv (inj₂ (inj₂ (inj₁ x))) = rsa x
proj₁ equiv (inj₂ (inj₂ (inj₂ x))) = unsupported x
proj₂ equiv (dsa x) = inj₁ x
proj₂ equiv (ecdsa x) = inj₂ (inj₁ x)
proj₂ equiv (rsa x) = inj₂ (inj₂ (inj₁ x))
proj₂ equiv (unsupported x) = inj₂ (inj₂ (inj₂ x))

iso : Iso Rep SignAlg
proj₁ iso = equiv
proj₁ (proj₂ iso) (inj₁ x) = refl
proj₁ (proj₂ iso) (inj₂ (inj₁ x)) = refl
proj₁ (proj₂ iso) (inj₂ (inj₂ (inj₁ x))) = refl
proj₁ (proj₂ iso) (inj₂ (inj₂ (inj₂ x))) = refl
proj₂ (proj₂ iso) (dsa x) = refl
proj₂ (proj₂ iso) (ecdsa x) = refl
proj₂ (proj₂ iso) (rsa x) = refl
proj₂ (proj₂ iso) (unsupported x) = refl

@0 unambiguous : Unambiguous SignAlg
unambiguous =
  Iso.unambiguous iso
    (Sum.unambiguous{A = DSA.Supported}{B = Sum ECDSA.Supported (Sum RSA.Supported UnsupportedSignAlg)}
      DSA.unambiguous ua₁ nc₁)

@0 nosubstrings : NoSubstrings SignAlg
nosubstrings xs₁++ys₁≡xs₂++ys₂ a₁ a₂ =
  TLV.nosubstrings xs₁++ys₁≡xs₂++ys₂ (erase a₁) (erase a₂)

