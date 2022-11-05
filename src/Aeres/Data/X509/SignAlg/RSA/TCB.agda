{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
import      Aeres.Data.X509.HashAlg.TCB
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.TCB where

open Aeres.Grammar.Option UInt8

module Param where
  NullOrAbsent = Aeres.Data.X509.HashAlg.TCB.RSASSA-PSS.Param

  {- https://datatracker.ietf.org/doc/html/rfc4055#section-3.1 -}
  record PSS (@0 bs : List UInt8) : Set where
    constructor mkPSS
    field
      @0 {h m sl t} : List UInt8

{-
hashAlgorithm

   The hashAlgorithm field identifies the hash function.  It MUST
   be one of the algorithm identifiers listed in Section 2.1, and
   the default hash function is SHA-1.  Implementations MUST
   support SHA-1 and MAY support any of the other one-way hash
   functions listed in Section 2.1.  Implementations that perform
   signature generation MUST omit the hashAlgorithm field when
   SHA-1 is used, indicating that the default algorithm was used.
   Implementations that perform signature validation MUST
   recognize both the sha1Identifier algorithm identifier and an
   absent hashAlgorithm field as an indication that SHA-1 was
   used.
-}
      hashAlg : Option OID h

    @0 hashAlgDefault : Exists─ _ OIDValue
    hashAlgDefault = elimOption {X = const _} (-, OIDs.SHA1) (λ o → -, TLV.val o) hashAlg

    supportedHashAlgs : List (Exists─ _ OIDValue)
    supportedHashAlgs =
      (_ , OIDs.SHA1) ∷ (_ , OIDs.SHA224) ∷ (_ , OIDs.SHA256) ∷ (_ , OIDs.SHA384) ∷ [ (_ , OIDs.SHA512) ]

    field
      @0 hashAlgSupported : hashAlgDefault ∈ supportedHashAlgs

{-
      maskGenAlgorithm

         The maskGenAlgorithm field identifies the mask generation
         function.  The default mask generation function is MGF1 with
         SHA-1.  For MGF1, it is strongly RECOMMENDED that the
         underlying hash function be the same as the one identified by
         hashAlgorithm.  Implementations MUST support MGF1.  MGF1
         requires a one-way hash function that is identified in the
         parameters field of the MGF1 algorithm identifier.
         Implementations MUST support SHA-1 and MAY support any of the
         other one-way hash functions listed in section Section 2.1.
         The MGF1 algorithm identifier is comprised of the id-mgf1
         object identifier and a parameter that contains the algorithm
         identifier of the one-way hash function employed with MGF1.
         The SHA-1 algorithm identifier is comprised of the id-sha1
         object identifier and an (optional) parameter of NULL.
         Implementations that perform signature generation MUST omit the
         maskGenAlgorithm field when MGF1 with SHA-1 is used, indicating
         that the default algorithm was used.

         Although mfg1SHA1Identifier is defined as the default value for
         this field, implementations MUST accept both the default value
         encoding (i.e., an absent field) and mfg1SHA1Identifier to be
         explicitly present in the encoding.
-}

    --   maskGenAlgo : Option OID m
    --   saltLength : Option Int sl
    --   -- default 20
    --   trailer    : Option Int t
    --   -- if present, must be equal to 1
