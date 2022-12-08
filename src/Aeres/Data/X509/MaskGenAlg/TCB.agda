{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
import Aeres.Data.X509.HashAlg.TCB              as HashAlg
open import Aeres.Data.X509.HashAlg.TCB.OIDs    as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
-- import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

module MGF1 where
{-
   The parameters field associated with id-mgf1 MUST have a
   hashAlgorithm value which identifies the hash function being used
   with MGF1.  This value MUST be sha1Identifier, sha224Identifier,
   sha256Identifier, sha384Identifier, or sha512Identifier, as specified
   in Section 2.1.  Implementations MUST support the default value,
   sha1Identifier, and MAY support the other four values.

   The following algorithm identifiers have been assigned for each of
   these alternatives:

      mgf1SHA1Identifier  AlgorithmIdentifier  ::=
                           { id-mgf1, sha1Identifier }
      mgf1SHA224Identifier  AlgorithmIdentifier  ::=
                           { id-mgf1, sha224Identifier }
      mgf1SHA256Identifier  AlgorithmIdentifier  ::=
                           { id-mgf1, sha256Identifier }
      mgf1SHA384Identifier  AlgorithmIdentifier  ::=
                           { id-mgf1, sha384Identifier }
      mgf1SHA512Identifier  AlgorithmIdentifier  ::=
                           { id-mgf1, sha512Identifier }
-}

  SupportedHashAlg : @0 List UInt8 → Set
  SupportedHashAlg =
    Sum HashAlg.SHA1
    (Sum HashAlg.SHA224
    (Sum HashAlg.SHA256
    (Sum HashAlg.SHA384
         HashAlg.SHA512)))

  Param : {@0 bs : List UInt8} (o : OID bs) → @0 List UInt8 → Set
  Param o =    SupportedHashAlg
            ×ₚ const (_≋_{A = OIDValue} (TLV.val o) OIDs.MGF1)

  MaskGenAlg = AlgorithmIdentifier Param