{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.TCB.OIDs  as OIDs
import      Aeres.Data.X509.HashAlg.TCB       as HashAlg
import      Aeres.Data.X509.HashAlg.TCB.OIDs  as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB    as MaskGenAlg
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Sum         UInt8

MD2    = HashAlg.SHA-Like OIDs.RSA.MD2
MD5    = HashAlg.SHA-Like OIDs.RSA.MD5
SHA1   = HashAlg.SHA-Like OIDs.RSA.SHA1
SHA224 = HashAlg.SHA-Like OIDs.RSA.SHA224
SHA256 = HashAlg.SHA-Like OIDs.RSA.SHA256
SHA384 = HashAlg.SHA-Like OIDs.RSA.SHA384
SHA512 = HashAlg.SHA-Like OIDs.RSA.SHA512

--   {- https://datatracker.ietf.org/doc/html/rfc4055#section-3.1 -}
{-
      id-RSASSA-PSS  OBJECT IDENTIFIER  ::=  { pkcs-1 10 }

      RSASSA-PSS-params  ::=  SEQUENCE  {
         hashAlgorithm      [0] HashAlgorithm DEFAULT
                                   sha1Identifier,
         maskGenAlgorithm   [1] MaskGenAlgorithm DEFAULT
                                   mgf1SHA1Identifier,
         saltLength         [2] INTEGER DEFAULT 20,
         trailerField       [3] INTEGER DEFAULT 1  }
-}
record PSSParamFields (@0 bs : List UInt8) : Set where
  constructor mkPSSParam
  field
    @0 {h m s t} : List UInt8
-- hashAlgorithm

--    The hashAlgorithm field identifies the hash function.  It MUST
--    be one of the algorithm identifiers listed in Section 2.1, and
--    the default hash function is SHA-1.  Implementations MUST
--    support SHA-1 and MAY support any of the other one-way hash
--    functions listed in Section 2.1.  Implementations that perform
--    signature generation MUST omit the hashAlgorithm field when
--    SHA-1 is used, indicating that the default algorithm was used.
--    Implementations that perform signature validation MUST
--    recognize both the sha1Identifier algorithm identifier and an
--    absent hashAlgorithm field as an indication that SHA-1 was
--    used.
--
  SupportedHashAlg : @0 List UInt8 → Set
  SupportedHashAlg =
     Sum HashAlg.SHA1
    (Sum HashAlg.SHA224
    (Sum HashAlg.SHA256
    (Sum HashAlg.SHA384
         HashAlg.SHA512)))

  field
    hashAlg : Option SupportedHashAlg h

-- maskGenAlgorithm

--    The maskGenAlgorithm field identifies the mask generation
--    function.  The default mask generation function is MGF1 with
--    SHA-1.  For MGF1, it is strongly RECOMMENDED that the
--    underlying hash function be the same as the one identified by
--    hashAlgorithm.  Implementations MUST support MGF1.  MGF1
--    requires a one-way hash function that is identified in the
--    parameters field of the MGF1 algorithm identifier.
--    Implementations MUST support SHA-1 and MAY support any of the
--    other one-way hash functions listed in section Section 2.1.
--    The MGF1 algorithm identifier is comprised of the id-mgf1
--    object identifier and a parameter that contains the algorithm
--    identifier of the one-way hash function employed with MGF1.
--    The SHA-1 algorithm identifier is comprised of the id-sha1
--    object identifier and an (optional) parameter of NULL.
--    Implementations that perform signature generation MUST omit the
--    maskGenAlgorithm field when MGF1 with SHA-1 is used, indicating
--    that the default algorithm was used.

--    Although mfg1SHA1Identifier is defined as the default value for
--    this field, implementations MUST accept both the default value
--    encoding (i.e., an absent field) and mfg1SHA1Identifier to be
--    explicitly present in the encoding.
    maskGenAlgo : MaskGenAlg.MGF1.MaskGenAlg m

-- saltLength

--    The saltLength field is the octet length of the salt.  For a
--    given hashAlgorithm, the recommended value of saltLength is the
--    number of octets in the hash value.  Unlike the other fields of
--    type RSASSA-PSS-params, saltLength does not need to be fixed
--    for a given RSA key pair; a different value could be used for
--    each RSASSA-PSS signature generated.
    saltLength : Option Int s

-- trailerField

--    The trailerField field is an integer.  It provides
--    compatibility with IEEE Std 1363a-2004 [P1363A].  The value
--    MUST be 1, which represents the trailer field with hexadecimal
--    value 0xBC.  Other trailer fields, including the trailer field
--    composed of HashID concatenated with 0xCC that is specified in
--    IEEE Std 1363a, are not supported.  Implementations that
--    perform signature generation MUST omit the trailerField field,
--    indicating that the default trailer field value was used.
--    Implementations that perform signature validation MUST
--    recognize both a present trailerField field with value 1 and an
--    absent trailerField field.
    trailerField : Option (Σₚ Int λ _ i → getVal i ≡ ℤ.1ℤ) t
