{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.HashAlg.RFC4055.TCB as RFC4055
open import Aeres.Data.X509.HashAlg.TCB.OIDs    as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.RFC4055.TCB where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.Parallel.TCB UInt8
open Aeres.Grammar.Sum.TCB      UInt8

{- https://datatracker.ietf.org/doc/html/rfc4055#section-2.2
-- One mask generation function is used with the RSASSA-PSS signature
-- algorithm and the RSAES-OAEP key transport algorithm: MGF1 [P1v2.1].
-- No other mask generation functions are supported by this
-- specification.
--
-- MGF1 is identified by the following object identifier:
--
--    id-mgf1  OBJECT IDENTIFIER  ::=  { pkcs-1 8 }
--
-- The parameters field associated with id-mgf1 MUST have a
-- hashAlgorithm value which identifies the hash function being used
-- with MGF1.  This value MUST be sha1Identifier, sha224Identifier,
-- sha256Identifier, sha384Identifier, or sha512Identifier, as specified
-- in Section 2.1.  Implementations MUST support the default value,
-- sha1Identifier, and MAY support the other four values.
--
-- The parameters field associated with id-mgf1 MUST have a
-- hashAlgorithm value which identifies the hash function being used
-- with MGF1.  This value MUST be sha1Identifier, sha224Identifier,
-- sha256Identifier, sha384Identifier, or sha512Identifier, as specified
-- in Section 2.1.  Implementations MUST support the default value,
-- sha1Identifier, and MAY support the other four values.
--
-- The following algorithm identifiers have been assigned for each of
-- these alternatives:
--
--    mgf1SHA1Identifier  AlgorithmIdentifier  ::=
--                         { id-mgf1, sha1Identifier }
--    mgf1SHA224Identifier  AlgorithmIdentifier  ::=
--                         { id-mgf1, sha224Identifier }
--    mgf1SHA256Identifier  AlgorithmIdentifier  ::=
--                         { id-mgf1, sha256Identifier }
--    mgf1SHA384Identifier  AlgorithmIdentifier  ::=
--                         { id-mgf1, sha384Identifier }
--    mgf1SHA512Identifier  AlgorithmIdentifier  ::=
--                         { id-mgf1, sha512Identifier }
-}

MGF1Params' : ∀ {@0 bs} → (o : OID bs) (o≋? : Dec (_≋_ {A = OIDValue} (TLV.val o) OIDs.MGF1)) → @0 List UInt8 → Set
MGF1Params' o (no ¬p) = λ _ → ⊥
MGF1Params' o (yes p) = RFC4055.HashAlg

MGF1Params : AnyDefinedByOID
MGF1Params o = MGF1Params' o (TLV.val o ≋? OIDs.MGF1)

RawMGF1Params : Raw₁ RawOID MGF1Params
toRawMGF1Param : ∀ {@0 bs} → (o : OID bs) (o≋? : Dec (_≋_ {A = OIDValue} (TLV.val o) OIDs.MGF1))
                  → ∀ {@0 bs'} → MGF1Params' o o≋? bs' → Raw₁.D RawMGF1Params (Raw.to RawOID o)

Raw₁.D RawMGF1Params _ = Raw.D RFC4055.RawHashAlg
Raw₁.to RawMGF1Params o = toRawMGF1Param o (TLV.val o ≋? OIDs.MGF1)

toRawMGF1Param o (yes p) x = Raw.to RFC4055.RawHashAlg x

MGF1 : @0 List UInt8 → Set
MGF1 = DefinedByOID MGF1Params

RawMGF1 : Raw MGF1
RawMGF1 = RawDefinedByOID RawMGF1Params
