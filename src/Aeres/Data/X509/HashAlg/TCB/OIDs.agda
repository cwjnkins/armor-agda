{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.Parser
open import Aeres.Data.X690-DER.OID.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.HashAlg.TCB.OIDs where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

{-
https://datatracker.ietf.org/doc/html/rfc4055#section-2.1

These one-way hash functions are identified by the following object
identifiers:

      id-sha1  OBJECT IDENTIFIER  ::=  { iso(1)
                           identified-organization(3) oiw(14)
                           secsig(3) algorithms(2) 26 }
      id-sha224  OBJECT IDENTIFIER  ::=  {{ joint-iso-itu-t(2)
                           country(16) us(840) organization(1) gov(101)
                           csor(3) nistalgorithm(4) hashalgs(2) 4 }
      id-sha256  OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2)
                           country(16) us(840) organization(1) gov(101)
                           csor(3) nistalgorithm(4) hashalgs(2) 1 }
      id-sha384  OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2)
                           country(16) us(840) organization(1) gov(101)
                           csor(3) nistalgorithm(4) hashalgs(2) 2 }
      id-sha512  OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2)
                           country(16) us(840) organization(1) gov(101)
                           csor(3) nistalgorithm(4) hashalgs(2) 3 }
-}

SHA1Lit SHA224Lit SHA256Lit SHA384Lit SHA512Lit : List UInt8

SHA1Lit = # 43 ∷ # 14 ∷ # 3 ∷ # 2 ∷ [ # 26 ]

SHA1 : OIDValue SHA1Lit
SHA1 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA1Lit)) SHA1Lit)} tt))

SHA224Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 4 ] 

SHA224 : OIDValue SHA224Lit
SHA224 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA224Lit)) SHA224Lit)} tt))

SHA256Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 1 ] 

SHA256 : OIDValue SHA256Lit
SHA256 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA256Lit)) SHA256Lit)} tt))

SHA384Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 2 ]

SHA384 : OIDValue SHA384Lit
SHA384 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA384Lit)) SHA384Lit)} tt))

SHA512Lit = # 96 ∷ # 134 ∷ # 72 ∷ # 1 ∷ # 101 ∷ # 3 ∷ # 4 ∷ # 2 ∷ [ # 3 ]

SHA512 : OIDValue SHA512Lit
SHA512 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SHA512Lit)) SHA512Lit)} tt))

NullOrAbsent : List (Exists─ _ OIDValue)
NullOrAbsent = (_ , SHA1) ∷ (_ , SHA224) ∷ (_ , SHA256) ∷ (_ , SHA384) ∷ [ (_ , SHA512) ]
