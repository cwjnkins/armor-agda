{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.HashAlg.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Prelude

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

module Aeres.Data.X509.SignAlg.TCB where

module Params where
  NullOrAbsent = Option Null
  Absent       = _≡_{A = List UInt8} []

  record PSS (@0 bs : List UInt8) : Set where
    constructor mkPSS
    field
      @0 {h m sl t} : List UInt8
      hashAlg : RSASSA-PSS.HashAlg h

    -- @0 hashAlgoDefault : ∃ OIDValue
    -- hashAlgoDefault = elimOption {X = const _} (-, OIDs.Hash.SHA1) (λ o → -, TLV.val o) hashAlgo

    -- field
    --   supportedHashAlgo : hashAlgoDefault ∈ OIDs.Hash.PSSSupported

    --   maskGenAlgo : Option OID m
    --   saltLength : Option Int sl
    --   -- default 20
    --   trailer    : Option Int t
    --   -- if present, must be equal to 1

-- module Param where
--   RSA : @0 List UInt8 → Set
--   RSA = Option Null

--   DSA : @0 List UInt8 → Set
--   DSA bs = Erased (bs ≡ [])

--   ECDSA : @0 List UInt8 → Set
--   ECDSA bs = Erased (bs ≡ [])


-- data SignAlgParam : ∀ {@0 bs} → @0 OID bs → Set where
--   rsa : ∀ {@0 bs bsₚ} → (@0 o : OID bs) → @0 OID.Prefix OID.RSA.RSA o → {!!} → SignAlgParam o

-- record SignAlgFields (@0 bs : List UInt8) : Set where
--   constructor mkSignAlgFields
--   field
--     @0 {o p} : List UInt8
--     signOID : OID o
--     param : Option (NotEmpty OctetStringValue) p
--     @0 bs≡  : bs ≡ o ++ p

-- SignAlg : (@0 _ : List UInt8) → Set
-- SignAlg xs = TLV Tag.Sequence SignAlgFields xs

-- getSignAlgOIDbs : ∀ {@0 bs} → SignAlg bs → List UInt8
-- getSignAlgOIDbs = Singleton.x ∘ OID.serialize ∘ SignAlgFields.signOID ∘ TLV.val
