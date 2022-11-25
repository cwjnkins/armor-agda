{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.TCB where

open Aeres.Grammar.Definitions UInt8


{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
 The elliptic curve public key (an ECPoint which is an OCTET STRING) is mapped
 to a subjectPublicKey (a BIT STRING) as follows: the most significant bit of
 the OCTET STRING becomes the most significant bit of the BIT STRING, and the
 least significant bit of the OCTET STRING becomes the least significant bit
 of the BIT STRING. Note that this octet string may represent an elliptic
 curve point in compressed or uncompressed form. Implementations that support
 elliptic curve according to this specification MUST support the uncompressed
 form and MAY support the compressed form.
-}


-- TODO: it would be nicer to say "BitString such that unused bits is 0"
ECBitString : @0 List UInt8 → Set
ECBitString = BitString ×ₚ (Erased ∘ TLV Tag.BitString (&ₚ (_≡ [ # 0 ]) OctetStringValue))
