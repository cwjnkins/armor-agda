{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB.OIDs
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Seq.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Seq.TCB                  UInt8
open Aeres.Grammar.Sum.TCB                  UInt8

{- https://datatracker.ietf.org/doc/html/rfc3279#section-2.3.5
-- The object identifier id-characteristic-two-basis specifies an arc
-- containing the object identifiers for each type of basis for the
-- characteristic-two finite fields.  It has the following value:
--
--    id-characteristic-two-basis OBJECT IDENTIFIER ::= {
--         characteristic-two-field basisType(1) }
--
-- The object identifiers gnBasis, tpBasis and ppBasis name the three
-- kinds of basis for characteristic-two finite fields defined by
-- [X9.62].  They have the following values:
--
--    gnBasis OBJECT IDENTIFIER ::= { id-characteristic-two-basis 1 }
--
--    -- for gnBasis, the value of the parameters field is NULL
--
--    tpBasis OBJECT IDENTIFIER ::= { id-characteristic-two-basis 2 }
--
--    -- type of parameters field for tpBasis is Trinomial
--
--    Trinomial ::= INTEGER
--
--    ppBasis OBJECT IDENTIFIER ::= { id-characteristic-two-basis 3 }
--
--    -- type of parameters field for ppBasis is Pentanomial
--
--    Pentanomial ::= SEQUENCE {
--       k1  INTEGER,
--       k2  INTEGER,
--       k3  INTEGER }
-}

Pentanomial   = &ₚ Int (&ₚ Int Int)

RawPentanomial : Raw Pentanomial
RawPentanomial = Raw&ₚ RawInt (Raw&ₚ RawInt RawInt)

BasisParameters' : ∀ {@0 bs₁} → (o : OID bs₁) → Dec ((-, TLV.val o) ∈ Supported) → @0 List UInt8 → Set
BasisParameters' o (no ¬p) = λ _ → ⊥
BasisParameters' o (yes (here px)) = Null
BasisParameters' o (yes (there (here px))) = Int
BasisParameters' o (yes (there (there (here px)))) = Pentanomial

BasisParameters : AnyDefinedByOID
BasisParameters o bs = BasisParameters' o ((-, TLV.val o) ∈? Supported) bs

RawBasisParameters : Raw₁ RawOID BasisParameters
toRawBasisParameters
  : ∀ {@0 bs} (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ Supported)) →
    ∀ {@0 bs'} → BasisParameters' o o∈? bs' → Raw₁.D RawBasisParameters (Raw.to RawOID o)

Raw₁.D RawBasisParameters o = Raw.D (RawSum RawNull (RawSum RawInt RawPentanomial))
Raw₁.to RawBasisParameters o = toRawBasisParameters o ((-, TLV.val o) ∈? Supported)

toRawBasisParameters o (yes (here px)) p = inj₁ (Raw.to RawNull p)
toRawBasisParameters o (yes (there (here px))) p = inj₂ (inj₁ (Raw.to RawInt p))
toRawBasisParameters o (yes (there (there (here px)))) p = inj₂ (inj₂ (Raw.to RawPentanomial p))

BasisFields : @0 List UInt8 → Set
BasisFields = DefinedByOIDFields BasisParameters

RawBasisFields : Raw BasisFields
RawBasisFields = RawDefinedByOIDFields RawBasisParameters
