{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.Properties
import      Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Basis.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Alg: EC: ECPKParameters: ECParameters: FieldID: CharTwo: Basis"

parseParameters : ∀ n {@0 bs} (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (BasisParameters o) n)
parseParameters n o =
  case (-, TLV.val o) ∈? OIDs.Supported
  ret (λ o∈? → Parser (Logging ∘ Dec) (ExactLength (BasisParameters' o o∈?) n))
  of λ where
    (no ¬p) → mkParser $ λ xs → do
      tell $ here' String.++ ": unsupported OID: " String.++ show (map (map toℕ) (Raw.to RawOID o))
      return ∘ no $ λ ()
    (yes (here px)) →
      parseExactLength TLV.nosubstrings (tell $ here' String.++ ": GNBasis: could not parse null parameter") parseNull _
    (yes (there (here px))) →
      parseExactLength TLV.nosubstrings (tell $ here' String.++ ": TPBasis: could not parse parameter") Int.parse _
    (yes (there (there (here px)))) →
      parseExactLength (Seq.nosubstrings TLV.nosubstrings (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings))
        (tell $ here' String.++ ": PPBasis: could not parse parameter")
        (parse& TLV.nosubstrings Int.parse (parse& TLV.nosubstrings Int.parse Int.parse))
        _

parse : ∀ n → Parser (Logging ∘ Dec) (ExactLength BasisFields n)
parse = DefinedByOID.parseFields here' parseParameters
