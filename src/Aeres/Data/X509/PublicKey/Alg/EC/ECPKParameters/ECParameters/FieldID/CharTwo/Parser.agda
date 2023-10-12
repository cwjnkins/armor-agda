{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Basis
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Properties
open import Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.ECPKParameters.ECParameters.FieldID.CharTwo.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Alg: EC: ECPKParameters: ECParameters: FieldID: CharTwo"

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength CharTwoFields n)
parseFields n =
  parseEquivalent equiv
     (parse&ᵈ
       (Parallel.nosubstrings₁ TLV.nosubstrings)
       (Parallel.Length≤.unambiguous _ Int.unambiguous)
       (parse≤ n Int.parse TLV.nosubstrings (tell $ here' String.++ ": length overflow"))
       λ where
         {bs} (singleton r r≡) m →
           subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength BasisFields (n - x))) r≡
             (Basis.parse (n - r)))
  where
  equiv : Equivalent (&ₚᵈ (Length≤ _ _) (λ {bs₁} _ → ExactLength BasisFields (n - length bs₁))) (ExactLength CharTwoFields n)
  equiv = Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁{A₁ = CharTwoFieldsRep}{A₂ = CharTwoFields} equivalent)

parse : Parser (Logging ∘ Dec) CharTwo
parse = parseTLV _ here' _ parseFields
