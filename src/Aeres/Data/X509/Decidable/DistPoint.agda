{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.TLV
import      Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.DistPoint where

open Base256

module parseDistPoint where
  here' = "parseDistPoint"

  postulate
    parseDistPointNameChoice : Parser _ (Logging ∘ Dec) X509.DistPointNameChoice

  parseDistPointFields : ∀ n → Parser _ (Logging ∘ Dec) (ExactLength _ X509.DistPointFields n)
  parseDistPointFields n =
    parseEquivalent _
      (equivalent×ₚ _ Props.DistPointFields.equivalent)
      (parseOption₃ _ Props.TLV.nonnesting Props.TLV.nonnesting Props.TLV.nonnesting
        (Props.TLV.noconfusion (λ where ())) (Props.TLV.noconfusion (λ where ())) (Props.TLV.noconfusion (λ where ()))
        (parseTLV Tag.A0 "dist. point name" X509.DistPointNameChoice
          (parseExactLength _ Props.DistPointNameChoice.nonnesting
            (tell $ "parseDistPoint: name choice: underflow")
            parseDistPointNameChoice))
        (parseTLV Tag.EightyOne "reason flags" _ parseBitstringValue)
        (parseTLV Tag.A2 "CRL issuer" X509.GeneralNamesElems
          parseGeneralNamesElems)
        (tell $ here' String.++ ": failed")
        n)

  parseDistPoint : Parser _ (Logging ∘ Dec) X509.DistPoint
  parseDistPoint =
    parseTLV _ "dist point" _ parseDistPointFields

open parseDistPoint public using (parseDistPoint)