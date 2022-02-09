{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.RDN
open import Aeres.Data.X509.Decidable.SequenceOf
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

  parseFullName = parseTLV Tag.A0 "full name" _ parseGeneralNamesElems

  parseNameRTCrlIssuer : Parser _ (Logging ∘ Dec) X509.NameRTCrlIssuer
  parseNameRTCrlIssuer =
    parseTLV Tag.A1 "RT CRL issuer" _
      (λ n → parseBoundedSequenceOf "RDNSeq" _ Props.TLV.nonempty Props.TLV.nonnesting parseRDNATV n 1)

  parseDistPointNameChoice : Parser _ (Logging ∘ Dec) X509.DistPointNameChoice
  parseDistPointNameChoice =
    parseEquivalent _ Props.DistPointNameChoice.equivalent
      (parseSum _ parseFullName parseNameRTCrlIssuer)

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



-- private
--   module Test where

--     val₁ : List Dig --- DispointNameChoice == FullName
--     val₁ = # 48 ∷ # 49 ∷ # 160 ∷ # 47 ∷ # 160 ∷ # 45 ∷ # 134 ∷ # 43 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 115 ∷ # 46 ∷ # 112 ∷ # 107 ∷ # 105 ∷ # 46 ∷ # 103 ∷ # 111 ∷ # 111 ∷ # 103 ∷ # 47 ∷ # 103 ∷ # 116 ∷ # 115 ∷ # 49 ∷ # 99 ∷ # 51 ∷ # 47 ∷ # 122 ∷ # 100 ∷ # 65 ∷ # 84 ∷ # 116 ∷ # 48 ∷ # 69 ∷ # 120 ∷ # 95 ∷ # 70 ∷ # 107 ∷ # 46 ∷ # 99 ∷ # 114 ∷ [ # 108 ]

--     val₂ : List Dig --- DispointNameChoice == NameRelativeToCRLIssuer
--     val₂ = # 48 ∷ # 101 ∷ # 160 ∷ # 99 ∷ # 161 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ [ # 50 ]

--     val₃ : List Dig --- Reasons
--     val₃ = # 48 ∷ # 4 ∷ # 129 ∷ # 2 ∷ # 5 ∷ [ # 160 ]

--     val₄ : List Dig --- CRLIssuer
--     val₄ = # 48 ∷ # 51 ∷ # 162 ∷ # 49 ∷ # 134 ∷ # 47 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 51 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 67 ∷ # 65 ∷ # 71 ∷ # 50 ∷ # 46 ∷ # 99 ∷ # 114 ∷ [ # 108 ]

--     val₅ : List Dig --- none
--     val₅ = # 48 ∷ [ # 0 ]

--     test₁ : X509.DistPoint val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseDistPoint val₁)} tt)

--     test₂ : X509.DistPoint val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseDistPoint val₂)} tt)

--     test₃ : X509.DistPoint val₃
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseDistPoint val₃)} tt)

--     test₄ : X509.DistPoint val₄
--     test₄ = Success.value (toWitness {Q = Logging.val (runParser parseDistPoint val₄)} tt)

--     test₅ : X509.DistPoint val₅
--     test₅ = Success.value (toWitness {Q = Logging.val (runParser parseDistPoint val₅)} tt)
