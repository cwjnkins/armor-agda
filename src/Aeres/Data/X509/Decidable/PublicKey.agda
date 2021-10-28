{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.SignAlg
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.PublicKey where

open Base256

module parsePublicKeyFields where
  here' = "parsePublicKeyFields"

  open ≡-Reasoning

  parsePublicKeyFields : Parser Dig (Logging ∘ Dec) X509.PublicKeyFields
  runParser parsePublicKeyFields xs = do
    yes r ← runParser (parse& _ Props.TLV.nonnesting parseSignAlg parseBitstring) xs
      where no ¬parse → do
        tell here'
        return ∘ no $ λ where
          r →
            contradiction
              (mapSuccess _ (λ where (X509.mkPublicKeyFields signalg pubkey bs≡) → mk&ₚ signalg pubkey bs≡) r)
              ¬parse
    return (yes
      (mapSuccess _ (λ where (mk&ₚ fstₚ₁ sndₚ₁ bs≡) → X509.mkPublicKeyFields fstₚ₁ sndₚ₁ bs≡) r))

open parsePublicKeyFields public using (parsePublicKeyFields)

parsePublicKey : Parser Dig (Logging ∘ Dec) X509.PublicKey
parsePublicKey =
  parseTLV _ "publick key" _
    (parseExactLength _ Props.PublicKeyFields.nonnesting (tell "public key: length mismatch") parsePublicKeyFields)


private
  module Test where

    Pk₁ : List Dig
    Pk₁ = Tag.Sequence ∷ # 130 ∷ # 1 ∷ # 34 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ # 0 ∷ # 3 ∷ # 130 ∷ # 1 ∷ # 15 ∷ # 0 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 10 ∷ # 2 ∷ # 130 ∷ # 1 ∷ # 1 ∷ # 0 ∷ # 237 ∷ # 38 ∷ # 152 ∷ # 205 ∷ # 78 ∷ # 152 ∷ # 104 ∷ # 248 ∷ # 211 ∷ # 90 ∷ # 79 ∷ # 230 ∷ # 18 ∷ # 95 ∷ # 220 ∷ # 113 ∷ # 251 ∷ # 182 ∷ # 189 ∷ # 226 ∷ # 141 ∷ # 242 ∷ # 5 ∷ # 235 ∷ # 135 ∷ # 222 ∷ # 239 ∷ # 254 ∷ # 19 ∷ # 122 ∷ # 237 ∷ # 55 ∷ # 1 ∷ # 47 ∷ # 87 ∷ # 110 ∷ # 116 ∷ # 125 ∷ # 228 ∷ # 39 ∷ # 245 ∷ # 167 ∷ # 212 ∷ # 208 ∷ # 70 ∷ # 101 ∷ # 123 ∷ # 63 ∷ # 238 ∷ # 93 ∷ # 29 ∷ # 185 ∷ # 75 ∷ # 210 ∷ # 98 ∷ # 49 ∷ # 212 ∷ # 148 ∷ # 42 ∷ # 28 ∷ # 248 ∷ # 8 ∷ # 107 ∷ # 167 ∷ # 41 ∷ # 246 ∷ # 47 ∷ # 147 ∷ # 71 ∷ # 4 ∷ # 253 ∷ # 1 ∷ # 75 ∷ # 252 ∷ # 82 ∷ # 120 ∷ # 53 ∷ # 105 ∷ # 116 ∷ # 223 ∷ # 177 ∷ # 98 ∷ # 46 ∷ # 189 ∷ # 6 ∷ # 96 ∷ # 180 ∷ # 55 ∷ # 215 ∷ # 132 ∷ # 9 ∷ # 188 ∷ # 65 ∷ # 231 ∷ # 134 ∷ # 131 ∷ # 145 ∷ # 30 ∷ # 84 ∷ # 251 ∷ # 48 ∷ # 127 ∷ # 87 ∷ # 7 ∷ # 198 ∷ # 132 ∷ # 124 ∷ # 222 ∷ # 163 ∷ # 175 ∷ # 103 ∷ # 113 ∷ # 153 ∷ # 49 ∷ # 87 ∷ # 224 ∷ # 217 ∷ # 182 ∷ # 1 ∷ # 107 ∷ # 165 ∷ # 107 ∷ # 113 ∷ # 23 ∷ # 233 ∷ # 255 ∷ # 253 ∷ # 49 ∷ # 181 ∷ # 213 ∷ # 106 ∷ # 37 ∷ # 109 ∷ # 167 ∷ # 150 ∷ # 226 ∷ # 153 ∷ # 149 ∷ # 77 ∷ # 213 ∷ # 212 ∷ # 230 ∷ # 202 ∷ # 156 ∷ # 198 ∷ # 232 ∷ # 98 ∷ # 55 ∷ # 138 ∷ # 153 ∷ # 3 ∷ # 57 ∷ # 249 ∷ # 204 ∷ # 170 ∷ # 138 ∷ # 165 ∷ # 64 ∷ # 80 ∷ # 233 ∷ # 216 ∷ # 85 ∷ # 167 ∷ # 103 ∷ # 114 ∷ # 106 ∷ # 44 ∷ # 128 ∷ # 227 ∷ # 86 ∷ # 88 ∷ # 248 ∷ # 24 ∷ # 188 ∷ # 1 ∷ # 165 ∷ # 26 ∷ # 30 ∷ # 135 ∷ # 198 ∷ # 216 ∷ # 157 ∷ # 230 ∷ # 30 ∷ # 136 ∷ # 114 ∷ # 66 ∷ # 33 ∷ # 128 ∷ # 153 ∷ # 83 ∷ # 192 ∷ # 198 ∷ # 202 ∷ # 17 ∷ # 89 ∷ # 48 ∷ # 100 ∷ # 236 ∷ # 203 ∷ # 231 ∷ # 72 ∷ # 20 ∷ # 83 ∷ # 91 ∷ # 231 ∷ # 155 ∷ # 183 ∷ # 243 ∷ # 137 ∷ # 188 ∷ # 200 ∷ # 17 ∷ # 194 ∷ # 139 ∷ # 106 ∷ # 194 ∷ # 121 ∷ # 136 ∷ # 227 ∷ # 12 ∷ # 48 ∷ # 195 ∷ # 109 ∷ # 187 ∷ # 3 ∷ # 226 ∷ # 167 ∷ # 94 ∷ # 204 ∷ # 40 ∷ # 53 ∷ # 205 ∷ # 71 ∷ # 45 ∷ # 60 ∷ # 72 ∷ # 217 ∷ # 192 ∷ # 128 ∷ # 211 ∷ # 50 ∷ # 60 ∷ # 146 ∷ # 196 ∷ # 147 ∷ # 57 ∷ # 55 ∷ # 153 ∷ # 128 ∷ # 174 ∷ # 39 ∷ # 16 ∷ # 230 ∷ # 179 ∷ # 12 ∷ # 2 ∷ # 3 ∷ # 1 ∷ # 0 ∷ [ # 1 ]

    -- this is an example of non-RSA public key (ECDSA). Its success depends on fixing signAlg "param" for non-RSA case
    Pk₂ : List Dig
    Pk₂ = Tag.Sequence ∷ # 89 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 7 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 2 ∷ # 1 ∷ # 6 ∷ # 8 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 3 ∷ # 1 ∷ # 7 ∷ # 3 ∷ # 66 ∷ # 0 ∷ # 4 ∷ # 39 ∷ # 173 ∷ # 175 ∷ # 236 ∷ # 195 ∷ # 224 ∷ # 229 ∷ # 106 ∷ # 154 ∷ # 247 ∷ # 15 ∷ # 228 ∷ # 123 ∷ # 204 ∷ # 162 ∷ # 63 ∷ # 91 ∷ # 37 ∷ # 11 ∷ # 160 ∷ # 185 ∷ # 35 ∷ # 138 ∷ # 44 ∷ # 56 ∷ # 199 ∷ # 118 ∷ # 23 ∷ # 180 ∷ # 169 ∷ # 242 ∷ # 252 ∷ # 9 ∷ # 243 ∷ # 2 ∷ # 174 ∷ # 194 ∷ # 163 ∷ # 108 ∷ # 152 ∷ # 136 ∷ # 140 ∷ # 243 ∷ # 79 ∷ # 196 ∷ # 250 ∷ # 59 ∷ # 184 ∷ # 87 ∷ # 66 ∷ # 178 ∷ # 197 ∷ # 187 ∷ # 78 ∷ # 45 ∷ # 118 ∷ # 161 ∷ # 247 ∷ # 94 ∷ # 66 ∷ # 247 ∷ # 141 ∷ # 188 ∷ [ # 49 ]

    test₁ : X509.PublicKey Pk₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parsePublicKey Pk₁)} tt)

    -- test₂ : X509.PublicKey Pk₂
    -- test₂ = Success.value (toWitness {Q = Logging.val (runParser parsePublicKey Pk₂)} tt)
