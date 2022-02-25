{-# OPTIONS --subtyping #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open import Aeres.Data.UTF8.TCB

module Aeres.Data.X509.Semantic.StringPrep where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig


-- StringPrepCompare : ∀ {@0 bs₁ bs₂} → X509.DirectoryString bs₁ → X509.DirectoryString bs₂ → Set
-- StringPrepCompare a@(X509.teletexString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.printableString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.utf8String x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.teletexString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.printableString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.printableString x) b@(X509.printableString x₁) = {!!}
-- StringPrepCompare a@(X509.printableString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.printableString x) b@(X509.utf8String x₁) = {!!}
-- StringPrepCompare a@(X509.printableString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.printableString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.utf8String x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.universalString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.utf8String x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.utf8String x) b@(X509.printableString x₁) = {!!}
-- StringPrepCompare a@(X509.utf8String x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.utf8String x) b@(X509.utf8String x₁) = {!!}
-- StringPrepCompare a@(X509.utf8String x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.teletexString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.printableString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.universalString x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.utf8String x₁) = _≋_ {A = X509.DirectoryString} a b
-- StringPrepCompare a@(X509.bmpString x) b@(X509.bmpString x₁) = _≋_ {A = X509.DirectoryString} a b


-- Transcode : ∀ {@0 bs} → X509.DirectoryString bs → List Dig
-- Transcode (X509.teletexString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = {!!}
-- Transcode (X509.printableString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = x
-- Transcode (X509.universalString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = {!!}
-- Transcode (X509.utf8String (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = x
-- Transcode (X509.bmpString (Aeres.Grammar.Definitions.mk×ₚ (Generic.mkTLV len (singleton x x≡) len≡ bs≡₁) sndₚ₁ bs≡)) = {!!}


-- record MappingResult (_ : Bool) (_ : List Dig)  : Set where
--   constructor mkMappingResult
--   field
--     fst : Bool
--     snd : List Dig
-- open MappingResult

-- getMappedList : ∀ {@0 a b} → MappingResult a b → List Dig
-- getMappedList (mkMappingResult fst₁ snd₁) = snd₁

-- MapOneByte : Dig → List Dig
-- MapOneByte x
--   with toℕ x ≟ 65
-- ... | yes p =  [ # 97 ]
-- ... | no ¬p
--   with toℕ x ≟ 66
-- ... | yes p =  [ # 98 ]
-- ... | no ¬p = []




-- MapTwoByte : Dig → Dig → List Dig
-- MapTwoByte x x₁
--   with toℕ x ∷ [ toℕ x₁ ] ≟ 194 ∷ [ 181 ]
-- ... | yes p = # 206 ∷ # 188 ∷ []
-- ... | no ¬p
--   with toℕ x ∷ [ toℕ x₁ ] ≟ 195 ∷ [ 128 ]
-- ... | yes p = # 195 ∷ # 160 ∷ []
-- ... | no ¬p = []

-- MapThreeByte : Dig → Dig → Dig → List Dig
-- MapThreeByte x x₁ x₂
--   with toℕ x ∷ toℕ x₁ ∷ [ toℕ x₂ ] ≟ 225 ∷ 184 ∷ [ 183 ] 
-- ... | yes p = # 225 ∷ # 184 ∷ # 129 ∷ []
-- ... | no ¬p
--   with toℕ x ∷ toℕ x₁ ∷ [ toℕ x₂ ] ≟ 225 ∷ 184 ∷ [ 184 ]
-- ... | yes p = # 225 ∷ # 184 ∷ # 131 ∷ []
-- ... | no ¬p = []

-- MapFourByte : Dig → Dig → Dig → Dig → List Dig
-- MapFourByte x x₁ x₂ x₃
--   with toℕ x ∷ toℕ x₁ ∷ toℕ x₂ ∷ [ toℕ x₃ ] ≟ 240 ∷ 135 ∷ 240 ∷ [ 144 ]
-- ... | yes p = # 240 ∷ # 144 ∷ # 144 ∷ # 168 ∷ []
-- ... | no ¬p
--   with toℕ x ∷ toℕ x₁ ∷ toℕ x₂ ∷ [ toℕ x₃ ] ≟ 240 ∷ 240 ∷ 135 ∷ 240 ∷ [ 145 ]
-- ... | yes p = # 240 ∷ # 144 ∷ # 144 ∷ # 169 ∷ []
-- ... | no ¬p = []


-- Mapping : List Dig → List Dig
-- Mapping [] = []
-- Mapping (x ∷ x₁)
--   with MapOneByte x
-- Mapping (x ∷ []) | [] = []
-- Mapping (x ∷ []) | x' = x'
-- Mapping (x ∷ x₁ ∷ x₂) | []
--   with MapTwoByte x x₁
-- Mapping (x ∷ x₁ ∷ []) | [] | [] = []
-- Mapping (x ∷ x₁ ∷ []) | [] | x'' = x''
-- Mapping (x ∷ x₁ ∷ x₂ ∷ x₃) | [] | []
--   with MapThreeByte x x₁ x₂
-- Mapping (x ∷ x₁ ∷ x₂ ∷ []) | [] | [] | [] = []
-- Mapping (x ∷ x₁ ∷ x₂ ∷ []) | [] | [] | x''' = x'''
-- Mapping (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄) | [] | [] | []
--   with MapFourByte x x₁ x₂ x₃
-- ... | [] = []
-- ... | x'''' = x'''' ++ Mapping x₄
-- Mapping (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄) | [] | [] | x''' = x''' ++ Mapping (x₃ ∷ x₄)
-- Mapping (x ∷ x₁ ∷ x₂ ∷ x₃) | [] | x'' = x'' ++ Mapping (x₂ ∷ x₃)
-- Mapping (x ∷ x₁ ∷ x₂) | x' =  x' ++ Mapping (x₁ ∷ x₂)





mapUTF8Char1 : ∀ {@0 bs} → UTF8Char1 bs → Exists─ (List Dig) UTF8Char
mapUTF8Char1 (mkUTF8Char1 b1 b1range refl) =
  case (toℕ b1 ≟ 65) of λ where
    (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 97) (toWitness {Q = 97 <? 128} tt) refl)
    (no ¬p) →
      case (toℕ b1 ≟ 66) of λ where
        (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 98) (toWitness {Q = 98 <? 128} tt) refl)
        (no ¬p) →
          case (toℕ b1 ≟ 67) of λ where
            (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 99) (toWitness {Q = 99 <? 128} tt) refl)
            (no ¬p) →
              case (toℕ b1 ≟ 68) of λ where
                (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 100) (toWitness {Q = 100 <? 128} tt) refl)
                (no ¬p) →
                  case (toℕ b1 ≟ 69) of λ where
                    (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 101) (toWitness {Q = 101 <? 128} tt) refl)
                    (no ¬p) →
                      case (toℕ b1 ≟ 70) of λ where
                        (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 102) (toWitness {Q = 102 <? 128} tt) refl)
                        (no ¬p) →
                          case (toℕ b1 ≟ 71) of λ where
                            (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 103) (toWitness {Q = 103 <? 128} tt) refl)
                            (no ¬p) →
                              case (toℕ b1 ≟ 72) of λ where
                                (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 104) (toWitness {Q = 104 <? 128} tt) refl)
                                (no ¬p) →
                                  case (toℕ b1 ≟ 73) of λ where
                                    (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 105) (toWitness {Q = 105 <? 128} tt) refl)
                                    (no ¬p) →
                                      case (toℕ b1 ≟ 74) of λ where
                                        (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 106) (toWitness {Q = 106 <? 128} tt) refl)
                                        (no ¬p) →
                                          case (toℕ b1 ≟ 75) of λ where
                                            (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 107) (toWitness {Q = 107 <? 128} tt) refl)
                                            (no ¬p) →
                                              case (toℕ b1 ≟ 76) of λ where
                                                (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 108) (toWitness {Q = 108 <? 128} tt) refl)
                                                (no ¬p) →
                                                  case (toℕ b1 ≟ 77) of λ where
                                                    (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 109) (toWitness {Q = 109 <? 128} tt) refl)
                                                    (no ¬p) →
                                                      case (toℕ b1 ≟ 78) of λ where
                                                        (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 110) (toWitness {Q = 110 <? 128} tt) refl)
                                                        (no ¬p) →
                                                          case (toℕ b1 ≟ 79) of λ where
                                                            (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 111) (toWitness {Q = 111 <? 128} tt) refl)
                                                            (no ¬p) →
                                                              case (toℕ b1 ≟ 80) of λ where
                                                                (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 112) (toWitness {Q = 112 <? 128} tt) refl)
                                                                (no ¬p) →
                                                                  case (toℕ b1 ≟ 81) of λ where
                                                                    (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 113) (toWitness {Q = 113 <? 128} tt) refl)
                                                                    (no ¬p) →
                                                                      case (toℕ b1 ≟ 82) of λ where
                                                                        (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 114) (toWitness {Q = 114 <? 128} tt) refl)
                                                                        (no ¬p) →
                                                                          case (toℕ b1 ≟ 83) of λ where
                                                                            (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 115) (toWitness {Q = 115 <? 128} tt) refl)
                                                                            (no ¬p) →
                                                                              case (toℕ b1 ≟ 84) of λ where
                                                                                (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 116) (toWitness {Q = 116 <? 128} tt) refl)
                                                                                (no ¬p) →
                                                                                  case (toℕ b1 ≟ 85) of λ where
                                                                                    (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 117) (toWitness {Q = 117 <? 128} tt) refl)
                                                                                    (no ¬p) →
                                                                                      case (toℕ b1 ≟ 86) of λ where
                                                                                        (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 118) (toWitness {Q = 118 <? 128} tt) refl)
                                                                                        (no ¬p) →
                                                                                          case (toℕ b1 ≟ 87) of λ where
                                                                                            (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 119) (toWitness {Q = 119 <? 128} tt) refl)
                                                                                            (no ¬p) →
                                                                                              case (toℕ b1 ≟ 88) of λ where
                                                                                                (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 120) (toWitness {Q = 120 <? 128} tt) refl)
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b1 ≟ 89) of λ where
                                                                                                    (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 121) (toWitness {Q = 121 <? 128} tt) refl)
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b1 ≟ 90) of λ where
                                                                                                        (yes p) → _ , Aeres.Grammar.Sum.inj₁ (mkUTF8Char1 (# 122) (toWitness {Q = 122 <? 128} tt) refl)
                                                                                                        (no ¬p) → {!!}




mapUTF8Char2 : ∀ {@0 bs} → UTF8Char2 bs → Exists─ (List Dig) UTF8Char
mapUTF8Char2 (mkUTF8Char2 b1 b2 b1range b2range refl) =
  case (toℕ b1 ≟ 194) of λ where
    (yes p) →
      case (toℕ b2 ≟ 181) of λ where
        (yes p) → ?
        (no ¬p) → ?
    (no ¬p) →
      case (toℕ b1 ≟ 195) of λ where
        (yes p) →
          case (toℕ b2 ≟ 128) of λ where
            (yes p) → ?
            (no ¬p) →
              case (toℕ b2 ≟ 129) of λ where
                (yes p) → ?
                (no ¬p) →
                  case (toℕ b2 ≟ 130) of λ where
                    (yes p) → ?
                    (no ¬p) →
                      case (toℕ b2 ≟ 131) of λ where
                        (yes p) → ?
                        (no ¬p) →
                          case (toℕ b2 ≟ 132) of λ where
                            (yes p) → ?
                            (no ¬p) →
                              case (toℕ b2 ≟ 133) of λ where
                                (yes p) → ?
                                (no ¬p) →
                                  case (toℕ b2 ≟ 134) of λ where
                                    (yes p) → ?
                                    (no ¬p) →
                                      case (toℕ b2 ≟ 135) of λ where
                                        (yes p) → ?
                                        (no ¬p) →
                                          case (toℕ b2 ≟ 136) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 137) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 138) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 139) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 140) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 141) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 142) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 143) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 144) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 145) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 146) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 147) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 148) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 149) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 150) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 152) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 153) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 154) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 155) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 156) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 157) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 158) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 159) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) → ?
        (no ¬p) →
          case (toℕ b1 ≟ 196) of λ where
            (yes p) →
              case (toℕ b2 ≟ 128) of λ where
                (yes p) → ?
                (no ¬p) →
                  case (toℕ b2 ≟ 130) of λ where
                    (yes p) → ?
                    (no ¬p) →
                      case (toℕ b2 ≟ 132) of λ where
                        (yes p) → ?
                        (no ¬p) →
                          case (toℕ b2 ≟ 134) of λ where
                            (yes p) → ?
                            (no ¬p) →
                              case (toℕ b2 ≟ 136) of λ where
                                (yes p) → ?
                                (no ¬p) →
                                  case (toℕ b2 ≟ 138) of λ where
                                    (yes p) → ?
                                    (no ¬p) →
                                      case (toℕ b2 ≟ 140) of λ where
                                        (yes p) → ?
                                        (no ¬p) →
                                          case (toℕ b2 ≟ 142) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 144) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 146) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 148) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 150) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 152) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 154) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 156) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 158) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 160) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 162) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 164) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 166) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 168) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 170) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 172) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 174) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 176) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 178) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 180) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 182) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 185) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 187) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 189) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 191) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) → ?
            (no ¬p) →
              case (toℕ b1 ≟ 197) of λ where
                (yes p) →
                  case (toℕ b2 ≟ 129) of λ where
                    (yes p) → ?
                    (no ¬p) →
                      case (toℕ b2 ≟ 131) of λ where
                        (yes p) → ?
                        (no ¬p) →
                          case (toℕ b2 ≟ 133) of λ where
                            (yes p) → ?
                            (no ¬p) →
                              case (toℕ b2 ≟ 135) of λ where
                                (yes p) → ?
                                (no ¬p) →
                                  case (toℕ b2 ≟ 137) of λ where
                                    (yes p) → ?
                                    (no ¬p) →
                                      case (toℕ b2 ≟ 138) of λ where
                                        (yes p) → ?
                                        (no ¬p) →
                                          case (toℕ b2 ≟ 140) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 142) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 144) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 146) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 148) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 150) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 152) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 154) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 156) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 158) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 160) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 162) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 164) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 166) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 168) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 170) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 172) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 174) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 176) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 178) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 180) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 182) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 184) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 185) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 187) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 189) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 191) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) → ?
                (no ¬p) →
                  case (toℕ b1 ≟ 198) of λ where
                    (yes p) →
                      case (toℕ b2 ≟ 129) of λ where
                        (yes p) → ?
                        (no ¬p) →
                          case (toℕ b2 ≟ 130) of λ where
                            (yes p) → ?
                            (no ¬p) →
                              case (toℕ b2 ≟ 132) of λ where
                                (yes p) → ?
                                (no ¬p) →
                                  case (toℕ b2 ≟ 134) of λ where
                                    (yes p) → ?
                                    (no ¬p) →
                                      case (toℕ b2 ≟ 135) of λ where
                                        (yes p) → ?
                                        (no ¬p) →
                                          case (toℕ b2 ≟ 137) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 138) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 139) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 142) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 143) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 144) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 145) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 147) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 148) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 150) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 151) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 152) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 156) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 157) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 159) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 160) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 162) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 164) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 166) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 167) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 169) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 172) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 174) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 175) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 177) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 178) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 179) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 181) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) →
                                                                                                                                                          case (toℕ b2 ≟ 183) of λ where
                                                                                                                                                            (yes p) → ?
                                                                                                                                                            (no ¬p) →
                                                                                                                                                              case (toℕ b2 ≟ 184) of λ where
                                                                                                                                                                (yes p) → ?
                                                                                                                                                                (no ¬p) →
                                                                                                                                                                  case (toℕ b2 ≟ 188) of λ where
                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                    (no ¬p) → ?
                    (no ¬p) →
                      case (toℕ b1 ≟ 199) of λ where
                        (yes p) →
                          case (toℕ b2 ≟ 132) of λ where
                            (yes p) → ?
                            (no ¬p) →
                              case (toℕ b2 ≟ 133) of λ where
                                (yes p) → ?
                                (no ¬p) →
                                  case (toℕ b2 ≟ 135) of λ where
                                    (yes p) → ?
                                    (no ¬p) →
                                      case (toℕ b2 ≟ 136) of λ where
                                        (yes p) → ?
                                        (no ¬p) →
                                          case (toℕ b2 ≟ 138) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 139) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 141) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 143) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 145) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 147) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 149) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 151) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 153) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 155) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 158) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 160) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 162) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 164) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 166) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 168) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 170) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 172) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 174) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 176) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 177) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 178) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 180) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 182) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 183) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 184) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 186) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 188) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) →
                                                                                                                                                          case (toℕ b2 ≟ 190) of λ where
                                                                                                                                                            (yes p) → ?
                                                                                                                                                            (no ¬p) → ?
                        (no ¬p) →
                          case (toℕ b1 ≟ 200) of λ where
                            (yes p) →
                              case (toℕ b2 ≟ 128) of λ where
                                (yes p) → ?
                                (no ¬p) →
                                  case (toℕ b2 ≟ 130) of λ where
                                    (yes p) → ?
                                    (no ¬p) →
                                      case (toℕ b2 ≟ 132) of λ where
                                        (yes p) → ?
                                        (no ¬p) →
                                          case (toℕ b2 ≟ 134) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 136) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 138) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 140) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 142) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 144) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 146) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 148) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 150) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 152) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 154) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 156) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 158) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 160) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 162) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 164) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 166) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 168) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 170) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 172) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 174) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 176) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 178) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) → ?
                            (no ¬p) →
                              case (toℕ b1 ≟ 205) of λ where
                                (yes p) →
                                  case (toℕ b2 ≟ 133) of λ where
                                    (yes p) → ?
                                    (no ¬p) →
                                      case (toℕ b2 ≟ 186) of λ where
                                        (yes p) → ?
                                        (no ¬p) → ?
                                (no ¬p) →
                                  case (toℕ b1 ≟ 206) of λ where
                                    (yes p) →
                                      case (toℕ b2 ≟ 134) of λ where
                                        (yes p) → ?
                                        (no ¬p) →
                                          case (toℕ b2 ≟ 136) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 137) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 138) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 140) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 142) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 143) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 144) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 145) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 146) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 147) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 148) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 149) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 150) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 151) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 152) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 153) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 154) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 155) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 156) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 157) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 158) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 159) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 160) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 161) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 163) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 164) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 165) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 166) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) →
                                                                                                                                                          case (toℕ b2 ≟ 167) of λ where
                                                                                                                                                            (yes p) → ?
                                                                                                                                                            (no ¬p) →
                                                                                                                                                              case (toℕ b2 ≟ 168) of λ where
                                                                                                                                                                (yes p) → ?
                                                                                                                                                                (no ¬p) →
                                                                                                                                                                  case (toℕ b2 ≟ 169) of λ where
                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                    (no ¬p) →
                                                                                                                                                                      case (toℕ b2 ≟ 170) of λ where
                                                                                                                                                                        (yes p) → ?
                                                                                                                                                                        (no ¬p) →
                                                                                                                                                                          case (toℕ b2 ≟ 171) of λ where
                                                                                                                                                                            (yes p) → ?
                                                                                                                                                                            (no ¬p) →
                                                                                                                                                                              case (toℕ b2 ≟ 176) of λ where
                                                                                                                                                                                (yes p) → ?
                                                                                                                                                                                (no ¬p) → ?
                                    (no ¬p) →
                                      case (toℕ b1 ≟ 207) of λ where
                                        (yes p) →
                                          case (toℕ b2 ≟ 130) of λ where
                                            (yes p) → ?
                                            (no ¬p) →
                                              case (toℕ b2 ≟ 144) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 145) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 146) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 147) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 148) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 149) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 150) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 152) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 154) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 156) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 158) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 160) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 162) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 164) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 166) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 168) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 170) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 172) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 174) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 176) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 177) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 178) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 180) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 181) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) → ?
                                        (no ¬p) →
                                          case (toℕ b1 ≟ 208) of λ where
                                            (yes p) →
                                              case (toℕ b2 ≟ 128) of λ where
                                                (yes p) → ?
                                                (no ¬p) →
                                                  case (toℕ b2 ≟ 129) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 130) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 131) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 132) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 133) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 134) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 135) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 136) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 137) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 138) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 139) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 140) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 141) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 142) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 143) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 144) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 145) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 146) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 147) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 148) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 149) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 150) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 151) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 152) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 153) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 154) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) →
                                                                                                                                                          case (toℕ b2 ≟ 155) of λ where
                                                                                                                                                            (yes p) → ?
                                                                                                                                                            (no ¬p) →
                                                                                                                                                              case (toℕ b2 ≟ 156) of λ where
                                                                                                                                                                (yes p) → ?
                                                                                                                                                                (no ¬p) →
                                                                                                                                                                  case (toℕ b2 ≟ 157) of λ where
                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                    (no ¬p) →
                                                                                                                                                                      case (toℕ b2 ≟ 158) of λ where
                                                                                                                                                                        (yes p) → ?
                                                                                                                                                                        (no ¬p) →
                                                                                                                                                                          case (toℕ b2 ≟ 159) of λ where
                                                                                                                                                                            (yes p) → ?
                                                                                                                                                                            (no ¬p) →
                                                                                                                                                                              case (toℕ b2 ≟ 160) of λ where
                                                                                                                                                                                (yes p) → ?
                                                                                                                                                                                (no ¬p) →
                                                                                                                                                                                  case (toℕ b2 ≟ 161) of λ where
                                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                                    (no ¬p) →
                                                                                                                                                                                      case (toℕ b2 ≟ 162) of λ where
                                                                                                                                                                                        (yes p) → ?
                                                                                                                                                                                        (no ¬p) →
                                                                                                                                                                                          case (toℕ b2 ≟ 163) of λ where
                                                                                                                                                                                            (yes p) → ?
                                                                                                                                                                                            (no ¬p) →
                                                                                                                                                                                              case (toℕ b2 ≟ 164) of λ where
                                                                                                                                                                                                (yes p) → ?
                                                                                                                                                                                                (no ¬p) →
                                                                                                                                                                                                  case (toℕ b2 ≟ 165) of λ where
                                                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                                                    (no ¬p) →
                                                                                                                                                                                                      case (toℕ b2 ≟ 166) of λ where
                                                                                                                                                                                                        (yes p) → ?
                                                                                                                                                                                                        (no ¬p) →
                                                                                                                                                                                                          case (toℕ b2 ≟ 167) of λ where
                                                                                                                                                                                                            (yes p) → ?
                                                                                                                                                                                                            (no ¬p) →
                                                                                                                                                                                                              case (toℕ b2 ≟ 168) of λ where
                                                                                                                                                                                                                (yes p) → ?
                                                                                                                                                                                                                (no ¬p) →
                                                                                                                                                                                                                  case (toℕ b2 ≟ 169) of λ where
                                                                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                                                                    (no ¬p) →
                                                                                                                                                                                                                      case (toℕ b2 ≟ 170) of λ where
                                                                                                                                                                                                                        (yes p) → ?
                                                                                                                                                                                                                        (no ¬p) →
                                                                                                                                                                                                                          case (toℕ b2 ≟ 171) of λ where
                                                                                                                                                                                                                            (yes p) → ?
                                                                                                                                                                                                                            (no ¬p) →
                                                                                                                                                                                                                              case (toℕ b2 ≟ 172) of λ where
                                                                                                                                                                                                                                (yes p) → ?
                                                                                                                                                                                                                                (no ¬p) →
                                                                                                                                                                                                                                  case (toℕ b2 ≟ 173) of λ where
                                                                                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                                                                                    (no ¬p) →
                                                                                                                                                                                                                                      case (toℕ b2 ≟ 174) of λ where
                                                                                                                                                                                                                                        (yes p) → ?
                                                                                                                                                                                                                                        (no ¬p) →
                                                                                                                                                                                                                                          case (toℕ b2 ≟ 175) of λ where
                                                                                                                                                                                                                                            (yes p) → ?
                                                                                                                                                                                                                                            (no ¬p) → ?
                                            (no ¬p) →
                                              case (toℕ b1 ≟ 209) of λ where
                                                (yes p) →
                                                  case (toℕ b2 ≟ 160) of λ where
                                                    (yes p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b2 ≟ 162) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 164) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 166) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 168) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 170) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 172) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 174) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 176) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 178) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 180) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 182) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 184) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 186) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 188) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 190) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) → ?
                                                (no ¬p) →
                                                  case (toℕ b1 ≟ 210) of λ where
                                                    (yes p) →
                                                      case (toℕ b2 ≟ 128) of λ where
                                                        (yes p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b2 ≟ 138) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 140) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 142) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 144) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 146) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 148) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 150) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 152) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 154) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 156) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 158) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 160) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 162) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 164) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 166) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 168) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 170) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 172) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 174) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 176) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 178) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 180) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 182) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 184) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) →
                                                                                                                                                          case (toℕ b2 ≟ 186) of λ where
                                                                                                                                                            (yes p) → ?
                                                                                                                                                            (no ¬p) →
                                                                                                                                                              case (toℕ b2 ≟ 188) of λ where
                                                                                                                                                                (yes p) → ?
                                                                                                                                                                (no ¬p) →
                                                                                                                                                                  case (toℕ b2 ≟ 190) of λ where
                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                    (no ¬p) → ?
                                                    (no ¬p) →
                                                      case (toℕ b1 ≟ 211) of λ where
                                                        (yes p) →
                                                          case (toℕ b2 ≟ 129) of λ where
                                                            (yes p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b2 ≟ 131) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 133) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 135) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 137) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 139) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 141) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 144) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 146) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 148) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 150) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 152) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 154) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 156) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 158) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 160) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 162) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 164) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 166) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 168) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 170) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 172) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 174) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 176) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) →
                                                                                                                                                          case (toℕ b2 ≟ 178) of λ where
                                                                                                                                                            (yes p) → ?
                                                                                                                                                            (no ¬p) →
                                                                                                                                                              case (toℕ b2 ≟ 180) of λ where
                                                                                                                                                                (yes p) → ?
                                                                                                                                                                (no ¬p) →
                                                                                                                                                                  case (toℕ b2 ≟ 184) of λ where
                                                                                                                                                                    (yes p) → ?
                                                                                                                                                                    (no ¬p) → ?
                                                        (no ¬p) →
                                                          case (toℕ b1 ≟ 212) of λ where
                                                            (yes p) →
                                                              case (toℕ b2 ≟ 128) of λ where
                                                                (yes p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b2 ≟ 130) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 132) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 134) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 136) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 138) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 140) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 142) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 177) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 178) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 179) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 180) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 181) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 182) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 183) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 184) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 185) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 186) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 187) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 188) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 189) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 190) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 191) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) → ?
                                                            (no ¬p) →
                                                              case (toℕ b1 ≟ 213) of λ where
                                                                (yes p) →
                                                                  case (toℕ b2 ≟ 128) of λ where
                                                                    (yes p) → ?
                                                                    (no ¬p) →
                                                                      case (toℕ b2 ≟ 129) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) →
                                                                          case (toℕ b2 ≟ 130) of λ where
                                                                            (yes p) → ?
                                                                            (no ¬p) →
                                                                              case (toℕ b2 ≟ 131) of λ where
                                                                                (yes p) → ?
                                                                                (no ¬p) →
                                                                                  case (toℕ b2 ≟ 132) of λ where
                                                                                    (yes p) → ?
                                                                                    (no ¬p) →
                                                                                      case (toℕ b2 ≟ 133) of λ where
                                                                                        (yes p) → ?
                                                                                        (no ¬p) →
                                                                                          case (toℕ b2 ≟ 134) of λ where
                                                                                            (yes p) → ?
                                                                                            (no ¬p) →
                                                                                              case (toℕ b2 ≟ 135) of λ where
                                                                                                (yes p) → ?
                                                                                                (no ¬p) →
                                                                                                  case (toℕ b2 ≟ 136) of λ where
                                                                                                    (yes p) → ?
                                                                                                    (no ¬p) →
                                                                                                      case (toℕ b2 ≟ 137) of λ where
                                                                                                        (yes p) → ?
                                                                                                        (no ¬p) →
                                                                                                          case (toℕ b2 ≟ 138) of λ where
                                                                                                            (yes p) → ?
                                                                                                            (no ¬p) →
                                                                                                              case (toℕ b2 ≟ 139) of λ where
                                                                                                                (yes p) → ?
                                                                                                                (no ¬p) →
                                                                                                                  case (toℕ b2 ≟ 140) of λ where
                                                                                                                    (yes p) → ?
                                                                                                                    (no ¬p) →
                                                                                                                      case (toℕ b2 ≟ 141) of λ where
                                                                                                                        (yes p) → ?
                                                                                                                        (no ¬p) →
                                                                                                                          case (toℕ b2 ≟ 142) of λ where
                                                                                                                            (yes p) → ?
                                                                                                                            (no ¬p) →
                                                                                                                              case (toℕ b2 ≟ 143) of λ where
                                                                                                                                (yes p) → ?
                                                                                                                                (no ¬p) →
                                                                                                                                  case (toℕ b2 ≟ 144) of λ where
                                                                                                                                    (yes p) → ?
                                                                                                                                    (no ¬p) →
                                                                                                                                      case (toℕ b2 ≟ 145) of λ where
                                                                                                                                        (yes p) → ?
                                                                                                                                        (no ¬p) →
                                                                                                                                          case (toℕ b2 ≟ 146) of λ where
                                                                                                                                            (yes p) → ?
                                                                                                                                            (no ¬p) →
                                                                                                                                              case (toℕ b2 ≟ 147) of λ where
                                                                                                                                                (yes p) → ?
                                                                                                                                                (no ¬p) →
                                                                                                                                                  case (toℕ b2 ≟ 148) of λ where
                                                                                                                                                    (yes p) → ?
                                                                                                                                                    (no ¬p) →
                                                                                                                                                      case (toℕ b2 ≟ 149) of λ where
                                                                                                                                                        (yes p) → ?
                                                                                                                                                        (no ¬p) →
                                                                                                                                                          case (toℕ b2 ≟ 150) of λ where
                                                                                                                                                            (yes p) → ?
                                                                                                                                                            (no ¬p) → ?
                                                                (no ¬p) →
                                                                  case (toℕ b1 ≟ 214) of λ where
                                                                    (yes p) →
                                                                      case (toℕ b2 ≟ 135) of λ where
                                                                        (yes p) → ?
                                                                        (no ¬p) → ?
