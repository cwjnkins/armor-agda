{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.Extension
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.PublicKey
open import Aeres.Data.X509.Decidable.RDN
open import Aeres.Data.X509.Decidable.SignAlg
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Decidable.Validity
open import Aeres.Data.X509.Decidable.Version
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.TBSCert where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

module parseTBSCert where
  here' = "parseTBSCert"

  parseTBSCertFields : ExactLengthParser _ (Logging ∘ Dec) X509.TBSCertFields
  parseTBSCertFields n =
    parseEquivalent _ (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ Props.TBSCertFields.equivalent))
      (parse&ᵈ _
        (withinLength-nonnesting (NonNesting.noconfusion-option&₁ Props.TLV.nonnesting Props.TLV.nonnesting (Props.TLV.noconfusion λ ())))
        (withinLength-unambiguous (Unambiguous.unambiguous-option₁&₁ (Props.TLV.unambiguous (TLV.unambiguous Props.Primitives.IntegerValue.unambiguous)) Props.TLV.nonnesting (Props.TLV.unambiguous Props.Primitives.IntegerValue.unambiguous) Props.TLV.nonnesting (Props.TLV.noconfusion λ ())))
        (parseOption₁&₁≤ _ parseVersion parseInt Props.TLV.nonnesting Props.TLV.nonnesting (TLV.noconfusion (λ ())) overflow n)
        λ where
          {bs} (singleton read read≡) _ →
            subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
              (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.SignAlgFields.unambiguous))
                  (parse≤ _ (n - read) parseSignAlg Props.TLV.nonnesting overflow)
                    λ where
                      {bs₁} (singleton r₁ r₁≡) _ →
                        subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - x))) r₁≡
                          (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                            (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous Props.RDNSeq.unambiguous)
                              (parse≤ _ (n - read - r₁) parseRDNSeq Props.TLV.nonnesting overflow)
                              λ {_} (singleton r₂ r₂≡) _ →
                                subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - x))) r₂≡
                                  (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                                    (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.ValidityFields.unambiguous))
                                      (parse≤ _ (n - read - r₁ - r₂) parseValidity Props.TLV.nonnesting overflow)
                                      λ where
                                        (singleton r₃ r₃≡) _ →
                                          subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - r₂ - x))) r₃≡
                                            (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                                              (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous Props.RDNSeq.unambiguous)
                                                (parse≤ _ (n - read - r₁ - r₂ - r₃) parseRDNSeq Props.TLV.nonnesting overflow)
                                                λ where
                                                  (singleton r₄ r₄≡) _ →
                                                    subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - r₂ - r₃ - x))) r₄≡
                                                      (parseEquivalent _ (symEquivalent Distribute.exactLength-&)
                                                        (parse&ᵈ _ (withinLength-nonnesting Props.TLV.nonnesting) (withinLength-unambiguous (TLV.unambiguous Props.PublicKeyFields.unambiguous))
                                                          (parse≤ _ (n - read - r₁ - r₂ - r₃ - r₄) parsePublicKey Props.TLV.nonnesting overflow)
                                                          λ where
                                                            (singleton r₅ r₅≡) _ →
                                                              subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ (n - read - r₁ - r₂ - r₃ - r₄ - x))) r₅≡
                                                                (parseOption₃ _ Props.TLV.nonnesting Props.TLV.nonnesting Props.TLV.nonnesting
                                                                  (TLV.noconfusion (λ ())) (Props.TLV.noconfusion λ ()) (Props.TLV.noconfusion λ ())
                                                                  parseIssUID parseSubUID parseExtensions (tell $ here' String.++ ": underflow") (n - read - r₁ - r₂ - r₃ - r₄ - r₅)) )))))))))))
    where
    overflow : Logging (Level.Lift _ ⊤)
    overflow = tell $ here' String.++ ": overflow"

  parseTBSCert : Parser _ (Logging ∘ Dec) X509.TBSCert
  parseTBSCert = parseTLV _ "TBS cert." _ parseTBSCertFields

open parseTBSCert public using (parseTBSCert)


private
  module Test where

    val₁ : List Dig
    val₁ = # 48 ∷ # 130 ∷ # 2 ∷ # 118 ∷ # 160 ∷ # 3 ∷ # 2 ∷ # 1 ∷ # 2 ∷ # 2 ∷ # 16 ∷ # 3 ∷ # 58 ∷ # 241 ∷ # 230 ∷ # 167 ∷ # 17 ∷ # 169 ∷ # 160 ∷ # 187 ∷ # 40 ∷ # 100 ∷ # 177 ∷ # 29 ∷ # 9 ∷ # 250 ∷ # 229 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 11 ∷ # 5 ∷ # 0 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 30 ∷ # 23 ∷ # 13 ∷ # 49 ∷ # 51 ∷ # 48 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 23 ∷ # 13 ∷ # 51 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 53 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 34 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ # 0 ∷ # 3 ∷ # 130 ∷ # 1 ∷ # 15 ∷ # 0 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 10 ∷ # 2 ∷ # 130 ∷ # 1 ∷ # 1 ∷ # 0 ∷ # 187 ∷ # 55 ∷ # 205 ∷ # 52 ∷ # 220 ∷ # 123 ∷ # 107 ∷ # 201 ∷ # 178 ∷ # 104 ∷ # 144 ∷ # 173 ∷ # 74 ∷ # 117 ∷ # 255 ∷ # 70 ∷ # 186 ∷ # 33 ∷ # 10 ∷ # 8 ∷ # 141 ∷ # 245 ∷ # 25 ∷ # 84 ∷ # 201 ∷ # 251 ∷ # 136 ∷ # 219 ∷ # 243 ∷ # 174 ∷ # 242 ∷ # 58 ∷ # 137 ∷ # 145 ∷ # 60 ∷ # 122 ∷ # 230 ∷ # 171 ∷ # 6 ∷ # 26 ∷ # 107 ∷ # 207 ∷ # 172 ∷ # 45 ∷ # 232 ∷ # 94 ∷ # 9 ∷ # 36 ∷ # 68 ∷ # 186 ∷ # 98 ∷ # 154 ∷ # 126 ∷ # 214 ∷ # 163 ∷ # 168 ∷ # 126 ∷ # 224 ∷ # 84 ∷ # 117 ∷ # 32 ∷ # 5 ∷ # 172 ∷ # 80 ∷ # 183 ∷ # 156 ∷ # 99 ∷ # 26 ∷ # 108 ∷ # 48 ∷ # 220 ∷ # 218 ∷ # 31 ∷ # 25 ∷ # 177 ∷ # 215 ∷ # 30 ∷ # 222 ∷ # 253 ∷ # 215 ∷ # 224 ∷ # 203 ∷ # 148 ∷ # 131 ∷ # 55 ∷ # 174 ∷ # 236 ∷ # 31 ∷ # 67 ∷ # 78 ∷ # 221 ∷ # 123 ∷ # 44 ∷ # 210 ∷ # 189 ∷ # 46 ∷ # 165 ∷ # 47 ∷ # 228 ∷ # 169 ∷ # 184 ∷ # 173 ∷ # 58 ∷ # 212 ∷ # 153 ∷ # 164 ∷ # 182 ∷ # 37 ∷ # 233 ∷ # 155 ∷ # 107 ∷ # 0 ∷ # 96 ∷ # 146 ∷ # 96 ∷ # 255 ∷ # 79 ∷ # 33 ∷ # 73 ∷ # 24 ∷ # 247 ∷ # 103 ∷ # 144 ∷ # 171 ∷ # 97 ∷ # 6 ∷ # 156 ∷ # 143 ∷ # 242 ∷ # 186 ∷ # 233 ∷ # 180 ∷ # 233 ∷ # 146 ∷ # 50 ∷ # 107 ∷ # 181 ∷ # 243 ∷ # 87 ∷ # 232 ∷ # 93 ∷ # 27 ∷ # 205 ∷ # 140 ∷ # 29 ∷ # 171 ∷ # 149 ∷ # 4 ∷ # 149 ∷ # 73 ∷ # 243 ∷ # 53 ∷ # 45 ∷ # 150 ∷ # 227 ∷ # 73 ∷ # 109 ∷ # 221 ∷ # 119 ∷ # 227 ∷ # 251 ∷ # 73 ∷ # 75 ∷ # 180 ∷ # 172 ∷ # 85 ∷ # 7 ∷ # 169 ∷ # 143 ∷ # 149 ∷ # 179 ∷ # 180 ∷ # 35 ∷ # 187 ∷ # 76 ∷ # 109 ∷ # 69 ∷ # 240 ∷ # 246 ∷ # 169 ∷ # 178 ∷ # 149 ∷ # 48 ∷ # 180 ∷ # 253 ∷ # 76 ∷ # 85 ∷ # 140 ∷ # 39 ∷ # 74 ∷ # 87 ∷ # 20 ∷ # 124 ∷ # 130 ∷ # 157 ∷ # 205 ∷ # 115 ∷ # 146 ∷ # 211 ∷ # 22 ∷ # 74 ∷ # 6 ∷ # 12 ∷ # 140 ∷ # 80 ∷ # 209 ∷ # 143 ∷ # 30 ∷ # 9 ∷ # 190 ∷ # 23 ∷ # 161 ∷ # 230 ∷ # 33 ∷ # 202 ∷ # 253 ∷ # 131 ∷ # 229 ∷ # 16 ∷ # 188 ∷ # 131 ∷ # 165 ∷ # 10 ∷ # 196 ∷ # 103 ∷ # 40 ∷ # 246 ∷ # 115 ∷ # 20 ∷ # 20 ∷ # 61 ∷ # 70 ∷ # 118 ∷ # 195 ∷ # 135 ∷ # 20 ∷ # 137 ∷ # 33 ∷ # 52 ∷ # 77 ∷ # 175 ∷ # 15 ∷ # 69 ∷ # 12 ∷ # 166 ∷ # 73 ∷ # 161 ∷ # 186 ∷ # 187 ∷ # 156 ∷ # 197 ∷ # 177 ∷ # 51 ∷ # 131 ∷ # 41 ∷ # 133 ∷ # 2 ∷ # 3 ∷ # 1 ∷ # 0 ∷ # 1 ∷ # 163 ∷ # 66 ∷ # 48 ∷ # 64 ∷ # 48 ∷ # 15 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ # 19 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 4 ∷ # 5 ∷ # 48 ∷ # 3 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 48 ∷ # 14 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ # 15 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 1 ∷ # 134 ∷ # 48 ∷ # 29 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ # 14 ∷ # 4 ∷ # 22 ∷ # 4 ∷ # 20 ∷ # 78 ∷ # 34 ∷ # 84 ∷ # 32 ∷ # 24 ∷ # 149 ∷ # 230 ∷ # 227 ∷ # 110 ∷ # 230 ∷ # 15 ∷ # 250 ∷ # 250 ∷ # 185 ∷ # 18 ∷ # 237 ∷ # 6 ∷ # 23 ∷ # 143 ∷ [ # 57 ]

    val₂ : List Dig -- wrong order
    val₂ = # 48 ∷ # 130 ∷ # 2 ∷ # 118 ∷ # 160 ∷ # 3 ∷ # 2 ∷ # 1 ∷ # 2 ∷ # 2 ∷ # 16 ∷ # 3 ∷ # 58 ∷ # 241 ∷ # 230 ∷ # 167 ∷ # 17 ∷ # 169 ∷ # 160 ∷ # 187 ∷ # 40 ∷ # 100 ∷ # 177 ∷ # 29 ∷ # 9 ∷ # 250 ∷ # 229 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 30 ∷ # 23 ∷ # 13 ∷ # 49 ∷ # 51 ∷ # 48 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 23 ∷ # 13 ∷ # 51 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 53 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 11 ∷ # 5 ∷ # 0 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 34 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ # 0 ∷ # 3 ∷ # 130 ∷ # 1 ∷ # 15 ∷ # 0 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 10 ∷ # 2 ∷ # 130 ∷ # 1 ∷ # 1 ∷ # 0 ∷ # 187 ∷ # 55 ∷ # 205 ∷ # 52 ∷ # 220 ∷ # 123 ∷ # 107 ∷ # 201 ∷ # 178 ∷ # 104 ∷ # 144 ∷ # 173 ∷ # 74 ∷ # 117 ∷ # 255 ∷ # 70 ∷ # 186 ∷ # 33 ∷ # 10 ∷ # 8 ∷ # 141 ∷ # 245 ∷ # 25 ∷ # 84 ∷ # 201 ∷ # 251 ∷ # 136 ∷ # 219 ∷ # 243 ∷ # 174 ∷ # 242 ∷ # 58 ∷ # 137 ∷ # 145 ∷ # 60 ∷ # 122 ∷ # 230 ∷ # 171 ∷ # 6 ∷ # 26 ∷ # 107 ∷ # 207 ∷ # 172 ∷ # 45 ∷ # 232 ∷ # 94 ∷ # 9 ∷ # 36 ∷ # 68 ∷ # 186 ∷ # 98 ∷ # 154 ∷ # 126 ∷ # 214 ∷ # 163 ∷ # 168 ∷ # 126 ∷ # 224 ∷ # 84 ∷ # 117 ∷ # 32 ∷ # 5 ∷ # 172 ∷ # 80 ∷ # 183 ∷ # 156 ∷ # 99 ∷ # 26 ∷ # 108 ∷ # 48 ∷ # 220 ∷ # 218 ∷ # 31 ∷ # 25 ∷ # 177 ∷ # 215 ∷ # 30 ∷ # 222 ∷ # 253 ∷ # 215 ∷ # 224 ∷ # 203 ∷ # 148 ∷ # 131 ∷ # 55 ∷ # 174 ∷ # 236 ∷ # 31 ∷ # 67 ∷ # 78 ∷ # 221 ∷ # 123 ∷ # 44 ∷ # 210 ∷ # 189 ∷ # 46 ∷ # 165 ∷ # 47 ∷ # 228 ∷ # 169 ∷ # 184 ∷ # 173 ∷ # 58 ∷ # 212 ∷ # 153 ∷ # 164 ∷ # 182 ∷ # 37 ∷ # 233 ∷ # 155 ∷ # 107 ∷ # 0 ∷ # 96 ∷ # 146 ∷ # 96 ∷ # 255 ∷ # 79 ∷ # 33 ∷ # 73 ∷ # 24 ∷ # 247 ∷ # 103 ∷ # 144 ∷ # 171 ∷ # 97 ∷ # 6 ∷ # 156 ∷ # 143 ∷ # 242 ∷ # 186 ∷ # 233 ∷ # 180 ∷ # 233 ∷ # 146 ∷ # 50 ∷ # 107 ∷ # 181 ∷ # 243 ∷ # 87 ∷ # 232 ∷ # 93 ∷ # 27 ∷ # 205 ∷ # 140 ∷ # 29 ∷ # 171 ∷ # 149 ∷ # 4 ∷ # 149 ∷ # 73 ∷ # 243 ∷ # 53 ∷ # 45 ∷ # 150 ∷ # 227 ∷ # 73 ∷ # 109 ∷ # 221 ∷ # 119 ∷ # 227 ∷ # 251 ∷ # 73 ∷ # 75 ∷ # 180 ∷ # 172 ∷ # 85 ∷ # 7 ∷ # 169 ∷ # 143 ∷ # 149 ∷ # 179 ∷ # 180 ∷ # 35 ∷ # 187 ∷ # 76 ∷ # 109 ∷ # 69 ∷ # 240 ∷ # 246 ∷ # 169 ∷ # 178 ∷ # 149 ∷ # 48 ∷ # 180 ∷ # 253 ∷ # 76 ∷ # 85 ∷ # 140 ∷ # 39 ∷ # 74 ∷ # 87 ∷ # 20 ∷ # 124 ∷ # 130 ∷ # 157 ∷ # 205 ∷ # 115 ∷ # 146 ∷ # 211 ∷ # 22 ∷ # 74 ∷ # 6 ∷ # 12 ∷ # 140 ∷ # 80 ∷ # 209 ∷ # 143 ∷ # 30 ∷ # 9 ∷ # 190 ∷ # 23 ∷ # 161 ∷ # 230 ∷ # 33 ∷ # 202 ∷ # 253 ∷ # 131 ∷ # 229 ∷ # 16 ∷ # 188 ∷ # 131 ∷ # 165 ∷ # 10 ∷ # 196 ∷ # 103 ∷ # 40 ∷ # 246 ∷ # 115 ∷ # 20 ∷ # 20 ∷ # 61 ∷ # 70 ∷ # 118 ∷ # 195 ∷ # 135 ∷ # 20 ∷ # 137 ∷ # 33 ∷ # 52 ∷ # 77 ∷ # 175 ∷ # 15 ∷ # 69 ∷ # 12 ∷ # 166 ∷ # 73 ∷ # 161 ∷ # 186 ∷ # 187 ∷ # 156 ∷ # 197 ∷ # 177 ∷ # 51 ∷ # 131 ∷ # 41 ∷ # 133 ∷ # 2 ∷ # 3 ∷ # 1 ∷ # 0 ∷ # 1 ∷ # 163 ∷ # 66 ∷ # 48 ∷ # 64 ∷ # 48 ∷ # 15 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ # 19 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 4 ∷ # 5 ∷ # 48 ∷ # 3 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 48 ∷ # 14 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ # 15 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 1 ∷ # 134 ∷ # 48 ∷ # 29 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 29 ∷ # 14 ∷ # 4 ∷ # 22 ∷ # 4 ∷ # 20 ∷ # 78 ∷ # 34 ∷ # 84 ∷ # 32 ∷ # 24 ∷ # 149 ∷ # 230 ∷ # 227 ∷ # 110 ∷ # 230 ∷ # 15 ∷ # 250 ∷ # 250 ∷ # 185 ∷ # 18 ∷ # 237 ∷ # 6 ∷ # 23 ∷ # 143 ∷ [ # 57 ]

    val₃ : List Dig -- no extensions
    val₃ = # 48 ∷ # 130 ∷ # 2 ∷ # 50 ∷ # 160 ∷ # 3 ∷ # 2 ∷ # 1 ∷ # 2 ∷ # 2 ∷ # 16 ∷ # 3 ∷ # 58 ∷ # 241 ∷ # 230 ∷ # 167 ∷ # 17 ∷ # 169 ∷ # 160 ∷ # 187 ∷ # 40 ∷ # 100 ∷ # 177 ∷ # 29 ∷ # 9 ∷ # 250 ∷ # 229 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 11 ∷ # 5 ∷ # 0 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 30 ∷ # 23 ∷ # 13 ∷ # 49 ∷ # 51 ∷ # 48 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 23 ∷ # 13 ∷ # 51 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 53 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 34 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ # 0 ∷ # 3 ∷ # 130 ∷ # 1 ∷ # 15 ∷ # 0 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 10 ∷ # 2 ∷ # 130 ∷ # 1 ∷ # 1 ∷ # 0 ∷ # 187 ∷ # 55 ∷ # 205 ∷ # 52 ∷ # 220 ∷ # 123 ∷ # 107 ∷ # 201 ∷ # 178 ∷ # 104 ∷ # 144 ∷ # 173 ∷ # 74 ∷ # 117 ∷ # 255 ∷ # 70 ∷ # 186 ∷ # 33 ∷ # 10 ∷ # 8 ∷ # 141 ∷ # 245 ∷ # 25 ∷ # 84 ∷ # 201 ∷ # 251 ∷ # 136 ∷ # 219 ∷ # 243 ∷ # 174 ∷ # 242 ∷ # 58 ∷ # 137 ∷ # 145 ∷ # 60 ∷ # 122 ∷ # 230 ∷ # 171 ∷ # 6 ∷ # 26 ∷ # 107 ∷ # 207 ∷ # 172 ∷ # 45 ∷ # 232 ∷ # 94 ∷ # 9 ∷ # 36 ∷ # 68 ∷ # 186 ∷ # 98 ∷ # 154 ∷ # 126 ∷ # 214 ∷ # 163 ∷ # 168 ∷ # 126 ∷ # 224 ∷ # 84 ∷ # 117 ∷ # 32 ∷ # 5 ∷ # 172 ∷ # 80 ∷ # 183 ∷ # 156 ∷ # 99 ∷ # 26 ∷ # 108 ∷ # 48 ∷ # 220 ∷ # 218 ∷ # 31 ∷ # 25 ∷ # 177 ∷ # 215 ∷ # 30 ∷ # 222 ∷ # 253 ∷ # 215 ∷ # 224 ∷ # 203 ∷ # 148 ∷ # 131 ∷ # 55 ∷ # 174 ∷ # 236 ∷ # 31 ∷ # 67 ∷ # 78 ∷ # 221 ∷ # 123 ∷ # 44 ∷ # 210 ∷ # 189 ∷ # 46 ∷ # 165 ∷ # 47 ∷ # 228 ∷ # 169 ∷ # 184 ∷ # 173 ∷ # 58 ∷ # 212 ∷ # 153 ∷ # 164 ∷ # 182 ∷ # 37 ∷ # 233 ∷ # 155 ∷ # 107 ∷ # 0 ∷ # 96 ∷ # 146 ∷ # 96 ∷ # 255 ∷ # 79 ∷ # 33 ∷ # 73 ∷ # 24 ∷ # 247 ∷ # 103 ∷ # 144 ∷ # 171 ∷ # 97 ∷ # 6 ∷ # 156 ∷ # 143 ∷ # 242 ∷ # 186 ∷ # 233 ∷ # 180 ∷ # 233 ∷ # 146 ∷ # 50 ∷ # 107 ∷ # 181 ∷ # 243 ∷ # 87 ∷ # 232 ∷ # 93 ∷ # 27 ∷ # 205 ∷ # 140 ∷ # 29 ∷ # 171 ∷ # 149 ∷ # 4 ∷ # 149 ∷ # 73 ∷ # 243 ∷ # 53 ∷ # 45 ∷ # 150 ∷ # 227 ∷ # 73 ∷ # 109 ∷ # 221 ∷ # 119 ∷ # 227 ∷ # 251 ∷ # 73 ∷ # 75 ∷ # 180 ∷ # 172 ∷ # 85 ∷ # 7 ∷ # 169 ∷ # 143 ∷ # 149 ∷ # 179 ∷ # 180 ∷ # 35 ∷ # 187 ∷ # 76 ∷ # 109 ∷ # 69 ∷ # 240 ∷ # 246 ∷ # 169 ∷ # 178 ∷ # 149 ∷ # 48 ∷ # 180 ∷ # 253 ∷ # 76 ∷ # 85 ∷ # 140 ∷ # 39 ∷ # 74 ∷ # 87 ∷ # 20 ∷ # 124 ∷ # 130 ∷ # 157 ∷ # 205 ∷ # 115 ∷ # 146 ∷ # 211 ∷ # 22 ∷ # 74 ∷ # 6 ∷ # 12 ∷ # 140 ∷ # 80 ∷ # 209 ∷ # 143 ∷ # 30 ∷ # 9 ∷ # 190 ∷ # 23 ∷ # 161 ∷ # 230 ∷ # 33 ∷ # 202 ∷ # 253 ∷ # 131 ∷ # 229 ∷ # 16 ∷ # 188 ∷ # 131 ∷ # 165 ∷ # 10 ∷ # 196 ∷ # 103 ∷ # 40 ∷ # 246 ∷ # 115 ∷ # 20 ∷ # 20 ∷ # 61 ∷ # 70 ∷ # 118 ∷ # 195 ∷ # 135 ∷ # 20 ∷ # 137 ∷ # 33 ∷ # 52 ∷ # 77 ∷ # 175 ∷ # 15 ∷ # 69 ∷ # 12 ∷ # 166 ∷ # 73 ∷ # 161 ∷ # 186 ∷ # 187 ∷ # 156 ∷ # 197 ∷ # 177 ∷ # 51 ∷ # 131 ∷ # 41 ∷ # 133 ∷ # 2 ∷ # 3 ∷ # 1 ∷ # 0 ∷ [ # 1 ]

    val₄ : List Dig -- no extesnions, no version
    val₄ = # 48 ∷ # 130 ∷ # 2 ∷ # 45 ∷ # 2 ∷ # 16 ∷ # 3 ∷ # 58 ∷ # 241 ∷ # 230 ∷ # 167 ∷ # 17 ∷ # 169 ∷ # 160 ∷ # 187 ∷ # 40 ∷ # 100 ∷ # 177 ∷ # 29 ∷ # 9 ∷ # 250 ∷ # 229 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 11 ∷ # 5 ∷ # 0 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 30 ∷ # 23 ∷ # 13 ∷ # 49 ∷ # 51 ∷ # 48 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 23 ∷ # 13 ∷ # 51 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 53 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 34 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ # 0 ∷ # 3 ∷ # 130 ∷ # 1 ∷ # 15 ∷ # 0 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 10 ∷ # 2 ∷ # 130 ∷ # 1 ∷ # 1 ∷ # 0 ∷ # 187 ∷ # 55 ∷ # 205 ∷ # 52 ∷ # 220 ∷ # 123 ∷ # 107 ∷ # 201 ∷ # 178 ∷ # 104 ∷ # 144 ∷ # 173 ∷ # 74 ∷ # 117 ∷ # 255 ∷ # 70 ∷ # 186 ∷ # 33 ∷ # 10 ∷ # 8 ∷ # 141 ∷ # 245 ∷ # 25 ∷ # 84 ∷ # 201 ∷ # 251 ∷ # 136 ∷ # 219 ∷ # 243 ∷ # 174 ∷ # 242 ∷ # 58 ∷ # 137 ∷ # 145 ∷ # 60 ∷ # 122 ∷ # 230 ∷ # 171 ∷ # 6 ∷ # 26 ∷ # 107 ∷ # 207 ∷ # 172 ∷ # 45 ∷ # 232 ∷ # 94 ∷ # 9 ∷ # 36 ∷ # 68 ∷ # 186 ∷ # 98 ∷ # 154 ∷ # 126 ∷ # 214 ∷ # 163 ∷ # 168 ∷ # 126 ∷ # 224 ∷ # 84 ∷ # 117 ∷ # 32 ∷ # 5 ∷ # 172 ∷ # 80 ∷ # 183 ∷ # 156 ∷ # 99 ∷ # 26 ∷ # 108 ∷ # 48 ∷ # 220 ∷ # 218 ∷ # 31 ∷ # 25 ∷ # 177 ∷ # 215 ∷ # 30 ∷ # 222 ∷ # 253 ∷ # 215 ∷ # 224 ∷ # 203 ∷ # 148 ∷ # 131 ∷ # 55 ∷ # 174 ∷ # 236 ∷ # 31 ∷ # 67 ∷ # 78 ∷ # 221 ∷ # 123 ∷ # 44 ∷ # 210 ∷ # 189 ∷ # 46 ∷ # 165 ∷ # 47 ∷ # 228 ∷ # 169 ∷ # 184 ∷ # 173 ∷ # 58 ∷ # 212 ∷ # 153 ∷ # 164 ∷ # 182 ∷ # 37 ∷ # 233 ∷ # 155 ∷ # 107 ∷ # 0 ∷ # 96 ∷ # 146 ∷ # 96 ∷ # 255 ∷ # 79 ∷ # 33 ∷ # 73 ∷ # 24 ∷ # 247 ∷ # 103 ∷ # 144 ∷ # 171 ∷ # 97 ∷ # 6 ∷ # 156 ∷ # 143 ∷ # 242 ∷ # 186 ∷ # 233 ∷ # 180 ∷ # 233 ∷ # 146 ∷ # 50 ∷ # 107 ∷ # 181 ∷ # 243 ∷ # 87 ∷ # 232 ∷ # 93 ∷ # 27 ∷ # 205 ∷ # 140 ∷ # 29 ∷ # 171 ∷ # 149 ∷ # 4 ∷ # 149 ∷ # 73 ∷ # 243 ∷ # 53 ∷ # 45 ∷ # 150 ∷ # 227 ∷ # 73 ∷ # 109 ∷ # 221 ∷ # 119 ∷ # 227 ∷ # 251 ∷ # 73 ∷ # 75 ∷ # 180 ∷ # 172 ∷ # 85 ∷ # 7 ∷ # 169 ∷ # 143 ∷ # 149 ∷ # 179 ∷ # 180 ∷ # 35 ∷ # 187 ∷ # 76 ∷ # 109 ∷ # 69 ∷ # 240 ∷ # 246 ∷ # 169 ∷ # 178 ∷ # 149 ∷ # 48 ∷ # 180 ∷ # 253 ∷ # 76 ∷ # 85 ∷ # 140 ∷ # 39 ∷ # 74 ∷ # 87 ∷ # 20 ∷ # 124 ∷ # 130 ∷ # 157 ∷ # 205 ∷ # 115 ∷ # 146 ∷ # 211 ∷ # 22 ∷ # 74 ∷ # 6 ∷ # 12 ∷ # 140 ∷ # 80 ∷ # 209 ∷ # 143 ∷ # 30 ∷ # 9 ∷ # 190 ∷ # 23 ∷ # 161 ∷ # 230 ∷ # 33 ∷ # 202 ∷ # 253 ∷ # 131 ∷ # 229 ∷ # 16 ∷ # 188 ∷ # 131 ∷ # 165 ∷ # 10 ∷ # 196 ∷ # 103 ∷ # 40 ∷ # 246 ∷ # 115 ∷ # 20 ∷ # 20 ∷ # 61 ∷ # 70 ∷ # 118 ∷ # 195 ∷ # 135 ∷ # 20 ∷ # 137 ∷ # 33 ∷ # 52 ∷ # 77 ∷ # 175 ∷ # 15 ∷ # 69 ∷ # 12 ∷ # 166 ∷ # 73 ∷ # 161 ∷ # 186 ∷ # 187 ∷ # 156 ∷ # 197 ∷ # 177 ∷ # 51 ∷ # 131 ∷ # 41 ∷ # 133 ∷ # 2 ∷ # 3 ∷ # 1 ∷ # 0 ∷ [ # 1 ]

    val₅ : List Dig -- missing signature algorithm
    val₅ = # 48 ∷ # 130 ∷ # 2 ∷ # 30 ∷ # 2 ∷ # 16 ∷ # 3 ∷ # 58 ∷ # 241 ∷ # 230 ∷ # 167 ∷ # 17 ∷ # 169 ∷ # 160 ∷ # 187 ∷ # 40 ∷ # 100 ∷ # 177 ∷ # 29 ∷ # 9 ∷ # 250 ∷ # 229 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 30 ∷ # 23 ∷ # 13 ∷ # 49 ∷ # 51 ∷ # 48 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 23 ∷ # 13 ∷ # 51 ∷ # 56 ∷ # 48 ∷ # 49 ∷ # 49 ∷ # 53 ∷ # 49 ∷ # 50 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 48 ∷ # 90 ∷ # 48 ∷ # 97 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 21 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 10 ∷ # 19 ∷ # 12 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 73 ∷ # 110 ∷ # 99 ∷ # 49 ∷ # 25 ∷ # 48 ∷ # 23 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 11 ∷ # 19 ∷ # 16 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 49 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 3 ∷ # 19 ∷ # 23 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 32 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 32 ∷ # 71 ∷ # 50 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 34 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ # 0 ∷ # 3 ∷ # 130 ∷ # 1 ∷ # 15 ∷ # 0 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 10 ∷ # 2 ∷ # 130 ∷ # 1 ∷ # 1 ∷ # 0 ∷ # 187 ∷ # 55 ∷ # 205 ∷ # 52 ∷ # 220 ∷ # 123 ∷ # 107 ∷ # 201 ∷ # 178 ∷ # 104 ∷ # 144 ∷ # 173 ∷ # 74 ∷ # 117 ∷ # 255 ∷ # 70 ∷ # 186 ∷ # 33 ∷ # 10 ∷ # 8 ∷ # 141 ∷ # 245 ∷ # 25 ∷ # 84 ∷ # 201 ∷ # 251 ∷ # 136 ∷ # 219 ∷ # 243 ∷ # 174 ∷ # 242 ∷ # 58 ∷ # 137 ∷ # 145 ∷ # 60 ∷ # 122 ∷ # 230 ∷ # 171 ∷ # 6 ∷ # 26 ∷ # 107 ∷ # 207 ∷ # 172 ∷ # 45 ∷ # 232 ∷ # 94 ∷ # 9 ∷ # 36 ∷ # 68 ∷ # 186 ∷ # 98 ∷ # 154 ∷ # 126 ∷ # 214 ∷ # 163 ∷ # 168 ∷ # 126 ∷ # 224 ∷ # 84 ∷ # 117 ∷ # 32 ∷ # 5 ∷ # 172 ∷ # 80 ∷ # 183 ∷ # 156 ∷ # 99 ∷ # 26 ∷ # 108 ∷ # 48 ∷ # 220 ∷ # 218 ∷ # 31 ∷ # 25 ∷ # 177 ∷ # 215 ∷ # 30 ∷ # 222 ∷ # 253 ∷ # 215 ∷ # 224 ∷ # 203 ∷ # 148 ∷ # 131 ∷ # 55 ∷ # 174 ∷ # 236 ∷ # 31 ∷ # 67 ∷ # 78 ∷ # 221 ∷ # 123 ∷ # 44 ∷ # 210 ∷ # 189 ∷ # 46 ∷ # 165 ∷ # 47 ∷ # 228 ∷ # 169 ∷ # 184 ∷ # 173 ∷ # 58 ∷ # 212 ∷ # 153 ∷ # 164 ∷ # 182 ∷ # 37 ∷ # 233 ∷ # 155 ∷ # 107 ∷ # 0 ∷ # 96 ∷ # 146 ∷ # 96 ∷ # 255 ∷ # 79 ∷ # 33 ∷ # 73 ∷ # 24 ∷ # 247 ∷ # 103 ∷ # 144 ∷ # 171 ∷ # 97 ∷ # 6 ∷ # 156 ∷ # 143 ∷ # 242 ∷ # 186 ∷ # 233 ∷ # 180 ∷ # 233 ∷ # 146 ∷ # 50 ∷ # 107 ∷ # 181 ∷ # 243 ∷ # 87 ∷ # 232 ∷ # 93 ∷ # 27 ∷ # 205 ∷ # 140 ∷ # 29 ∷ # 171 ∷ # 149 ∷ # 4 ∷ # 149 ∷ # 73 ∷ # 243 ∷ # 53 ∷ # 45 ∷ # 150 ∷ # 227 ∷ # 73 ∷ # 109 ∷ # 221 ∷ # 119 ∷ # 227 ∷ # 251 ∷ # 73 ∷ # 75 ∷ # 180 ∷ # 172 ∷ # 85 ∷ # 7 ∷ # 169 ∷ # 143 ∷ # 149 ∷ # 179 ∷ # 180 ∷ # 35 ∷ # 187 ∷ # 76 ∷ # 109 ∷ # 69 ∷ # 240 ∷ # 246 ∷ # 169 ∷ # 178 ∷ # 149 ∷ # 48 ∷ # 180 ∷ # 253 ∷ # 76 ∷ # 85 ∷ # 140 ∷ # 39 ∷ # 74 ∷ # 87 ∷ # 20 ∷ # 124 ∷ # 130 ∷ # 157 ∷ # 205 ∷ # 115 ∷ # 146 ∷ # 211 ∷ # 22 ∷ # 74 ∷ # 6 ∷ # 12 ∷ # 140 ∷ # 80 ∷ # 209 ∷ # 143 ∷ # 30 ∷ # 9 ∷ # 190 ∷ # 23 ∷ # 161 ∷ # 230 ∷ # 33 ∷ # 202 ∷ # 253 ∷ # 131 ∷ # 229 ∷ # 16 ∷ # 188 ∷ # 131 ∷ # 165 ∷ # 10 ∷ # 196 ∷ # 103 ∷ # 40 ∷ # 246 ∷ # 115 ∷ # 20 ∷ # 20 ∷ # 61 ∷ # 70 ∷ # 118 ∷ # 195 ∷ # 135 ∷ # 20 ∷ # 137 ∷ # 33 ∷ # 52 ∷ # 77 ∷ # 175 ∷ # 15 ∷ # 69 ∷ # 12 ∷ # 166 ∷ # 73 ∷ # 161 ∷ # 186 ∷ # 187 ∷ # 156 ∷ # 197 ∷ # 177 ∷ # 51 ∷ # 131 ∷ # 41 ∷ # 133 ∷ # 2 ∷ # 3 ∷ # 1 ∷ # 0 ∷ [ # 1 ]

    test₁ : X509.TBSCert val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseTBSCert val₁)} tt)

    test₂ : ¬ Success _ X509.TBSCert val₂
    test₂ = toWitnessFalse {Q = Logging.val (runParser parseTBSCert val₂)} tt

    test₃ : X509.TBSCert val₃
    test₃ = Success.value (toWitness {Q = Logging.val (runParser parseTBSCert val₃)} tt)

    test₄ : X509.TBSCert val₄
    test₄ = Success.value (toWitness {Q = Logging.val (runParser parseTBSCert val₄)} tt)

    test₅ : ¬ Success _ X509.TBSCert val₅
    test₅ = toWitnessFalse {Q = Logging.val (runParser parseTBSCert val₅)} tt
