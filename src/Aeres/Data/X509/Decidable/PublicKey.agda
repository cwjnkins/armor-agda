{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.SignAlg
open import Aeres.Data.X509.Properties as Props
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.PublicKey where


open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

module parsePublicKeyFields where
  here' = "parsePublicKeyFields"

  open ≡-Reasoning

  parseCurveFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.CurveFields n)
  parseCurveFields n =
    parseEquivalent (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ Props.CurveFields.equivalent))
      (parse&ᵈ (withinLength-nonnesting (NonNesting&ₚ TLV.nonnesting  TLV.nonnesting))
        (withinLength-unambiguous (unambiguous&ₚ (TLV.unambiguous Props.OctetstringValue.unambiguous) TLV.nonnesting (TLV.unambiguous Props.OctetstringValue.unambiguous)))
          (parse≤ n (parse& TLV.nonnesting  parseOctetString parseOctetString) (NonNesting&ₚ TLV.nonnesting TLV.nonnesting) ((tell $ here' String.++ ": overflow")))
          λ where
            {bs} (singleton read read≡) _ →
              subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
                (parseOption₁ExactLength TLV.nonempty TLV.nonnesting (tell $ here' String.++ ": underflow") parseBitstring (n - read)))

  parseCurve : Parser (Logging ∘ Dec) X509.Curve
  parseCurve = parseTLV _ "Curve" _ parseCurveFields

  parseFieldID :  Parser (Logging ∘ Dec) X509.FieldID
  parseFieldID = parseTLV _ "Field ID" _ parseOctetStringValue

  parseEcParamsFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.EcParamsFields n)
  parseEcParamsFields n = parseEquivalent (transEquivalent (symEquivalent Distribute.exactLength-&)  (equivalent×ₚ Props.EcParamsFields.equivalent))
    (parse&ᵈ 
      (withinLength-nonnesting
        (NonNesting&ₚ
          (NonNesting&ₚ
            (NonNesting&ₚ
              (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting)
              TLV.nonnesting)
            TLV.nonnesting)
          TLV.nonnesting))
      (withinLength-unambiguous
        (unambiguous&ₚ
          (unambiguous&ₚ
            (unambiguous&ₚ
              (unambiguous&ₚ (λ where refl refl → refl) (λ where _ refl refl → refl)
                (TLV.unambiguous Props.OctetstringValue.unambiguous))
              (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting)
              (TLV.unambiguous Props.CurveFields.unambiguous))
            (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting)
            (TLV.unambiguous Props.OctetstringValue.unambiguous))
          (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting)
          (TLV.unambiguous λ{xs} → Int.unambiguous{xs})))
        (parse≤ n (parse& (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting)
          (parse& (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting)
            (parse& (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting)
              (parse& (λ where _ refl refl → refl) (parseLit (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") (# 2 ∷ # 1 ∷ [ # 1 ]))
              parseFieldID) parseCurve) parseOctetString) parseInt)
          (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting) (tell $ here' String.++ ": overflow"))
        λ where
          {bs} (singleton read read≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n - x))) read≡
              (parseOption₁ExactLength TLV.nonempty TLV.nonnesting (tell $ here' String.++ ": underflow") parseInt (n - read)))

  parseEcParams :  Parser (Logging ∘ Dec) X509.EcParams
  parseEcParams = parseTLV _ "EC params" _ parseEcParamsFields

  parseEcPkAlgParams : Parser (Logging ∘ Dec) X509.EcPkAlgParams
  runParser parseEcPkAlgParams xs = do
    no ¬ecparams ← runParser parseEcParams xs
      where yes p → return (yes (mapSuccess (λ x → X509.ecparams x) p))
    no ¬namedcurve ← runParser parseOID xs
      where yes q → return (yes (mapSuccess (λ x → X509.namedcurve x) q))
    no ¬impca ← runParser (parseLit (tell $ here' String.++ ": exp null : underflow")
      (tell $ here' String.++ ": exp null: mismatch") X509.ExpNull) xs
      where yes r → return (yes (mapSuccess (λ {bs} x → X509.implicitlyCA{bs} x ) r))
    return ∘ no $ λ where
     (success prefix read read≡ (X509.ecparams x) suffix ps≡) →
       contradiction (success _ _ read≡ x _ ps≡) ¬ecparams
     (success prefix read read≡ (X509.namedcurve x) suffix ps≡) →
       contradiction (success _ _ read≡ x _ ps≡) ¬namedcurve
     (success prefix read read≡ (X509.implicitlyCA x) suffix ps≡) →
       contradiction (success _ _ read≡ x _ ps≡) ¬impca

  parseEcPkAlgFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.EcPkAlgFields n)
  parseEcPkAlgFields n =
    parseExactLength Props.EcPkAlgFields.nonnesting (tell $ here' String.++ ": underflow")
      (parseEquivalent Props.EcPkAlgFields.equivalent
        (parse& (λ ≡xys a₁ a₂ → trans a₁ (sym a₂))
          (parseLit (tell $ here' String.++ ": EcPKOID : underflow") (tell $ here' String.++ ": EcPKOID: mismatch") X509.PKOID.EcPk)
            parseEcPkAlgParams)) n

  parseEcPkAlg :  Parser (Logging ∘ Dec) X509.EcPkAlg
  parseEcPkAlg = parseTLV _ "Ec PK Algorithm" _ parseEcPkAlgFields

  parseRSAPkIntsFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.RSAPkIntsFields n)
  parseRSAPkIntsFields n =
    parseExactLength Props.RSAPkIntsFields.nonnesting (tell $ here' String.++ ": underflow")
      (parseEquivalent Props.RSAPkIntsFields.equivalent (parse& TLV.nonnesting parseInt parseInt)) n

  parseRSAPkInts :  Parser (Logging ∘ Dec) X509.RSAPkInts
  parseRSAPkInts = parseTLV _ "RSA pk n and e" _ parseRSAPkIntsFields

  parseRSABitStringFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.RSABitStringFields n)
  parseRSABitStringFields n =
    parseExactLength Props.RSABitStringFields.nonnesting (tell $ here' String.++ ": underflow")
      (parseEquivalent Props.RSABitStringFields.equivalent
        (parse& (λ where _ refl refl → refl)
          (parseLit 
            (tell $ here' String.++ ": zero bit : underflow") (tell $ here' String.++ ": zero bit: mismatch") [ # 0 ]) parseRSAPkInts)) n

  parseRSABitString :  Parser (Logging ∘ Dec) X509.RSABitString
  parseRSABitString = parseTLV _ "RSA BitString" _ parseRSABitStringFields

  parseRSAPkAlgFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.RSAPkAlgFields n)
  parseRSAPkAlgFields n =
    parseExactLength Props.RSAPkAlgFields.nonnesting (tell $ here' String.++ ": underflow")
      (parseEquivalent Props.RSAPkAlgFields.equivalent
        (parse& (λ ≡xys a₁ a₂ → trans a₁ (sym a₂))
          (parseLit (tell $ here' String.++ ": RSAPKOID : underflow") (tell $ here' String.++ ": RSAPKOID: mismatch") X509.PKOID.RsaEncPk)
          (parseLit (tell $ here' String.++ ": RSAPK Param: underflow") (tell $ here' String.++ ": RSAPK Param: mismatch") X509.ExpNull))) n

  parseRSAPkAlg :  Parser (Logging ∘ Dec) X509.RSAPkAlg
  parseRSAPkAlg = parseTLV _ "RSA PK Algorithm" _ parseRSAPkAlgFields

  parsePkAlg : Parser (Logging ∘ Dec) X509.PkAlg
  runParser parsePkAlg xs = do
    yes (success pre r r≡ v@(mkTLV{l = l} len (X509.SignAlg.mkSignAlgFields{o = o}{p} so par refl) len≡ refl) suf ps≡) ← runParser parseSignAlg xs
      where no ¬p → return ∘ no $ λ where
        (success prefix read read≡ (X509.PkAlg.rsapkalg x) suffix ps≡) →
          contradiction (success prefix read read≡ (PkAlg.RSAPkAlg2SignAlg x) suffix ps≡) ¬p
        (success prefix read read≡ (X509.PkAlg.ecpkalg x) suffix ps≡) →
          contradiction (success prefix read read≡ (PkAlg.EcPkAlg2SignAlg x) suffix ps≡) ¬p
        (success prefix read read≡ (X509.PkAlg.otherpkalg sa x) suffix ps≡) →
          contradiction (success prefix read read≡ sa suffix ps≡) ¬p
    case (X509.SignAlg.getSignAlgOIDbs v ∈? X509.PKOID.Supported) of λ where
      (no ¬p) → return (yes (success pre r r≡ (X509.PkAlg.otherpkalg v (fromWitnessFalse ¬p)) suf ps≡))
      (yes (here px)) → do
        yes (success pre' r' r≡' v' suf' ps≡') ← runParser parseRSAPkAlg xs
          where no ¬p → return ∘  no $ λ where
            (success prefix read read≡ (X509.PkAlg.rsapkalg x) suffix ps≡) →
              contradiction (success prefix read read≡ x suffix ps≡) ¬p
            (success prefix read read≡ (X509.PkAlg.ecpkalg v'@(mkTLV{l = l'} len' (X509.mkEcPkAlgFields{p = p'} self param refl) len≡' refl)) suffix ps≡') → ‼
              let v“ : X509.SignAlg _
                  v“ = PkAlg.EcPkAlg2SignAlg v'

                  @0 ps≡“ : pre ++ suf ≡ prefix ++ suffix
                  ps≡“ = trans ps≡ (sym ps≡')

                  @0 pre≡ : pre ≡ prefix
                  pre≡ = TLV.nonnesting ps≡“ v v“

                  @0 o++p≡ : o ++ p ≡ X509.PKOID.EcPk ++ p'
                  o++p≡ = Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) $ Length.nonnesting (∷-injectiveʳ pre≡) len len')
                            (cong (Tag.Sequence ∷_) $ begin
                              l ++ o ++ p ≡⟨ ∷-injectiveʳ pre≡ ⟩
                              l' ++ X509.PKOID.EcPk ++ p' ∎)
              in
              contradiction{P = X509.PKOID.RsaEncPk ≡  X509.PKOID.EcPk}
                (begin X509.PKOID.RsaEncPk            ≡⟨ sym px ⟩
                       X509.SignAlg.getSignAlgOIDbs v ≡⟨ Singleton.x≡ (OID.serialize so) ⟩
                       o                              ≡⟨ TLV.nonnesting o++p≡ so (toWitness{Q = isOID? X509.PKOID.EcPk} tt) ⟩
                       X509.PKOID.EcPk                ∎)
                (λ where ())
            (success prefix read read≡ (X509.PkAlg.otherpkalg sa@(mkTLV{l = l'} len' (X509.SignAlg.mkSignAlgFields{o = o'}{p'} so' _ refl) leb≡ refl) o∉) suffix ps≡') → ‼
              let @0 ps≡“ : pre ++ suf ≡ prefix ++ suffix
                  ps≡“ = trans ps≡ (sym ps≡')

                  @0 pre≡ : pre ≡ prefix
                  pre≡ = TLV.nonnesting ps≡“ v sa

                  @0 o++p≡ : o ++ p ≡ o' ++ p'
                  o++p≡ = Lemmas.++-cancel≡ˡ (_ ∷ l) (_ ∷ l')
                            (cong (Tag.Sequence ∷_) (Length.nonnesting (∷-injectiveʳ pre≡) len len'))
                            pre≡
              in
              contradiction
                (subst (_∈ X509.PKOID.Supported)
                  (begin X509.SignAlg.getSignAlgOIDbs v ≡⟨ Singleton.x≡ (OID.serialize so) ⟩
                         o ≡⟨ TLV.nonnesting o++p≡ so so' ⟩
                         o' ≡⟨ sym (Singleton.x≡ (OID.serialize so')) ⟩
                         X509.SignAlg.getSignAlgOIDbs sa ∎)
                  (here px))
                (toWitnessFalse o∉) 
        return (yes (success pre' r' r≡' (X509.PkAlg.rsapkalg v') suf' ps≡'))
      (yes (there (here px))) → do
        yes (success pre' r' r≡' v' suf' ps≡') ← runParser parseEcPkAlg xs
          where no ¬p → return ∘ no $ λ where
            (success prefix read read≡ (X509.PkAlg.rsapkalg v'@(mkTLV{l = l'} len' (X509.mkRSAPkAlgFields self (singleton p' refl) refl) len≡' refl)) suffix ps≡') → ‼
              let @0 ps≡“ : pre ++ suf ≡ prefix ++ suffix
                  ps≡“ = trans ps≡ (sym ps≡')

                  v“ : X509.SignAlg _
                  v“ = PkAlg.RSAPkAlg2SignAlg v'

                  @0 pre≡ : pre ≡ prefix
                  pre≡ = TLV.nonnesting ps≡“ v v“

                  @0 o++p≡ : o ++ p ≡ X509.PKOID.RsaEncPk ++ p'
                  o++p≡ = Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) $ Length.nonnesting (∷-injectiveʳ pre≡) len len')
                            (cong (Tag.Sequence ∷_) $ begin
                              l ++ o ++ p ≡⟨ ∷-injectiveʳ pre≡ ⟩
                              l' ++ X509.PKOID.RsaEncPk ++ p' ∎)
              in
              contradiction{P = X509.PKOID.EcPk ≡ X509.PKOID.RsaEncPk}
                (begin (X509.PKOID.EcPk ≡⟨ sym px ⟩
                       X509.SignAlg.getSignAlgOIDbs v ≡⟨ Singleton.x≡ (OID.serialize so) ⟩
                       o ≡⟨ TLV.nonnesting o++p≡ so (toWitness{Q = isOID? X509.PKOID.RsaEncPk} tt) ⟩
                       X509.PKOID.RsaEncPk ∎))
                λ where ()
            (success prefix read read≡ (X509.PkAlg.ecpkalg x) suffix ps≡) → contradiction (success prefix read read≡ x suffix ps≡) ¬p
            (success prefix read read≡ (X509.PkAlg.otherpkalg sa@(mkTLV{l = l'} len' (X509.SignAlg.mkSignAlgFields{o = o'}{p'} so' _ refl) leb≡ refl) o∉) suffix ps≡') → ‼
              let @0 ps≡“ : pre ++ suf ≡ prefix ++ suffix
                  ps≡“ = trans ps≡ (sym ps≡')

                  @0 pre≡ : pre ≡ prefix
                  pre≡ = TLV.nonnesting ps≡“ v sa

                  @0 o++p≡ : o ++ p ≡ o' ++ p'
                  o++p≡ = Lemmas.++-cancel≡ˡ (_ ∷ l) (_ ∷ l')
                            (cong (Tag.Sequence ∷_) (Length.nonnesting (∷-injectiveʳ pre≡) len len'))
                            pre≡
              in
              contradiction
                (subst (_∈ X509.PKOID.Supported)
                  (begin (X509.SignAlg.getSignAlgOIDbs v ≡⟨ Singleton.x≡ (OID.serialize so) ⟩
                         o ≡⟨ TLV.nonnesting o++p≡ so so' ⟩
                         o' ≡⟨ sym (Singleton.x≡ (OID.serialize so')) ⟩
                         X509.SignAlg.getSignAlgOIDbs sa ∎))
                  (there (here px)))
                (toWitnessFalse o∉) 
        return (yes (success pre' r' r≡' (X509.PkAlg.ecpkalg v') suf' ps≡'))

  parsePkVal : (bs : List UInt8) → Parser (Logging ∘ Dec) (X509.PkVal bs)
  runParser (parsePkVal o) xs
    with (o ≟ X509.PKOID.RsaEncPk)
  ... | yes refl = do
    no ¬rsapkbits ← runParser parseRSABitString xs
      where
        (yes (success prefix read read≡ value suffix ps≡)) →
          return (yes (success prefix read read≡ (X509.rsapkbits refl value) suffix ps≡))
    return ∘ no $ λ where
      (success prefix read read≡ (X509.rsapkbits refl x) suffix ps≡) →
        contradiction (success prefix read read≡ x suffix ps≡) ¬rsapkbits
      (success prefix read read≡ (X509.otherpkbits o∉ x) suffix ps≡) →
        contradiction{P = o ∈ X509.PKOID.Supported} (here refl) (toWitnessFalse{Q = o ∈? _} o∉)
  ... | no ¬rsa
    with (o ≟ X509.PKOID.EcPk)
  ... | yes refl = do
    no ¬ecpkbits ← runParser parseBitstring xs
      where
        (yes (success prefix read read≡ value suffix ps≡)) →
          return (yes (success prefix read read≡ (X509.ecpkbits refl value) suffix ps≡))
    return ∘ no $ λ where
      (success prefix read read≡ (X509.ecpkbits refl x) suffix ps≡) →
        contradiction (success prefix read read≡ x suffix ps≡) ¬ecpkbits
      (success prefix read read≡ (X509.otherpkbits o∉ x) suffix ps≡) →
        contradiction (success prefix read read≡ x suffix ps≡) ¬ecpkbits
  ... | no ¬ec
    with o∉
    where
    o∉ : o ∉ X509.PKOID.Supported
    o∉ (here px) = contradiction px ¬rsa
    o∉ (there (here px)) = contradiction px ¬ec
  ... | o∉ =  do
    no ¬otherpkbits ← runParser parseBitstring xs
      where
        (yes (success prefix read read≡ value suffix ps≡)) →
          return (yes (success prefix read read≡ (X509.otherpkbits (fromWitnessFalse{Q = o ∈? _} o∉) value) suffix ps≡))
    return ∘ no $ λ where
      (success prefix read read≡ (X509.rsapkbits o≡ x) suffix ps≡) → contradiction o≡ ¬rsa
      (success prefix read read≡ (X509.ecpkbits o≡ x) suffix ps≡) → contradiction o≡ ¬ec
      (success prefix read read≡ (X509.otherpkbits o∉ x) suffix ps≡) → contradiction (success prefix read read≡ x suffix ps≡) ¬otherpkbits

  parsePublicKeyFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength X509.PublicKeyFields n)
  parsePublicKeyFields n =
    parseExactLength Props.PublicKeyFields.nonnesting (tell $ here' String.++ ": underflow")
      (parseEquivalent Props.PublicKeyFields.equivalent
        (parse&ᵈ Props.PkAlg.nonnesting Props.PkAlg.unambiguous
          parsePkAlg λ x a → parsePkVal _)) n

open parsePublicKeyFields public using (parsePublicKeyFields)


parsePublicKey : Parser (Logging ∘ Dec) X509.PublicKey
parsePublicKey = parseTLV _ "Public key" _ parsePublicKeyFields

-- -------------------------------------------------------------------------------------------------------

-- -- private
-- --   module Test where

-- --     Pk₁ : List UInt8
-- --     Pk₁ = Tag.Sequence ∷ # 130 ∷ # 1 ∷ # 34 ∷ # 48 ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ # 0 ∷ # 3 ∷ # 130 ∷ # 1 ∷ # 15 ∷ # 0 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 10 ∷ # 2 ∷ # 130 ∷ # 1 ∷ # 1 ∷ # 0 ∷ # 237 ∷ # 38 ∷ # 152 ∷ # 205 ∷ # 78 ∷ # 152 ∷ # 104 ∷ # 248 ∷ # 211 ∷ # 90 ∷ # 79 ∷ # 230 ∷ # 18 ∷ # 95 ∷ # 220 ∷ # 113 ∷ # 251 ∷ # 182 ∷ # 189 ∷ # 226 ∷ # 141 ∷ # 242 ∷ # 5 ∷ # 235 ∷ # 135 ∷ # 222 ∷ # 239 ∷ # 254 ∷ # 19 ∷ # 122 ∷ # 237 ∷ # 55 ∷ # 1 ∷ # 47 ∷ # 87 ∷ # 110 ∷ # 116 ∷ # 125 ∷ # 228 ∷ # 39 ∷ # 245 ∷ # 167 ∷ # 212 ∷ # 208 ∷ # 70 ∷ # 101 ∷ # 123 ∷ # 63 ∷ # 238 ∷ # 93 ∷ # 29 ∷ # 185 ∷ # 75 ∷ # 210 ∷ # 98 ∷ # 49 ∷ # 212 ∷ # 148 ∷ # 42 ∷ # 28 ∷ # 248 ∷ # 8 ∷ # 107 ∷ # 167 ∷ # 41 ∷ # 246 ∷ # 47 ∷ # 147 ∷ # 71 ∷ # 4 ∷ # 253 ∷ # 1 ∷ # 75 ∷ # 252 ∷ # 82 ∷ # 120 ∷ # 53 ∷ # 105 ∷ # 116 ∷ # 223 ∷ # 177 ∷ # 98 ∷ # 46 ∷ # 189 ∷ # 6 ∷ # 96 ∷ # 180 ∷ # 55 ∷ # 215 ∷ # 132 ∷ # 9 ∷ # 188 ∷ # 65 ∷ # 231 ∷ # 134 ∷ # 131 ∷ # 145 ∷ # 30 ∷ # 84 ∷ # 251 ∷ # 48 ∷ # 127 ∷ # 87 ∷ # 7 ∷ # 198 ∷ # 132 ∷ # 124 ∷ # 222 ∷ # 163 ∷ # 175 ∷ # 103 ∷ # 113 ∷ # 153 ∷ # 49 ∷ # 87 ∷ # 224 ∷ # 217 ∷ # 182 ∷ # 1 ∷ # 107 ∷ # 165 ∷ # 107 ∷ # 113 ∷ # 23 ∷ # 233 ∷ # 255 ∷ # 253 ∷ # 49 ∷ # 181 ∷ # 213 ∷ # 106 ∷ # 37 ∷ # 109 ∷ # 167 ∷ # 150 ∷ # 226 ∷ # 153 ∷ # 149 ∷ # 77 ∷ # 213 ∷ # 212 ∷ # 230 ∷ # 202 ∷ # 156 ∷ # 198 ∷ # 232 ∷ # 98 ∷ # 55 ∷ # 138 ∷ # 153 ∷ # 3 ∷ # 57 ∷ # 249 ∷ # 204 ∷ # 170 ∷ # 138 ∷ # 165 ∷ # 64 ∷ # 80 ∷ # 233 ∷ # 216 ∷ # 85 ∷ # 167 ∷ # 103 ∷ # 114 ∷ # 106 ∷ # 44 ∷ # 128 ∷ # 227 ∷ # 86 ∷ # 88 ∷ # 248 ∷ # 24 ∷ # 188 ∷ # 1 ∷ # 165 ∷ # 26 ∷ # 30 ∷ # 135 ∷ # 198 ∷ # 216 ∷ # 157 ∷ # 230 ∷ # 30 ∷ # 136 ∷ # 114 ∷ # 66 ∷ # 33 ∷ # 128 ∷ # 153 ∷ # 83 ∷ # 192 ∷ # 198 ∷ # 202 ∷ # 17 ∷ # 89 ∷ # 48 ∷ # 100 ∷ # 236 ∷ # 203 ∷ # 231 ∷ # 72 ∷ # 20 ∷ # 83 ∷ # 91 ∷ # 231 ∷ # 155 ∷ # 183 ∷ # 243 ∷ # 137 ∷ # 188 ∷ # 200 ∷ # 17 ∷ # 194 ∷ # 139 ∷ # 106 ∷ # 194 ∷ # 121 ∷ # 136 ∷ # 227 ∷ # 12 ∷ # 48 ∷ # 195 ∷ # 109 ∷ # 187 ∷ # 3 ∷ # 226 ∷ # 167 ∷ # 94 ∷ # 204 ∷ # 40 ∷ # 53 ∷ # 205 ∷ # 71 ∷ # 45 ∷ # 60 ∷ # 72 ∷ # 217 ∷ # 192 ∷ # 128 ∷ # 211 ∷ # 50 ∷ # 60 ∷ # 146 ∷ # 196 ∷ # 147 ∷ # 57 ∷ # 55 ∷ # 153 ∷ # 128 ∷ # 174 ∷ # 39 ∷ # 16 ∷ # 230 ∷ # 179 ∷ # 12 ∷ # 2 ∷ # 3 ∷ # 1 ∷ # 0 ∷ [ # 1 ]

-- --     -- this is an example of non-RSA public key (ECDSA)
-- --     Pk₂ : List UInt8
-- --     Pk₂ = Tag.Sequence ∷ # 89 ∷ # 48 ∷ # 19 ∷ # 6 ∷ # 7 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 2 ∷ # 1 ∷ # 6 ∷ # 8 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 3 ∷ # 1 ∷ # 7 ∷ # 3 ∷ # 66 ∷ # 0 ∷ # 4 ∷ # 39 ∷ # 173 ∷ # 175 ∷ # 236 ∷ # 195 ∷ # 224 ∷ # 229 ∷ # 106 ∷ # 154 ∷ # 247 ∷ # 15 ∷ # 228 ∷ # 123 ∷ # 204 ∷ # 162 ∷ # 63 ∷ # 91 ∷ # 37 ∷ # 11 ∷ # 160 ∷ # 185 ∷ # 35 ∷ # 138 ∷ # 44 ∷ # 56 ∷ # 199 ∷ # 118 ∷ # 23 ∷ # 180 ∷ # 169 ∷ # 242 ∷ # 252 ∷ # 9 ∷ # 243 ∷ # 2 ∷ # 174 ∷ # 194 ∷ # 163 ∷ # 108 ∷ # 152 ∷ # 136 ∷ # 140 ∷ # 243 ∷ # 79 ∷ # 196 ∷ # 250 ∷ # 59 ∷ # 184 ∷ # 87 ∷ # 66 ∷ # 178 ∷ # 197 ∷ # 187 ∷ # 78 ∷ # 45 ∷ # 118 ∷ # 161 ∷ # 247 ∷ # 94 ∷ # 66 ∷ # 247 ∷ # 141 ∷ # 188 ∷ [ # 49 ]

-- --     test₁ : X509.PublicKey Pk₁
-- --     test₁ = Success.value (toWitness {Q = Logging.val (runParser parsePublicKey Pk₁)} tt)

-- --     test₂ : X509.PublicKey Pk₂
-- --     test₂ = Success.value (toWitness {Q = Logging.val (runParser parsePublicKey Pk₂)} tt)
