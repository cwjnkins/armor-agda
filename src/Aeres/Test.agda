open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509

module Aeres.Test where

open Base256

open import Aeres.Data.Parser Dig

ParserX509 : (A : List Dig → Set) → Set
ParserX509 A = Parser Maybe A

postulate
  parseLen : ParserX509 Length
  parseTBS : ParserX509 X509.TBSCert
  parseSignAlg : ParserX509 X509.SignAlg
  parseSignature : ParserX509 X509.Signature

parseCertField : ParserX509 X509.CertField
Parser.runParser parseCertField xs = do
  (mkSuccess pre tup suf pf) ← Parser.runParser (parseTBS ⟨&⟩ (parseSignAlg ⟨&⟩ parseSignature)) xs
  return (mkSuccess pre (combine pre tup) suf pf)
  where
  open ≡-Reasoning

  combine : ∀ pre → (X509.TBSCert ×ₚ (X509.SignAlg ×ₚ X509.Signature)) pre
            → X509.CertField pre
  combine pre (mkProdₚ prefix₁ suffix₁ prefix++suffix≡₁ tbs (mkProdₚ prefix₂ suffix₂ prefix++suffix≡₂ sa sig)) =
    subst X509.CertField pf (X509.mkCertField tbs sa sig)
    where
    pf : prefix₁ ++ prefix₂ ++ suffix₂ ≡ pre
    pf = begin
      prefix₁ ++ prefix₂ ++ suffix₂ ≡⟨ sym (cong (prefix₁ ++_) prefix++suffix≡₂) ⟩
      prefix₁ ++ suffix₁            ≡⟨ sym prefix++suffix≡₁ ⟩
      pre ∎

parseCert : ParserX509 X509.Cert
Parser.runParser parseCert xs = do
  mkSuccess ._  refl suf₀ refl ← Parser.runParser (parseSingle Tag.Sequence) xs
  mkSuccess lenₛ len suf₁ refl ← Parser.runParser parseLen suf₀
  mkSuccess cfₛ  cf  suf₂ refl ← Parser.runParser parseCertField suf₁
  combine suf₂ len cf
  where
  open ≡-Reasoning

  combine : ∀ {lenₛ cfₛ} suf₂
            → Length lenₛ → X509.CertField cfₛ
            → Maybe (Success X509.Cert (Tag.Sequence ∷ lenₛ ++ cfₛ ++ suf₂))
  combine {lenₛ}{cfₛ} [] len cf
    with sizeOf cf ≟ getLength len  -- TODO: it really should be length cfₛ
  ...| yes len≡
    rewrite ++-identityʳ cfₛ
    = return (mkSuccess (Tag.Sequence ∷ lenₛ ++ cfₛ) cert [] (++-identityʳ _))
    where
    cert : X509.Cert (Tag.Sequence ∷ lenₛ ++ cfₛ)
    cert = X509.mkCert len cf (fromWitness len≡)
  ...| no  len≢ = ∅
  combine (x ∷ suf) len cf = ∅
