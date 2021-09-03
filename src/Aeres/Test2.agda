open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties

module Aeres.Test2 where

open Base256
open import Aeres.Data.Parser Dig

open import Data.List.Solver using (module ++-Solver)
open ++-Solver

ParserX509 : (A : List Dig → Set) → Set
ParserX509 A = Parser (Logging ∘ Dec) A

postulate
  parseLen : ParserX509 Length
  parseTBS : ParserX509 X509.TBSCert
  parseSignAlg : ParserX509 X509.SignAlg
  parseSignature : ParserX509 X509.Signature

parseCertField : ParserX509 X509.CertField
runParser parseCertField xs = do
  yes tbs'@(tbs ^S suf₀ [ refl ]S) ← runParser parseTBS xs
    where no pf → tell here' >> (return ∘ no $ noTBS pf)
  yes sa'@(sa ^S suf₁  [ refl ]S) ← runParser parseSignAlg suf₀
    where no pf → tell here' >> (return ∘ no $ noSignAlg tbs pf)
  yes sig'@(sig ^S suf₂ [ refl ]S) ← runParser parseSignature suf₁
    where no pf → tell here' >> (return ∘ no $ noSignature tbs sa pf)
  return (yes (X509.mkCertField tbs sa sig ^S suf₂
                [ sym $ Lemmas.++-assoc₄
                    (Success.prefix tbs') (Success.prefix sa') (Success.prefix sig') suf₂ ]S))
  where
  here' = "parseCertField"

  noTBS : ¬ Success X509.TBSCert xs → ¬ Success X509.CertField xs
  noTBS ¬tbs (cf ^S suf [ ps≡ ]S)
    with cf
  ... | X509.mkCertField{tbsₛ}{saₛ}{sigₛ} tbs _ _ =
    ¬tbs (tbs ^S saₛ ++ sigₛ ++ suf
      [ begin
        tbsₛ ++ saₛ ++ sigₛ ++ suf
          ≡⟨ Lemmas.++-assoc₄ tbsₛ saₛ sigₛ suf ⟩
        (tbsₛ ++ saₛ ++ sigₛ) ++ suf
          ≡⟨ ps≡ ⟩
        xs ∎ ]S)
    where open ≡-Reasoning

  noSignAlg : ∀ {tbsₛ suf} → X509.TBSCert tbsₛ → ¬ Success X509.SignAlg suf → ¬ Success X509.CertField (tbsₛ ++ suf)
  noSignAlg{tbsₛ}{suf} tbs ¬sa (cf ^S suf' [ ps≡ ]S)
    with cf
  ... | X509.mkCertField{tbsₛ'}{saₛ'}{sigₛ'} tbs' sa' _
    with ps≡'
    where
    open ≡-Reasoning

    ps≡' : tbsₛ' ++ saₛ' ++ sigₛ' ++ suf' ≡ tbsₛ ++ suf
    ps≡' = begin
      tbsₛ' ++ saₛ' ++ sigₛ' ++ suf'
        ≡⟨ Lemmas.++-assoc₄ tbsₛ' saₛ' sigₛ' suf' ⟩
      (tbsₛ' ++ saₛ' ++ sigₛ') ++ suf'
        ≡⟨ ps≡ ⟩
      tbsₛ ++ suf
        ∎
  ... | ps≡'
    with NoNest.TBSCert ps≡' tbs' tbs
  ... | refl = ¬sa (sa' ^S sigₛ' ++ suf' [ ++-cancelˡ tbsₛ' ps≡' ]S)

  noSignature : ∀ {tbsₛ saₛ suf} → X509.TBSCert tbsₛ → X509.SignAlg saₛ
                → ¬ Success X509.Signature suf
                → ¬ Success X509.CertField (tbsₛ ++ saₛ ++ suf)
  noSignature{tbsₛ}{saₛ}{suf} tbs sa ¬sig (cf ^S suf' [ ps≡ ]S)
    with cf
  ... | X509.mkCertField{tbsₛ'}{saₛ'}{sigₛ'} tbs' sa' sig'
    with ps≡'
    where
    open ≡-Reasoning

    ps≡' : tbsₛ' ++ saₛ' ++ sigₛ' ++ suf' ≡ tbsₛ ++ saₛ ++ suf
    ps≡' = begin
      tbsₛ' ++ saₛ' ++ sigₛ' ++ suf'
        ≡⟨ Lemmas.++-assoc₄ tbsₛ' saₛ' sigₛ' suf' ⟩
      (tbsₛ' ++ saₛ' ++ sigₛ') ++ suf'
        ≡⟨ ps≡ ⟩
      tbsₛ ++ saₛ ++ suf
        ∎
  ... | ps≡'
    with NoNest.TBSCert ps≡' tbs' tbs
  ... | refl
    with NoNest.SignAlg (++-cancelˡ tbsₛ' ps≡') sa' sa
  ... | refl =
    ¬sig (sig' ^S suf'
           [ ++-cancelˡ saₛ' (++-cancelˡ tbsₛ' ps≡') ]S)

