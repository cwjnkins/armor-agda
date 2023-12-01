{-# OPTIONS --subtyping --sized-types --guardedness #-}

open import Aeres.Binary
  hiding (module Base64)
open import Aeres.Data.X509
open import Aeres.Data.X509.Semantic.Chain
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Foreign.ByteString
  hiding (foldl)
open import Aeres.Prelude
import      Data.Nat.Properties as Nat
open import Data.Nat.Show renaming (show to showℕ) 

module Aeres.Data.X509.ChainBuilder.Exec where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Base256

candidateChains : List (List (Exists─ (List UInt8) Cert)) → List (Exists─ (List UInt8) CertList)
candidateChains [] = []
candidateChains (x ∷ x₁) = (candidateChains x₁) ++ [ helper (reverse x) ]
  where
  helper : List (Exists─ (List UInt8) Cert) → Exists─ (List UInt8) CertList
  helper [] = _ , nil
  helper ((─ ps , snd) ∷ x₁) = let (─ bs , tl) = helper x₁ in (─ (ps ++ bs)) , cons (mkIListCons snd tl refl)

-- Function to find a trusted certificate
findTrustedCert : Exists─ (List UInt8) Name → List (Exists─ (List UInt8) Cert)
  →  Maybe (List (Exists─ (List UInt8) Cert))
findTrustedCert (fst , snd) [] = nothing
findTrustedCert (fst , snd) ((fst₁ , snd₁) ∷ tl)
   with MatchRDNSeq-dec (Cert.getSubject snd₁) snd
... | no _ = findTrustedCert (fst , snd) tl
... | yes _
  with findTrustedCert (fst , snd) tl
... | just x = just ((fst₁ , snd₁) ∷ x)
... | nothing = just [ (fst₁ , snd₁) ]

-- Function to build a chain of certificates
{-# NON_TERMINATING #-}
buildChain' : (workList : List (List (Exists─ _ Cert) × List (Exists─ _ Cert)))
              → (trustedCert : List (Exists─ _ Cert)) → (allChains : List (List (Exists─ _ Cert)))
              → List (List (Exists─ _ Cert))
buildChain' [] trustedCert allChains = allChains
buildChain' (([] , otherCerts) ∷ workList) trustedCert allChains = []
  -- TODO rule this out by types (Vec ... (suc n))
buildChain' ((toAuth ∷ restCandidateChain , otherCerts) ∷ workList) trustedCerts allChains =
  buildChain' (newChainsForEntity ++ workList) trustedCerts allChains'
  where   
  allChains' : List (List (Exists─ _ Cert))
  allChains' = case findTrustedCert (─ _ , Cert.getIssuer (proj₂ toAuth)) trustedCerts of λ where
    nothing → allChains
    (just issuersForAuthInTrust) →
         map (λ issuerForAuthInTrust →
                if ⌊ issuerForAuthInTrust ≟ toAuth ⌋
                then toAuth ∷ restCandidateChain
                else issuerForAuthInTrust ∷ toAuth ∷ restCandidateChain)
           issuersForAuthInTrust
      ++ allChains

  otherIssuersForEntity : List (Exists─ _ Cert) × List (Exists─ _ Cert)
  otherIssuersForEntity =
    partition (λ c → MatchRDNSeq-dec (Cert.getSubject (proj₂ c)) (Cert.getIssuer (proj₂ toAuth)))
      otherCerts

  newChainsForEntity : List (List (Exists─ _ Cert) × List (Exists─ _ Cert))
  newChainsForEntity =
    let (matchers , nomatchers) = otherIssuersForEntity in
    tabulate{n = length matchers} λ i → lookup matchers i ∷ toAuth ∷ restCandidateChain , (take (toℕ i) matchers ++ drop (1 + toℕ i) matchers) ++ nomatchers

generateValidChains : (candidates trusted : List (Exists─ (List UInt8) Cert)) → List (List (Exists─ (List UInt8) Cert))
generateValidChains [] trusted = []
generateValidChains (startCert ∷ candidates) trusted =
  buildChain' [ ( [ startCert ] , candidates ) ] trusted []
