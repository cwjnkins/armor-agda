{-# OPTIONS --subtyping --guardedness --sized-types #-}


open import Data.Maybe
open import Aeres.Binary
  hiding (module Base64)
open import Aeres.Data.X509
open import Aeres.Data.X509.Semantic.Chain
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Main2 where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Base256

-- Function to find a trusted certificate
findTrustedCert : Exists─ (List UInt8) Name → List (Exists─ (List UInt8) Cert)
  →  Maybe (Exists─ (List UInt8) Cert)
findTrustedCert (fst , snd) [] = nothing
findTrustedCert (fst , snd) ((fst₁ , snd₁) ∷ tl)
   with MatchRDNSeq-dec (proj₂ (Cert.getSubject snd₁)) snd
... | yes _ = just (fst₁ , snd₁)
... | no _ = findTrustedCert (fst , snd) tl

alreadyInChain : Exists─ (List UInt8) Cert → List (Exists─ (List UInt8) Cert) → Bool
alreadyInChain (fst , snd) [] = false
alreadyInChain (fst , snd) ((fst₁ , snd₁) ∷ tl)
  with MatchRDNSeq-dec (proj₂ (Cert.getSubject snd)) (proj₂ (Cert.getSubject snd₁))
      | MatchRDNSeq-dec (proj₂ (Cert.getIssuer snd)) (proj₂ (Cert.getIssuer snd₁))
... | no _ | no _ = alreadyInChain (fst , snd) tl
... | no _ | yes _ = alreadyInChain (fst , snd) tl
... | yes _ | no _ = alreadyInChain (fst , snd) tl
... | yes _ | yes _ = true



-- Function to build a chain of certificates
buildChain : Exists─ (List UInt8) Cert → List (Exists─ (List UInt8) Cert)
  → List (Exists─ (List UInt8) Cert) → List (Exists─ (List UInt8) Cert)
  → List (List (Exists─ (List UInt8) Cert)) →  List (Exists─ (List UInt8) Cert)
  → List (List (Exists─ (List UInt8) Cert))
buildChain startCert candidateCerts trustedCerts currentChain allChains usedIndices
  with findTrustedCert (Cert.getIssuer (proj₂ startCert)) trustedCerts
... | nothing  = let
                  newChain = currentChain ++ [ startCert ]
                  newUsedIndices = {!!}
                  continue = filter {!!} candidateCerts
                in
                  foldr (λ nextCert → {!!}) allChains continue
... | just trustedCert = let
                         newChain = currentChain ++ {!!}
                       in
                         if not (alreadyInChain trustedCert currentChain) then newChain ∷ allChains else allChains


-- -- Function to build a chain of certificates
-- buildChain : Certificate → List Certificate → List Certificate → List Certificate → List (List Certificate) → List Certificate → List (List Certificate)
-- buildChain startCert candidateCerts trustedCerts currentChain allChains usedIndices with findTrustedCert (Certificate.issuer startCert) trustedCerts
-- ... | nothing  = let
--                   newChain = currentChain ++ [ startCert ]
--                   newUsedIndices = startCert ∷ usedIndices
--                   continue = filter (λ nextCert → nextCert .subject ≡ startCert .issuer ∧ not (List.any (λ cert → cert .subject ≡ nextCert .subject ∧ cert .issuer ≡ nextCert .issuer) newChain)) candidateCerts
--                 in
--                   foldr (λ nextCert → buildChain nextCert candidateCerts trustedCerts newChain) allChains continue
-- ... | just trustedCert = let
--                          newChain = currentChain ++ [ startCert, trustedCert ]
--                        in
--                          if not (alreadyInChain trustedCert currentChain) then newChain ∷ allChains else allChains


-- Function to generate all valid chains
generateValidChains :  List (Exists─ (List UInt8) Cert) → List (Exists─ (List UInt8) Cert)
  → List (List (Exists─ (List UInt8) Cert))
generateValidChains candidateCerts trustedCerts with List.head candidateCerts
... | nothing  = []
... | just hd  = buildChain hd candidateCerts trustedCerts [] [] []
