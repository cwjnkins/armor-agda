{-# OPTIONS  --subtyping --sized-types #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Semantic.Chain.NameMatch
import      Aeres.Grammar.Parallel
open import Aeres.Prelude
import      Data.List as List
import      Data.List.Membership.Propositional as List
import      Data.List.Membership.Propositional.Properties as List

module Aeres.Data.X509.Semantic.Chain.Builder where

open Aeres.Grammar.Parallel UInt8

-- IssuerFor c₁ c₂ := "a cert for the issuer of c₁ is c₂"
_IsIssuerFor_ : ∀ {@0 bs₁ bs₂} → Cert bs₁ → Cert bs₂ → Set
_IsIssuerFor_ issuer issuee = NameMatch (Cert.getIssuer issuee) (Cert.getSubject issuer)

_isIssuerFor?_ :  ∀ {@0 bs₁ bs₂} → (issuer : Cert bs₁) → (issuee : Cert bs₂) → Dec (issuer IsIssuerFor issuee)
issuer isIssuerFor? issuee = nameMatch? (Cert.getIssuer issuee) (Cert.getSubject issuer)

_IsIssuerFor_In_ : ∀ {@0 bs₁ bs₂} → Cert bs₁ → Cert bs₂ → (certs : List (Exists─ _ Cert)) → Set
issuer IsIssuerFor issuee In certs = issuer IsIssuerFor issuee × (─ _ , issuer) ∈ certs

IssuerFor_In_ : ∀ {@0 bs} → Cert bs → List (Exists─ _ Cert) → Set
IssuerFor issuee In certs = Σ (Exists─ _ Cert) (λ where (─ _ , issuer) → issuer IsIssuerFor issuee In certs)

IssuersFor_In_ : {@0 bs : List UInt8} (issuee : Cert bs) (certs : List (Exists─ _ Cert)) → Set
IssuersFor issuee In certs = List (IssuerFor issuee In certs)
  -- List (Exists─ _ (Σₚ Cert λ _ issuer → issuer IsIssuerFor issuee In certs))

pattern anIssuerForIn{bs} issuer isIssuerFor issuer∈ = _,_ (_,_ (─_ bs) issuer) (_,_ isIssuerFor issuer∈)

-- data TrustTree (trustedRoot candidates : List (Exists─ _ Cert)) : ∀ {@0 bs} → Cert bs → Set
TrustTreeBranchF : ∀ {@0 bs} trustedRoot candidates (issuee : Cert bs) → IssuerFor issuee In candidates → Set
record TrustTree (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs : List UInt8} (issuee : Cert bs) : Set

-- data TrustTree trustedRoot candidates where
--   trustTree : ∀ {@0 bs} → (issuee : Cert bs) → TrustTreeNode trustedRoot candidates issuee → TrustTree trustedRoot candidates issuee

TrustTreeBranchF trustedRoot candidates issuee (anIssuerForIn issuer isIssuerFor issuer∈) = TrustTree trustedRoot (candidates Any.─ issuer∈) issuer

record TrustTree trustedRoot candidates {bs} issuee where
  inductive
  constructor mkTrustTree
  field
    rootIssuers  : IssuersFor issuee In trustedRoot
    otherIssuers : IssuersFor issuee In candidates
    otherTrust   : All (TrustTreeBranchF trustedRoot candidates issuee) otherIssuers

findIssuersFor : ∀ {@0 bs} → (issuee : Cert bs) → (certs : List (Exists─ _ Cert)) → IssuersFor issuee In certs
findIssuersFor issuee certs =
  All.toList (All.tabulate help)
  where
  P : Exists─ _ Cert → Set
  P (─ _ , cert) = cert IsIssuerFor issuee

  P? : Decidable P
  P? (─ _ , cert) = cert isIssuerFor? issuee

  issuers : List (Exists─ _ Cert)
  issuers = filter P? certs

  help : {issuer : Exists─ _ Cert} → issuer ∈ issuers → (proj₂ issuer) IsIssuerFor issuee In certs
  help{(─ _ , issuer)} issuer∈ = swap (List.∈-filter⁻ P? {xs = certs} issuer∈)

buildTrustTreeWF : (trustedRoot candidates : List (Exists─ _ Cert)) → @0 Acc _<_ (length candidates)
               → ∀ {@0 bs} → (issuee : Cert bs) → TrustTree trustedRoot candidates issuee
buildTrustTreeWF trustedRoot candidates (WellFounded.acc rs) issuee =
  mkTrustTree rootIssuers otherIssuers (All.tabulate ih)
  where
  rootIssuers : IssuersFor issuee In trustedRoot
  rootIssuers = findIssuersFor issuee trustedRoot

  otherIssuers : IssuersFor issuee In candidates
  otherIssuers = findIssuersFor issuee candidates

  ih : {iss : IssuerFor issuee In candidates} → iss ∈ otherIssuers → TrustTreeBranchF trustedRoot candidates issuee iss
  ih{anIssuerForIn issuer isIssuerFor issuer∈candidates} ∈otherIssuers =
    buildTrustTreeWF trustedRoot (candidates Any.─ issuer∈candidates) (rs _ (Lemmas.length-─-< candidates _)) issuer

buildTrustTree : (trustedRoot candidates : List (Exists─ _ Cert))
                 → ∀ {@0 bs} → (issuee : Cert bs) → TrustTree trustedRoot candidates issuee
buildTrustTree trustedRoot candidates = buildTrustTreeWF trustedRoot candidates (<-wellFounded _)
  where
  open import Data.Nat.Induction

data Chain (trustedRoot candidates : List (Exists─ _ Cert)) : ∀ {@0 bs} → Cert bs → Set where
  root : ∀ {@0 bs} {c : Cert bs} → IssuerFor c In trustedRoot → Chain trustedRoot candidates c
  link : ∀ {@0 bs₁ bs₂} (issuer : Cert bs₁) {c₂ : Cert bs₂}
         → (isIn : issuer IsIssuerFor c₂ In candidates) → Chain trustedRoot (candidates Any.─ proj₂ isIn) issuer
         → Chain trustedRoot candidates c₂

toChainsWF : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
             → TrustTree trustedRoot candidates endEnt
             → @0 Acc _<_ (length candidates)
             → List (Chain trustedRoot candidates endEnt)
toChainsWF trustedRoot candidates endEnt (mkTrustTree rootIssuers otherIssuers otherTrust) (WellFounded.acc rs) =
     map root rootIssuers
  ++ concatMap
       (λ where
         (anIssuerForIn issuer isIssuerFor issuer∈ , tr) →
           map (link issuer (isIssuerFor , issuer∈))
             (toChainsWF trustedRoot (candidates Any.─ issuer∈) issuer tr (rs _ (Lemmas.length-─-< candidates _))))
       (All.toList otherTrust)

toChains : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
           → TrustTree trustedRoot candidates endEnt
           → List (Chain trustedRoot candidates endEnt)
toChains trustedRoot candidates endEnt tr = toChainsWF trustedRoot candidates endEnt tr (<-wellFounded _)
  where
  open import Data.Nat.Induction

buildChains : (trustedRoot candidates : List (Exists─ _ Cert))
              → ∀ {@0 bs} → (issuee : Cert bs)
              → List (Chain trustedRoot candidates issuee)
buildChains trustedRoot candidates issuee =
  toChains _ _ _ (buildTrustTree trustedRoot candidates issuee)
