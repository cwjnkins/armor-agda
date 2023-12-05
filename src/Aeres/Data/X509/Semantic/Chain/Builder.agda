{-# OPTIONS  --sized-types #-}

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

IsAllIssuersForIn-syntax : {@0 bs : List UInt8} (issuee : Cert bs) (certs : List (Exists─ _ Cert)) → IssuersFor issuee In certs → Set
IsAllIssuersForIn-syntax issuee certs issuers = All (λ (─ _ , cert) → cert IsIssuerFor issuee → (-, cert) ∈ map proj₁ issuers) certs

syntax IsAllIssuersForIn-syntax issuee certs issuers = issuers IsAllIssuersFor issuee In certs

AllIssuersFor_In_ : {@0 bs : List UInt8} (issuee : Cert bs) (certs : List (Exists─ _ Cert)) → Set
AllIssuersFor issuee In certs = Σ (IssuersFor issuee In certs) λ issuers → (issuers IsAllIssuersFor issuee In certs)

data Chain (trustedRoot candidates : List (Exists─ _ Cert)) : ∀ {@0 bs} → Cert bs → Set where
  root : ∀ {@0 bs} {c : Cert bs} → IssuerFor c In trustedRoot → Chain trustedRoot candidates c
  link : ∀ {@0 bs₁ bs₂} (issuer : Cert bs₁) {c₂ : Cert bs₂}
         → (isIn : issuer IsIssuerFor c₂ In candidates) → Chain trustedRoot (candidates Any.─ proj₂ isIn) issuer
         → Chain trustedRoot candidates c₂

isLink? : ∀ {trustedRoot candidates : List (Exists─ _ Cert)} {@0 bs} {c : Cert bs}
          → Chain trustedRoot candidates c → Bool
isLink? (root _) = false
isLink? (link _ _ _) = true

-- produces a list of certs corresponding to the chain, plus the trusted issuer certificate
toList : ∀ {trustedRoot candidates} {@0 bs} {issuee : Cert bs} → Chain trustedRoot candidates issuee → List (Exists─ _ Cert)
toList{issuee = issuee} (root (issuer , _)) = (-, issuee) ∷ [ issuer ]
toList{issuee = issuee} (link issuer isIn chain) = (-, issuee) ∷ toList chain

pattern anIssuerForIn{bs} issuer isIssuerFor issuer∈ = _,_ (_,_ (─_ bs) issuer) (_,_ isIssuerFor issuer∈)

-- data TrustTree (trustedRoot candidates : List (Exists─ _ Cert)) : ∀ {@0 bs} → Cert bs → Set
TrustTreeBranchF : ∀ {@0 bs} trustedRoot candidates (issuee : Cert bs) → IssuerFor issuee In candidates → Set
record TrustTree (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs : List UInt8} (issuee : Cert bs) : Set

-- data TrustTree trustedRoot candidates where
--   trustTree : ∀ {@0 bs} → (issuee : Cert bs) → TrustTreeNode trustedRoot candidates issuee → TrustTree trustedRoot candidates issuee

TrustTreeBranchF trustedRoot candidates issuee (anIssuerForIn issuer isIssuerFor issuer∈) =
  TrustTree trustedRoot (candidates Any.─ issuer∈) issuer

record TrustTree trustedRoot candidates {bs} issuee where
  inductive
  constructor mkTrustTree
  field
    rootIssuers  : AllIssuersFor issuee In trustedRoot
    otherIssuers : AllIssuersFor issuee In candidates
    otherTrust   : All (TrustTreeBranchF trustedRoot candidates issuee) (proj₁ otherIssuers)

findIssuersFor : ∀ {@0 bs} → (issuee : Cert bs) → (certs : List (Exists─ _ Cert)) → AllIssuersFor issuee In certs
findIssuersFor issuee [] = [] , []
findIssuersFor issuee ((─ _ , cert) ∷ certs) =
  case cert isIssuerFor? issuee of λ where
    (yes isIssuer) →
      Product.map (λ issuers → ((-, cert) , (isIssuer , (here refl))) ∷ weaken issuers)
      (λ {issuers} isAllIssuersForIn →
        All.tabulate (λ where
          {─ _ , cert} (here px) isIssuerFor → here px
          {─ _ , cert} (there cert∈) isIssuerFor →
            there (∈weaken issuers (-, cert) (All.lookup isAllIssuersForIn cert∈ isIssuerFor))))
      issuers
    (no ¬isIssuer) →
      Product.map
        (λ issuers → weaken issuers)
        (λ {issuers} isAllIssuersForIn →
          All.tabulate λ where
            {─ _ , cert} (here refl) isIssuerFor →
              contradiction isIssuerFor ¬isIssuer
            {─ _ , cert} (there c∈) isIssuerFor →
              ∈weaken issuers (-, cert) (All.lookup isAllIssuersForIn c∈ isIssuerFor))
        issuers
  where
  import Data.Product as Product

  issuers : AllIssuersFor issuee In certs
  issuers = findIssuersFor issuee certs

  weaken₁ : IssuerFor issuee In certs → IssuerFor issuee In ((-, cert) ∷ certs)
  weaken₁ = (λ where (anIssuerForIn issuer isIssuerFor issuer∈) → anIssuerForIn issuer isIssuerFor (there issuer∈))

  weaken : IssuersFor issuee In certs → IssuersFor issuee In ((-, cert) ∷ certs)
  weaken issuers = map weaken₁ issuers

  ∈weaken : (issuers : IssuersFor issuee In certs) → (c : Exists─ _ Cert) → c ∈ map proj₁ issuers → c ∈ map proj₁ (weaken issuers)
  ∈weaken issuers (─ _ , c) c∈issuers = subst (_∈ map proj₁ (weaken issuers)) c≡ c∈
    where
    lem : ∃ λ x → x ∈ issuers × (-, c) ≡ proj₁ x
    lem = List.∈-map⁻ proj₁ c∈issuers

    c∈ : proj₁ (weaken₁ (proj₁ lem)) ∈ map proj₁ (weaken issuers)
    c∈ = List.∈-map⁺ proj₁ (List.∈-map⁺ weaken₁ (proj₁ (proj₂ lem)))

    c≡ : proj₁ (weaken₁ (proj₁ lem)) ≡ (-, c)
    c≡ = case lem ret (λ x → proj₁ (weaken₁ (proj₁ x)) ≡ (-, c)) of λ where
      (anIssuerForIn _ _ _ , (_ , refl)) → refl

buildTrustTreeWF : (trustedRoot candidates : List (Exists─ _ Cert)) → @0 Acc _<_ (length candidates)
               → ∀ {@0 bs} → (issuee : Cert bs) → TrustTree trustedRoot candidates issuee
buildTrustTreeWF trustedRoot candidates (WellFounded.acc rs) issuee =
  mkTrustTree rootIssuers otherIssuers (All.tabulate ih)
  where
  rootIssuers : AllIssuersFor issuee In trustedRoot
  rootIssuers = findIssuersFor issuee trustedRoot

  otherIssuers : AllIssuersFor issuee In candidates
  otherIssuers = findIssuersFor issuee candidates

  ih : {iss : IssuerFor issuee In candidates} → iss ∈ proj₁ otherIssuers → TrustTreeBranchF trustedRoot candidates issuee iss
  ih{anIssuerForIn issuer isIssuerFor issuer∈candidates} ∈otherIssuers =
    buildTrustTreeWF trustedRoot (candidates Any.─ issuer∈candidates) (rs _ (Lemmas.length-─-< candidates _)) issuer

buildTrustTree : (trustedRoot candidates : List (Exists─ _ Cert))
                 → ∀ {@0 bs} → (issuee : Cert bs) → TrustTree trustedRoot candidates issuee
buildTrustTree trustedRoot candidates = buildTrustTreeWF trustedRoot candidates (<-wellFounded _)
  where
  open import Data.Nat.Induction

toChainsBranchWF
  : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
    → @0 Acc _<_ (length candidates)
    → ∃ (TrustTreeBranchF trustedRoot candidates endEnt) → List (Chain trustedRoot candidates endEnt)

toChainsWF : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
             → @0 Acc _<_ (length candidates)
             → TrustTree trustedRoot candidates endEnt
             → List (Chain trustedRoot candidates endEnt)

toChainsBranchWF trustedRoot candidates endEnt (WellFounded.acc rs) (anIssuerForIn issuer isIssuerFor issuer∈ , tr) =
  map (link issuer (isIssuerFor , issuer∈))
    (toChainsWF trustedRoot (candidates Any.─ issuer∈) issuer (rs _ (Lemmas.length-─-< candidates _)) tr)

toChainsWF trustedRoot candidates endEnt ac (mkTrustTree rootIssuers otherIssuers otherTrust) =
     map root (proj₁ rootIssuers)
  ++ concatMap (toChainsBranchWF trustedRoot candidates endEnt ac) (All.toList otherTrust)

toChains : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) {@0 bs} (endEnt : Cert bs)
           → TrustTree trustedRoot candidates endEnt
           → List (Chain trustedRoot candidates endEnt)
toChains trustedRoot candidates endEnt tr = toChainsWF trustedRoot candidates endEnt (<-wellFounded _) tr
  where
  open import Data.Nat.Induction

buildChains : (trustedRoot candidates : List (Exists─ _ Cert))
              → ∀ {@0 bs} → (issuee : Cert bs)
              → List (Chain trustedRoot candidates issuee)
buildChains trustedRoot candidates issuee =
  toChains _ _ _ (buildTrustTree trustedRoot candidates issuee)

-- completeness
data _≡Chain_ {trustedRoot candidates : List (Exists─ _ Cert)} : ∀ {@0 bs} {endEnt : Cert bs} → (c₁ c₂ : Chain trustedRoot candidates endEnt) → Set where
  root : ∀ {@0 bs} {c : Cert bs} → (iss₁ iss₂ : IssuerFor c In trustedRoot)
         → proj₁ iss₁ ≡ proj₁ iss₂
         → (root{c = c} iss₁) ≡Chain (root{c = c} iss₂)
  link : ∀ {@0 bs₁ bs₂} (issuer : Cert bs₁) {c : Cert bs₂}
         → (isIssuer₁ isIssuer₂ : issuer IsIssuerFor c)
         → (isIn : (-, issuer) ∈ candidates)
         → (c₁ c₂ : Chain trustedRoot (candidates Any.─ isIn) issuer) → c₁ ≡Chain c₂
         → (link issuer {c} (isIssuer₁ , isIn) c₁) ≡Chain (link issuer {c} (isIssuer₂ , isIn) c₂)

toChainsBranchCompleteWF
  : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) (unique : List.Unique _≟_ candidates)
    → ∀ {@0 bs} (issuee : Cert bs)
    → (@0 ac : Acc _<_ (length candidates))
    → (tb : ∃ (TrustTreeBranchF trustedRoot candidates issuee))
    → let (anIssuerForIn issuer _ issuer∈) = proj₁ tb in
      ∀ (isIssuerFor : issuer IsIssuerFor issuee)
      → (chain : Chain trustedRoot (candidates Any.─ issuer∈) issuer)
      → Any{A = Chain trustedRoot candidates issuee} (λ c → link issuer (isIssuerFor , issuer∈) chain ≡Chain c) (toChainsBranchWF _ _ _ ac tb)


toChainsCompleteWF
  : ∀ (trustedRoot candidates : List (Exists─ _ Cert)) (unique : List.Unique _≟_ candidates)
    → ∀ {@0 bs} (issuee : Cert bs)
    → (@0 ac : Acc _<_ (length candidates))
    → (tr : TrustTree trustedRoot candidates issuee)
    → (c : Chain trustedRoot candidates issuee)
    → Any (c ≡Chain_) (toChainsWF _ _ _ ac tr)

─-preserves-distinct : {A : Set} ⦃ _ : Eq A ⦄ {x y : A} (xs : List A) → All (y ≢_) xs → (x∈ : x ∈ xs) → All (y ≢_) (xs Any.─ x∈)
─-preserves-distinct {x = x} {y} .(_ ∷ _) (px₁ ∷ distinct) (here px) = distinct
─-preserves-distinct {x = x} {y} .(_ ∷ _) (px ∷ distinct) (there x∈) = px ∷ ─-preserves-distinct _ distinct x∈

unique─ : {A : Set} ⦃ _ : Eq A ⦄ {x : A} (xs : List A) → List.Unique _≟_ xs → (x∈ : x ∈ xs) → List.Unique _≟_ (xs Any.─ x∈)
unique─ .(_ ∷ _) (x ∷ unique) (here refl) = unique
unique─ .(_ ∷ _) (x ∷ unique) (there x∈) = ─-preserves-distinct _ x x∈ ∷ unique─ _ unique x∈

toChainsBranchCompleteWF trustedRoot candidates unique issuee (WellFounded.acc rs) ((anIssuerForIn issuer isIssuerFor issuer∈) , tr) isIssuerFor' chain =
  Any ((link issuer (isIssuerFor' , issuer∈) chain) ≡Chain_) (map (link issuer (isIssuerFor , issuer∈)) chains') ∋
    Any.map⁺ {xs = chains'} (Any.map (λ {chain'} ≡chain → link issuer isIssuerFor' isIssuerFor issuer∈ chain chain' ≡chain) ih)
  where
  chains' : List (Chain trustedRoot (candidates Any.─ issuer∈) issuer)
  chains' = toChainsWF trustedRoot _ issuer (rs _ (Lemmas.length-─-< candidates _)) tr

  ih : Any (chain ≡Chain_) chains'
  ih = toChainsCompleteWF trustedRoot (candidates Any.─ issuer∈) (unique─ candidates unique issuer∈) issuer (rs _ (Lemmas.length-─-< candidates _)) tr chain

allLookupLemma : {A : Set} {P : (a : A) → Set} → ∀ {x xs} → (all : All P xs) → (x∈ : x ∈ xs) → ((x , All.lookup all x∈)) ∈ All.toList all
allLookupLemma {x} {xs} (px₁ ∷ all₁) (here refl) = here refl
allLookupLemma {x} {xs} (px ∷ all₁) (there x∈) = there (allLookupLemma all₁ x∈)


toChainsCompleteWF trustedRoot candidates unique endEnt ac (mkTrustTree (rootIssuers , allRootIssuers) otherIssuers otherTrust) (root (anIssuerForIn issuer isIssuerFor issuer∈)) =
  Any.++⁺ˡ {xs = map root rootIssuers} (Any.map⁺ (List.lose rootIssuer∈root (root _ _ (proj₂ (proj₂ rootIssuerLem)))))
  where
  rootIssuerLem : ∃ λ x → x ∈ rootIssuers × (-, issuer) ≡ proj₁ x
  rootIssuerLem = List.∈-map⁻ proj₁ (All.lookup allRootIssuers issuer∈ isIssuerFor)

  rootIssuer = proj₁ rootIssuerLem
  rootIssuer∈root = proj₁ (proj₂ rootIssuerLem)
toChainsCompleteWF trustedRoot candidates unique endEnt ac (mkTrustTree (rootIssuers , _) (otherIssuers , allOtherIssuers) otherTrust) chain@(link issuer (isIssuer , issuer∈) c) =
  Any.++⁺ʳ (map root rootIssuers)
    (Any.concat⁺{xss = map (toChainsBranchWF trustedRoot candidates endEnt ac) (All.toList otherTrust)}
      (Any.map⁺{xs = All.toList otherTrust}
        (List.lose
          (allLookupLemma{x = issuer'} otherTrust issuer'∈otherIssuers)
          (toChainsBranchCompleteWF trustedRoot candidates unique endEnt ac (issuer' , All.lookup otherTrust issuer'∈otherIssuers) isIssuer c))))
  where
  xs = concatMap (toChainsBranchWF trustedRoot candidates endEnt ac) (All.toList otherTrust)

  issuerFromOtherIssuers : ∃ λ x → x ∈ otherIssuers × (-, issuer) ≡ proj₁ x
  issuerFromOtherIssuers = List.∈-map⁻ proj₁ (All.lookup allOtherIssuers issuer∈ isIssuer)

  isIssuer×isInF : (∃ λ x → x ∈ otherIssuers × (-, issuer) ≡ proj₁ x) → issuer IsIssuerFor endEnt In candidates
  isIssuer×isInF ((_ , ret) , x∈otherIssuers , refl) = ret

  isIssuer×isIn : issuer IsIssuerFor endEnt In candidates
  isIssuer×isIn = isIssuer×isInF issuerFromOtherIssuers

  issuer' : IssuerFor endEnt In candidates
  issuer' = anIssuerForIn issuer (proj₁ isIssuer×isIn) issuer∈

  issuer'∈otherIssuers : issuer' ∈ otherIssuers
  issuer'∈otherIssuers =
    case issuerFromOtherIssuers ret (λ x → anIssuerForIn issuer (proj₁ (isIssuer×isInF x)) issuer∈ ∈ otherIssuers) of λ where
      ((_ , isIssuer , isIn) , x∈otherIssuers , refl) →
        case ∈-unique unique isIn issuer∈ of λ where
          refl → x∈otherIssuers
