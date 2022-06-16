{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.EcPkAlgFields  as EcProps
import      Aeres.Data.X509.Properties.RSAPkAlgFields as RSAProps
import      Aeres.Data.X509.Properties.SignAlgFields  as SignAlgProps
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PkAlg where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning

Rep : @0 List UInt8 → Set
Rep = Sum (Sum X509.RSAPkAlg X509.EcPkAlg)
          (Σₚ X509.SignAlg (λ _ sa → False (X509.SignAlg.getSignAlgOIDbs sa ∈? X509.PKOID.Supported)))

equivalent : Equivalent Rep X509.PkAlg
proj₁ equivalent (inj₁ (inj₁ x)) = X509.PkAlg.rsapkalg x
proj₁ equivalent (inj₁ (inj₂ x)) = X509.PkAlg.ecpkalg x
proj₁ equivalent (inj₂ (mk×ₚ fstₚ₁ sndₚ₁ refl)) = X509.PkAlg.otherpkalg fstₚ₁ sndₚ₁
proj₂ equivalent (X509.PkAlg.rsapkalg x) = inj₁ (inj₁ x)
proj₂ equivalent (X509.PkAlg.ecpkalg x) = inj₁ (inj₂ x)
proj₂ equivalent (X509.PkAlg.otherpkalg x o∉) = inj₂ (mk×ₚ x o∉ refl)

iso : Iso Rep X509.PkAlg
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)) = refl
proj₁ (proj₂ iso) (Aeres.Grammar.Sum.inj₂ (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ refl)) = refl
proj₂ (proj₂ iso) (X509.PkAlg.rsapkalg x) = refl
proj₂ (proj₂ iso) (X509.PkAlg.ecpkalg x) = refl
proj₂ (proj₂ iso) (X509.PkAlg.otherpkalg sa x) = refl

@0 noconfRSA-EC : NoConfusion X509.RSAPkAlg X509.EcPkAlg
noconfRSA-EC {xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkTLV{l} len (X509.mkRSAPkAlgFields (singleton _ refl) param refl) len≡ bs≡) (mkTLV{l₁} len₁ (X509.mkEcPkAlgFields{p = p} (singleton _ refl) param₁ refl) len≡₁ bs≡₁) =
  contradiction{P = X509.PKOID.RsaEncPk ++ Singleton.x param ++ ys₁ ≡ X509.PKOID.EcPk ++ p ++ ys₂ }
    (Lemmas.++-cancel≡ˡ _ _ l≡ (∷-injectiveʳ bs≡'))
    λ ()
  where
  @0 bs≡' : _≡_ {A = List UInt8}
              (Tag.Sequence ∷ l  ++ X509.PKOID.RsaEncPk ++ Singleton.x param ++ ys₁)
              (Tag.Sequence ∷ l₁ ++ X509.PKOID.EcPk ++ p ++ ys₂)
  bs≡' = begin
    _ ≡⟨ cong (Tag.Sequence ∷_) (sym (++-assoc l _ ys₁)) ⟩
    (Tag.Sequence ∷ l ++ X509.PKOID.RsaEncPk ++ Singleton.x param) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
    xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
    xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
    (Tag.Sequence ∷ l₁ ++ X509.PKOID.EcPk ++ p) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (++-assoc l₁ _ ys₂) ⟩
    _ ∎

  @0 l≡ : l ≡ l₁
  l≡ = Length.nonnesting (∷-injectiveʳ bs≡') len len₁

@0 noconfSA-RSA : NoConfusion (Σₚ X509.SignAlg (λ _ sa → False (X509.SignAlg.getSignAlgOIDbs sa ∈? X509.PKOID.Supported))) X509.RSAPkAlg
noconfSA-RSA{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mk×ₚ val@(mkTLV{l = l}{v} len (X509.SignAlg.mkSignAlgFields{p = p} signOID param refl) len≡₁ bs≡) o∉ refl) (mkTLV{l = l₁}{v₁} len₁ (X509.mkRSAPkAlgFields self self refl) len≡ bs≡₁)
  with OID.serialize ∘ X509.SignAlg.SignAlgFields.signOID ∘ TLV.val $ val
... | singleton o refl =
  contradiction (subst (_∈ X509.PKOID.Supported) (sym o≡) (toWitness{Q = _ ∈? _ } tt)) (toWitnessFalse o∉)
  where
  @0 bs≡' : _≡_{A = List UInt8} (Tag.Sequence ∷ l ++ o ++ p ++ ys₁) (Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂)
  bs≡' = begin Tag.Sequence ∷ l ++ o ++ p ++ ys₁ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
               (Tag.Sequence ∷ l ++ o ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
               xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
               xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
               (Tag.Sequence ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
               Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂ ∎

  @0 l≡ : l ≡ l₁
  l≡ = Length.nonnesting (∷-injectiveʳ bs≡') len len₁

  @0 v≡ : v ≡ v₁
  v≡ = proj₁ $ Lemmas.length-++-≡ v ys₁ v₁ ys₂
                 (begin v ++ ys₁      ≡⟨ solve (++-monoid UInt8) ⟩ 
                        o ++ p ++ ys₁ ≡⟨ Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡' ⟩
                        v₁ ++ ys₂     ∎)
                 (begin length v ≡⟨ sym len≡₁ ⟩
                        getLength len ≡⟨ Length.unambiguous-getLength l≡ len len₁ ⟩
                        getLength len₁ ≡⟨ len≡ ⟩
                        length v₁ ∎)

  @0 o≡ : o ≡ X509.PKOID.RsaEncPk
  o≡ = TLV.nonnesting
         (Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡')
         signOID (toWitness{Q = parser2dec Logging.val TLV.nonnesting parseOID X509.PKOID.RsaEncPk} tt)


@0 noconfSA-EC : NoConfusion (Σₚ X509.SignAlg (λ _ sa → False (X509.SignAlg.getSignAlgOIDbs sa ∈? X509.PKOID.Supported))) X509.EcPkAlg
noconfSA-EC {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (mk×ₚ (mkTLV{l = l}{v} len val@(X509.SignAlg.mkSignAlgFields{p = p} signOID param₁ refl) len≡₁ bs≡) o∉ refl) (mkTLV{l = l₁}{v₁} len₁ (X509.mkEcPkAlgFields{p = p₁} self param refl) len≡ bs≡₁)
  with OID.serialize ∘ X509.SignAlg.SignAlgFields.signOID $ val
... | singleton o refl = contradiction (subst (_∈ X509.PKOID.Supported) (sym o≡) (toWitness{Q = _ ∈? _ } tt)) (toWitnessFalse o∉)
  where
  @0 bs≡' : _≡_{A = List UInt8} (Tag.Sequence ∷ l ++ o ++ p ++ ys₁) (Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂)
  bs≡' = begin Tag.Sequence ∷ l ++ o ++ p ++ ys₁ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
               (Tag.Sequence ∷ l ++ o ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
               xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
               xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
               (Tag.Sequence ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (++-assoc l₁ v₁ ys₂) ⟩
               Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂ ∎

  @0 l≡ : l ≡ l₁
  l≡ = Length.nonnesting (∷-injectiveʳ bs≡') len len₁

  @0 v≡ : v ≡ v₁
  v≡ = proj₁ $ Lemmas.length-++-≡ v ys₁ v₁ ys₂
                 (begin v ++ ys₁      ≡⟨ solve (++-monoid UInt8) ⟩ 
                        o ++ p ++ ys₁ ≡⟨ Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡' ⟩
                        v₁ ++ ys₂     ∎)
                 (begin length v ≡⟨ sym len≡₁ ⟩
                        getLength len ≡⟨ Length.unambiguous-getLength l≡ len len₁ ⟩
                        getLength len₁ ≡⟨ len≡ ⟩
                        length v₁ ∎)

  @0 o≡ : o ≡ X509.PKOID.EcPk
  o≡ = TLV.nonnesting
         (Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡')
         signOID (toWitness{Q = parser2dec Logging.val TLV.nonnesting parseOID X509.PKOID.EcPk} tt)


@0 nonnesting : NonNesting X509.PkAlg
nonnesting =
  equivalent-nonnesting equivalent
    (NonNesting.sumRestriction
      (nonnestingSum TLV.nonnesting TLV.nonnesting noconfRSA-EC)
      (nonnestingΣₚ₁ TLV.nonnesting)
      restr)
  where
  @0 restr : NonNesting.Restriction (Sum X509.RSAPkAlg X509.EcPkAlg) (Σₚ X509.SignAlg _)
  restr{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ (inj₁ (mkTLV{l = l}{v} len val len≡ bs≡)) (mk×ₚ (mkTLV{l = l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) _ refl) =
    begin (xs₁ ≡⟨ bs≡ ⟩
          Tag.Sequence ∷ l  ++ v  ≡⟨ cong₂ (λ x y → Tag.Sequence ∷ x ++ y) l≡ v≡ ⟩
          Tag.Sequence ∷ l₁ ++ v₁ ≡⟨ sym bs≡₁ ⟩
          xs₂                     ∎)
    where
    @0 bs≡' : _≡_{A = List UInt8} (Tag.Sequence ∷ l ++ v ++ ys₁) (Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂)
    bs≡' = begin Tag.Sequence ∷ l ++ v ++ ys₁ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 (Tag.Sequence ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                 xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                 xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                 (Tag.Sequence ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂ ∎
    @0 l≡ : l ≡ l₁
    l≡ = Length.nonnesting (∷-injectiveʳ bs≡') len len₁

    @0 v≡ : v ≡ v₁
    v≡ = proj₁ $ Lemmas.length-++-≡ v ys₁ v₁ ys₂
                   (begin v ++ ys₁ ≡⟨ Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡' ⟩
                          v₁ ++ ys₂ ∎)
                   (begin (length v ≡⟨ sym len≡ ⟩
                          getLength len ≡⟨ Length.unambiguous-getLength l≡ len len₁ ⟩
                          getLength len₁ ≡⟨ len≡₁ ⟩
                          length v₁ ∎))
  restr{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ (inj₂ (mkTLV{l = l}{v} len val len≡ bs≡)) (mk×ₚ (mkTLV{l = l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) _ refl) =
    begin (xs₁ ≡⟨ bs≡ ⟩
          Tag.Sequence ∷ l ++ v ≡⟨ cong₂ (λ x y → _ ∷ x ++ y) l≡ v≡ ⟩
          Tag.Sequence ∷ l₁ ++ v₁ ≡⟨ sym bs≡₁ ⟩
          xs₂ ∎)
    where
    @0 bs≡' : _≡_{A = List UInt8} (Tag.Sequence ∷ l ++ v ++ ys₁) (Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂)
    bs≡' = begin Tag.Sequence ∷ l ++ v ++ ys₁ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 (Tag.Sequence ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                 xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                 xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                 (Tag.Sequence ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂ ∎

    @0 l≡ : l ≡ l₁
    l≡ = Length.nonnesting (∷-injectiveʳ bs≡') len len₁

    @0 v≡ : v ≡ v₁
    v≡ = proj₁ $ Lemmas.length-++-≡ v ys₁ v₁ ys₂
                   (begin v ++ ys₁ ≡⟨ Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡' ⟩
                          v₁ ++ ys₂ ∎)
                   (begin (length v ≡⟨ sym len≡ ⟩
                          getLength len ≡⟨ Length.unambiguous-getLength l≡ len len₁ ⟩
                          getLength len₁ ≡⟨ len≡₁ ⟩
                          length v₁ ∎))

@0 unambiguous : Unambiguous X509.PkAlg
unambiguous =
  isoUnambiguous iso
    (unambiguousSum
      (unambiguousSum
        (TLV.unambiguous RSAProps.unambiguous)
        (TLV.unambiguous EcProps.unambiguous)
        noconfRSA-EC)
      (unambiguousΣₚ (TLV.unambiguous SignAlgProps.unambiguous)
        λ where
          {xs} a → T-unique)
      (symNoConfusion{A = Σₚ _ λ _ sa → False _}{B = Sum X509.RSAPkAlg X509.EcPkAlg}
        (NoConfusion.sumₚ
          {A = Σₚ X509.SignAlg λ _ sa → False (X509.SignAlg.getSignAlgOIDbs sa ∈? X509.PKOID.Supported)}
          {B = X509.RSAPkAlg}{C = X509.EcPkAlg}
          noconfSA-RSA noconfSA-EC)))
