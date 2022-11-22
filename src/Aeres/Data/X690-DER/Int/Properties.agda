{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Grammar.Definitions UInt8
open import Aeres.Prelude

module Aeres.Data.X690-DER.Int.Properties where

unambiguous : Unambiguous IntegerValue
unambiguous self self = refl

-- instance
--   IntValEq : Eq (Exists─ (List UInt8) Singleton)
--   Eq._≟_ IntValEq (─ bs₁ , singleton s₁ refl) (─ bs₂ , singleton s₂ refl)
--     with s₁ ≟ s₂
--   ... | yes refl = yes refl
--   ... | no ¬eq = no λ where refl → contradiction refl ¬eq

--   eq≋ : Eq≋ IntegerValue
--   eq≋ = Eq⇒Eq≋ it
