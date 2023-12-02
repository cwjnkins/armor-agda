open import Aeres.Data.Base64.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.PEM.RFC5234.TCB where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.Sum         Char

WSP = Sum (λ x → Erased (x ≡ [ ' ' ])) (λ x → Erased (x ≡ [ '\t' ]))

data EOL : @0 List Char → Set where
  crlf : EOL ('\r' ∷ [ '\n' ])
  cr   : EOL [ '\r' ]
  lf   : EOL [ '\n' ]
