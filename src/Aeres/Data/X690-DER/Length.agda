open import Aeres.Binary
open import Aeres.Prelude

module Aeres.Data.X690-DER.Length where

open Base256

module Length where
  open import Aeres.Data.X690-DER.Length.TCB        public
  open import Aeres.Data.X690-DER.Length.Properties public
  open import Aeres.Data.X690-DER.Length.Serializer public

open Length public
  using (Length ; getLength)
  hiding (module Length)

open import Aeres.Data.X690-DER.Length.Parser public
