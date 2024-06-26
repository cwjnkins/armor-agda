{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M12 where

open Armor.Grammar.IList UInt8

trie₁₂ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₁₂ = ((# 240 ∷ # 157 ∷ # 149 ∷ [ # 187 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 149 ∷ [ # 188 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 149 ∷ [ # 189 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 149 ∷ [ # 190 ]) , (─ ([ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 115 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 149 ∷ [ # 191 ]) , (─ ([ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 128 ]) , (─ ([ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 117 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 129 ]) , (─ ([ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 130 ]) , (─ ([ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 131 ]) , (─ ([ # 120 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 120 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 132 ]) , (─ ([ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 121 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 133 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 160 ]) , (─ ([ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 161 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 162 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 163 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 164 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 165 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 166 ]) , (─ ([ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 167 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 168 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 169 ]) , (─ ([ # 106 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 106 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 170 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 171 ]) , (─ ([ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 108 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 172 ]) , (─ ([ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 173 ]) , (─ ([ # 110 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 110 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 174 ]) , (─ ([ # 111 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 111 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 175 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 176 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 177 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 178 ]) , (─ ([ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 115 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 179 ]) , (─ ([ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 180 ]) , (─ ([ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 117 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 181 ]) , (─ ([ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 182 ]) , (─ ([ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 183 ]) , (─ ([ # 120 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 120 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 184 ]) , (─ ([ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 121 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 150 ∷ [ # 185 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 148 ]) , (─ ([ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 149 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 150 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 151 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 152 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 153 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 154 ]) , (─ ([ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 155 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 156 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 157 ]) , (─ ([ # 106 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 106 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 158 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 159 ]) , (─ ([ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 108 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 160 ]) , (─ ([ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 161 ]) , (─ ([ # 110 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 110 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 162 ]) , (─ ([ # 111 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 111 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 163 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 164 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 165 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 166 ]) , (─ ([ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 115 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 167 ]) , (─ ([ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 168 ]) , (─ ([ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 117 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 169 ]) , (─ ([ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 170 ]) , (─ ([ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 171 ]) , (─ ([ # 120 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 120 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 172 ]) , (─ ([ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 121 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 151 ∷ [ # 173 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 136 ]) , (─ ([ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 137 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 138 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 139 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 140 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 141 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 142 ]) , (─ ([ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 143 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 144 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 145 ]) , (─ ([ # 106 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 106 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 146 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 147 ]) , (─ ([ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 108 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 148 ]) , (─ ([ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 109 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 149 ]) , (─ ([ # 110 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 110 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 150 ]) , (─ ([ # 111 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 111 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 151 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 152 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 153 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 154 ]) , (─ ([ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 115 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 155 ]) , (─ ([ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 116 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 156 ]) , (─ ([ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 117 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 157 ]) , (─ ([ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 118 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 158 ]) , (─ ([ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 119 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 159 ]) , (─ ([ # 120 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 120 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 160 ]) , (─ ([ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 121 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 161 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 188 ]) , (─ ([ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 97 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 189 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 190 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 152 ∷ [ # 191 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 153 ∷ [ # 128 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 153 ∷ [ # 129 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 153 ∷ [ # 130 ]) , (─ ([ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 103 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 153 ∷ [ # 131 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 153 ∷ [ # 132 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 153 ∷ [ # 133 ]) , (─ ([ # 106 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 106 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 153 ∷ [ # 134 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {Q = 107 <? 128 } tt) refl)) nil refl)))
          ∷ []


