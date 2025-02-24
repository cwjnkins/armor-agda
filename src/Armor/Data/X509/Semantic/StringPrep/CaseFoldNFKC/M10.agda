{-# OPTIONS --erasure --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M10 where

open Armor.Grammar.IList UInt8

trie₁₀ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₁₀ = ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 143 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 183 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 144 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 184 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 184 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 145 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 185 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 146 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 186 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 186 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 147 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 187 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 148 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 188 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 188 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 149 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 189 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 150 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 190 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 190 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 151 ]) , (─ (# 240 ∷ # 144 ∷ # 144 ∷ [ # 191 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 152 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 128 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 153 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 129 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 154 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 130 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 130 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 155 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 131 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 156 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 132 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 157 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 133 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 158 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 134 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 134 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 159 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 135 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 160 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 136 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 136 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 161 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 137 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 162 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 138 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 138 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 163 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 139 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 139 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 164 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 140 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 140 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 144 ∷ # 144 ∷ [ # 165 ]) , (─ (# 240 ∷ # 144 ∷ # 145 ∷ [ # 141 ]) , cons (mkIListCons (utf84 (mkUTF8Char4 _ _ _ _ (toWitness {a? = inRange? 240 247 240 } tt) (toWitness {a? = inRange? 128 191 144 } tt) (toWitness {a? = inRange? 128 191 145 } tt) (toWitness {a? = inRange? 128 191 141 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 128 ]) , (─ ([ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 97 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 129 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 130 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 131 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 132 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 133 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 134 ]) , (─ ([ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 103 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 135 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 136 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 137 ]) , (─ ([ # 106 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 106 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 138 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 107 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 139 ]) , (─ ([ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 108 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 140 ]) , (─ ([ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 109 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 141 ]) , (─ ([ # 110 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 110 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 142 ]) , (─ ([ # 111 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 111 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 143 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 144 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 145 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 146 ]) , (─ ([ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 115 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 147 ]) , (─ ([ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 116 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 148 ]) , (─ ([ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 117 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 149 ]) , (─ ([ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 118 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 150 ]) , (─ ([ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 119 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 151 ]) , (─ ([ # 120 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 120 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 152 ]) , (─ ([ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 121 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 153 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 180 ]) , (─ ([ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 97 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 181 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 182 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 183 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 184 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 185 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 186 ]) , (─ ([ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 103 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 187 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 188 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 189 ]) , (─ ([ # 106 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 106 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 190 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 107 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 144 ∷ [ # 191 ]) , (─ ([ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 108 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 128 ]) , (─ ([ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 109 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 129 ]) , (─ ([ # 110 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 110 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 130 ]) , (─ ([ # 111 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 111 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 131 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 132 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 133 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 134 ]) , (─ ([ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 115 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 135 ]) , (─ ([ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 116 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 136 ]) , (─ ([ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 117 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 137 ]) , (─ ([ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 118 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 138 ]) , (─ ([ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 119 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 139 ]) , (─ ([ # 120 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 120 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 140 ]) , (─ ([ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 121 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 141 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 168 ]) , (─ ([ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 97 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 169 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 170 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 171 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 172 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 173 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 174 ]) , (─ ([ # 103 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 103 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 175 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 176 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 177 ]) , (─ ([ # 106 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 106 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 178 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 107 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 179 ]) , (─ ([ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 108 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 180 ]) , (─ ([ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 109 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 181 ]) , (─ ([ # 110 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 110 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 182 ]) , (─ ([ # 111 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 111 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 183 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 184 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 185 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 186 ]) , (─ ([ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 115 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 187 ]) , (─ ([ # 116 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 116 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 188 ]) , (─ ([ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 117 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 189 ]) , (─ ([ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 118 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 190 ]) , (─ ([ # 119 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 119 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 145 ∷ [ # 191 ]) , (─ ([ # 120 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 120 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 240 ∷ # 157 ∷ # 146 ∷ [ # 128 ]) , (─ ([ # 121 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 121 <? 128 } tt) refl)) nil refl)))
          ∷ []


