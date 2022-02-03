module HoareLogic.Maps where

open import Data.Bool using (Bool; true; false)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (yes; no)

infix  71 ·↦_
infixr 70 _↦_,_

Map : Set → Set
Map A = String → A

·↦_ : ∀ {A} → A → Map A
·↦_ v _ = v

_↦_,_ : ∀ {A} → String → A → Map A → Map A
_↦_,_ x v m x′ with x ≟ x′
... | yes _  = v
... | no  _  = m x′

_ : Map Bool
_ = "bar" ↦ true , "foo" ↦ true , ·↦ false
