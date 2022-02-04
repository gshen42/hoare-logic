module HoareLogic.Hoare where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as Nat using (ℕ; _<_)
open import Data.Nat.Literals as NatLiterals
open import Data.String using (String)
open import HoareLogic.Imp
open import HoareLogic.Maps
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Assertion : Set₁
Assertion = State → Set

⟪_⟫_⟪_⟫ : Assertion → Com → Assertion → Set
⟪ P ⟫ c ⟪ Q ⟫ = ∀ s s′ → s =[ c ]=> s′ → P s → Q s′

hoare-post-true : ∀ {P Q} {c} →
                  (∀ s → Q s) →
                  ⟪ P ⟫ c ⟪ Q ⟫
hoare-post-true f _ s′ _ _  = f s′

hoare-pre-false : ∀ {P Q} {c} →
                  (∀ s → P s → ⊥) →
                  ⟪ P ⟫ c ⟪ Q ⟫
hoare-pre-false f s s′ s==>s′ Ps = ⊥-elim (f s Ps)

_[_≔_] : Assertion → String → Expr ℕ → Assertion
P [ X ≔ e ] = λ s → P (X ↦ eval s e , s)

hoare-asgn : ∀ Q X a →
             ⟪ Q [ X ≔ a ] ⟫ X := a ⟪ Q ⟫
hoare-asgn Q X a s s′ (asgn n refl) Ps = Ps

assn-sub-example : ⟪ (λ s → s X < 5) [ X ≔ X + (num 1) ] ⟫ X := X + (num 1) ⟪ (λ s → s X < 5) ⟫
assn-sub-example = hoare-asgn _ _ _

assn-sub-example₂ : ⟪ (λ s → s X < 4) ⟫ X := X + (num 1) ⟪ (λ s → s X < 5) ⟫
assn-sub-example₂ = hoare-asgn _ _ _
