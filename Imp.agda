module Imp where

open import Agda.Builtin.FromNat
open import Data.String using (String)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Data.Nat.Literals as NatLiterals
open import Data.Unit using (⊤)
open import Data.Product using (_×_)
open import Function.Equivalence using (_⇔_)
open import Map
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reflection as Rfl using (TC; Term; _>>=_)

infix  79 !_
infixl 78 _*_
infixl 77 _+_ _-_
infix  75 _==_ _<=_
infixr 74 _&&_
infix  71 _↦_

data Type : Set where
  `ℕ    : Type
  `Bool : Type

⟦_⟧ : Type → Set
⟦ `ℕ    ⟧ = ℕ
⟦ `Bool ⟧ = Bool

-- We could have written `Expr : Set → Set`, the problem is that the unification doesn't work very well with `Set`.
data Expr : Type → Set where
  num   : ℕ → Expr `ℕ
  var   : String → Expr `ℕ
  _+_   : Expr `ℕ → Expr `ℕ → Expr `ℕ
  _-_   : Expr `ℕ → Expr `ℕ → Expr `ℕ
  _*_   : Expr `ℕ → Expr `ℕ → Expr `ℕ
  true  : Expr `Bool
  false : Expr `Bool
  _==_  : Expr `ℕ → Expr `ℕ → Expr `Bool
  _<=_  : Expr `ℕ → Expr `ℕ → Expr `Bool
  !_    : Expr `Bool → Expr `Bool
  _&&_  : Expr `Bool → Expr `Bool → Expr `Bool

instance
  -- so we can write natural number literal `n` for `(num n)`
  _ : Number (Expr `ℕ)
  _ = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → num n
    }

  _ : Number ℕ
  _ = NatLiterals.number

StringOrVar : String → Term → TC ⊤
StringOrVar s hole = inferType hole >>=
  λ where
    (def (quote String) _) → unify hole (lit (string s))
    (def (quote Expr) _)   → unify hole (con (quote var) ((vArg (lit (string s))) ∷ []))
    goal                   → typeError (strErr "wrong usage" ∷ [])
  where
  open Rfl hiding (var)

macro
  W X Y Z : Term → TC ⊤
  W = StringOrVar "W"
  X = StringOrVar "X"
  Y = StringOrVar "Y"
  Z = StringOrVar "Z"

State = Map ℕ

eval : ∀ {A} → State → Expr A → ⟦ A ⟧
eval s (num n)    = n
eval s (var x)    = s x
eval s (e₁ + e₂)  = (eval s e₁) ℕ.+ (eval s e₂)
eval s (e₁ - e₂)  = (eval s e₁) ℕ.∸ (eval s e₂)
eval s (e₁ * e₂)  = (eval s e₁) ℕ.* (eval s e₂)
eval s true       = Bool.true
eval s false      = Bool.false
eval s (e₁ == e₂) = (eval s e₁) ℕ.≡ᵇ (eval s e₂)
eval s (e₁ <= e₂) = (eval s e₁) ℕ.≤ᵇ (eval s e₂)
eval s (! e)      = Bool.not (eval s e)
eval s (e₁ && e₂) = (eval s e₁) Bool.∧ (eval s e₂)

s₀ : State
s₀ = ·↦ 0

_↦_ : String → ℕ → State
x ↦ v = x ↦ v , s₀

_ : eval (X ↦ 5) (3 + X * 2) ≡ 13
_ = refl

_ : eval (X ↦ 5 , Y ↦ 4) (Z + X * Y) ≡ 20
_ = refl

_ : eval (X ↦ 5) (true && ! (X <= 4)) ≡ true
_ = refl
