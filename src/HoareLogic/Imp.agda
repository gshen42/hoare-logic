module HoareLogic.Imp where

open import Agda.Builtin.FromNat
open import Data.String using (String)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Data.Nat.Literals as NatLiterals
open import Data.Unit using (⊤)
open import Data.Product using (_×_)
open import Function.Equivalence using (_⇔_)
open import HoareLogic.Map
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Reflection as Rfl using (TC; Term; _>>=_)

infix  79 !_
infixl 78 _*_
infixl 77 _+_ _-_
infix  75 _==_ _<=_
infixr 74 _&&_
infix  73 _:=_ if_then_else_end while_then_end
infixr 72 _;_
infix  71 _↦_ _=[_]=>_

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

data Com : Set where
  skip : Com
  _:=_ : String → Expr `ℕ → Com
  _;_  : Com → Com → Com -- this is the greek question mark not semicolon
  if_then_else_end : Expr `Bool → Com → Com → Com
  while_then_end   : Expr `Bool → Com → Com

-- compute the factorial of the number stored in X
factorial : Com
factorial =
  Z := X ;
  Y := 1 ;
  while ! (Z == 0) then
    Y := Y * Z ;
    Z := Z - 1
  end

data _=[_]=>_ : State → Com → State → Set where
  skip   : ∀ {s} →
           s =[ skip ]=> s
  asgn   : ∀ {s} {x} {e} n →
           eval s e ≡ n →
           s =[ x := e ]=> (x ↦ n , s)
  seq    : ∀ {s s′ s″} {c₁ c₂} →
           s =[ c₁ ]=> s′ →
           s′ =[ c₂ ]=> s″ →
           s =[ c₁ ; c₂ ]=> s″
  ifᵗ    : ∀ {s s′} {b} {c₁ c₂} →
           eval s b ≡ true →
           s =[ c₁ ]=> s′ →
           s =[ if b then c₁ else c₂ end ]=> s′
  ifᶠ    : ∀ {s s′} {b} {c₁ c₂} →
           eval s b ≡ false →
           s =[ c₂ ]=> s′ →
           s =[ if b then c₁ else c₂ end ]=> s′
  whileᵗ : ∀ {s s′ s″} {b} {c} →
           eval s b ≡ true →
           s =[ c ]=> s′ →
           s′ =[ while b then c end ]=> s″ →
           s =[ while b then c end ]=> s″
  whileᶠ : ∀ {s} {b} {c} →
           eval s b ≡ false →
           s =[ while b then c end ]=> s

ex₁ : Com
ex₁ =
  X := 2 ;
  if (X <= 1)
    then Y := 3
    else Z := 4
  end

_ : s₀ =[ ex₁ ]=> (Z ↦ 4 , X ↦ 2)
_ = seq (asgn 2 refl) (ifᶠ refl (asgn 4 refl))

ex₂ : Com
ex₂ =
  X := 0 ;
  Y := 1 ;
  Z := 2

_ : s₀ =[ ex₂ ]=> (Z ↦ 2 , Y ↦ 1 , X ↦ 0)
_ = seq (asgn 0 refl) (seq (asgn 1 refl) (asgn 2 refl))

-- sum the numbers from 1 to X in Y
sum : Com
sum =
  Y := 0 ;
  while ! (X == 0) then
    Y := Y + X ;
    X := X - 1
  end

_ : (X ↦ 2) =[ sum ]=> (X ↦ 0 , Y ↦ 3 , X ↦ 1 , Y ↦ 2 ,  Y ↦ 0 , X ↦ 2)
_ = seq (asgn 0 refl) (whileᵗ refl (seq (asgn 2 refl) (asgn 1 refl)) (whileᵗ refl (seq (asgn 3 refl) (asgn 0 refl)) (whileᶠ refl)))

=[]=>-deterministic : ∀ {c} {s s′ s″} →
                       s =[ c ]=> s′ →
                       s =[ c ]=> s″ →
                       s′ ≡ s″
=[]=>-deterministic {skip} skip skip = refl
=[]=>-deterministic {x := e} (asgn n refl) (asgn n refl) = refl
=[]=>-deterministic {c₁ ; c₂} (seq a b) (seq c d) rewrite =[]=>-deterministic a c | =[]=>-deterministic b d = refl
=[]=>-deterministic {if b then c₁ else c₂ end} (ifᵗ x y) (ifᵗ z w) rewrite =[]=>-deterministic y w = refl
=[]=>-deterministic {if b then c₁ else c₂ end} (ifᵗ x y) (ifᶠ z w) with () ← trans (sym x) z
=[]=>-deterministic {if b then c₁ else c₂ end} (ifᶠ x y) (ifᵗ z w) with () ← trans (sym x) z
=[]=>-deterministic {if b then c₁ else c₂ end} (ifᶠ x y) (ifᶠ z w) rewrite =[]=>-deterministic y w = refl
=[]=>-deterministic {while b then c end} (whileᵗ x y z) (whileᵗ w u v) rewrite =[]=>-deterministic y u | =[]=>-deterministic z v = refl
=[]=>-deterministic {while b then c end} (whileᵗ x y z) (whileᶠ w) with () ← trans (sym x) w
=[]=>-deterministic {while b then c end} (whileᶠ w) (whileᵗ x y z) with () ← trans (sym w) x
=[]=>-deterministic {while b then c end} (whileᶠ x) (whileᶠ y) = refl
