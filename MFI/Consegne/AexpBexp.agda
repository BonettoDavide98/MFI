module Consegne.AexpBexp where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning

-- Sintassi delle espressioni aritmetiche: Aexp

Index = ℕ
data Vname : Set where
   Vn : Index -> Vname

X : Vname
X = Vn 0

Y : Vname
Y = Vn 1

Z : Vname
Z = Vn 2

_=ℕ_ : ℕ -> ℕ -> Bool
zero =ℕ zero = true
zero =ℕ succ m = false
succ n =ℕ zero = false
succ n =ℕ succ m = n =ℕ m

_=Vn_ : (x y : Vname) -> Bool
Vn i =Vn Vn j = i =ℕ j

-- Aexp ∋ a, a' ::= N n | V vn | Plus a a' 

data Aexp : Set where
  N : ℕ → Aexp                -- numerali
  V : Vname → Aexp            -- variabili
  Plus : Aexp → Aexp → Aexp   -- somma

-- aexp0 X + (1 + Y)

aexp0 : Aexp
aexp0 = Plus (V X) (Plus (N 1) (V Y))


-- Semantica delle espressioni aritmetiche

Val = ℕ
State = Vname → Val

aval : Aexp → State → Val
aval (N n) s       = n
aval (V vn) s      = s vn
aval (Plus a a') s = aval a s + aval a' s

st0 : State
st0 = λ x → 0

-- Funzione update: s [ x ::= v ] dove s ∈ State, x ∈ Vname, v ∈ Val

_[_::=_] : State → Vname → Val → State
(s [ x ::= v ]) y = if x =Vn y then v else s y

st1 : State
st1 = st0 [ X ::= 1 ]

st2 : State
st2 = st1 [ Y ::= 2 ]

-- Sostituzione: a [ a' / x ] dove a, a' ∈ Aexp, x ∈ Vname è la sostituzione di a' ad x in a

_[_/_] : Aexp → Aexp → Vname → Aexp
N n [ a' / x ]        = N n
V y [ a' / x ]        = if x =Vn y then a' else V y
Plus a₁ a₂ [ a' / x ] = Plus (a₁ [ a' / x ]) (a₂ [ a' / x ])

aexp1 : Aexp
aexp1 = aexp0 [ Plus (V Z) (N 3) / X ]

aexp2 : Aexp
aexp2 = aexp0 [ Plus (V X) (N 3) / X ]

-- Lemma di sostituzione

lemma-subst-aexp : ∀(a a' : Aexp) (x : Vname) (s : State) →
      aval (a [ a' / x ]) s == aval a (s [ x ::= aval a' s ])

lemma-subst-aexp (N n) a' x s = refl

lemma-subst-aexp (V y) a' x s with x =Vn y
... | true  = refl
... | false = refl

lemma-subst-aexp (Plus a₁ a₂) a' x s =
    begin
      aval (a₁ [ a' / x ]) s + aval (a₂ [ a' / x ]) s ==⟨ cong2 _+_ h1 h2 ⟩
      aval a₁ (s [ x ::= aval a' s ]) + aval a₂ (s [ x ::= aval a' s ])
    end

    where

      h1 : aval (a₁ [ a' / x ]) s == aval a₁ (s [ x ::= aval a' s ])
      h1 = lemma-subst-aexp a₁ a' x s

      h2 : aval (a₂ [ a' / x ]) s == aval a₂ (s [ x ::= aval a' s ])
      h2 = lemma-subst-aexp a₂ a' x s

-- Expressioni booleane:       Bexp ∋ b, b' ::= B bc | Less a a' | Not b | And b b'

data Bexp : Set where
   B : Bool -> Bexp               -- boolean constants
   Less : Aexp -> Aexp -> Bexp    -- less than
   Not : Bexp -> Bexp             -- negation
   And : Bexp -> Bexp -> Bexp     -- conjunction

_<ℕ_ : ℕ -> ℕ -> Bool          --  n <ℕ m == true if n < m 
zero <ℕ   zero   = false      --  in the ordinary ordering of ℕ
zero <ℕ   succ n = true
succ n <ℕ zero   = false
succ n <ℕ succ m = n <ℕ m

bval : Bexp → State → Bool
bval (B cb) s       = cb
bval (Less a₁ a₂) s = aval a₁ s <ℕ aval a₂ s
bval (Not b) s      = not (bval b s)
bval (And b₁ b₂) s  = bval b₁ s && bval b₂ s
