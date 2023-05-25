module Consegne.CompilerEx where

open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.List
open import Library.List.Properties

open import Consegne.AexpBexp

------------------
-- Automa a pila
------------------

-- Istruzioni

data Instr : Set where
   LOADI : Val → Instr     -- carica un valore sullo stack
   LOAD  : Vname → Instr   -- carica il valore di una variabile sullo stack
   ADD   : Instr           -- rimuove i primi due elementi dello stack
                           -- e carica la loro somma sullo stack

Stack = List Val    -- uno stack è una pila di valori
Prog  = List Instr  -- un programma è una lista di istruzioni

-- exec1 esegue una singola istruzione modificando lo stack
-- utilizzando uno stato per trattare le variabili 

exec1 : Instr → State → Stack → Stack
exec1 (LOADI n) s       stk         = n :: stk
exec1 (LOAD x)  s       stk         = (s x) :: stk
exec1 ADD       s (m :: (n :: stk)) = (m + n) :: stk
exec1 ADD       s        _          = []    -- questo caso è un errore!

-- exec itera exec1 su un programma p : Prog

exec : Prog → State → Stack → Stack
exec []        _ stk = stk
exec (i :: is) s stk = exec is s (exec1 i s stk)

----------------
-- Compilatore
----------------

comp : Aexp → Prog
comp (N n)        = (LOADI n) :: []
comp (V x)        = (LOAD x) :: []
comp (Plus a₁ a₂) = (comp a₂) ++ (comp a₁) ++ (ADD :: [])

-- La definizione di comp, benché corretta, rende più complessa
-- la dimostrazione del teorema di correttezza del compilatore.
-- Al suo posto si utilizza comp' tale che invece di definire mediante _++_
-- la lista dei comandi associati ad un'espressione a utilizza un secondo
-- parametro p : Prog dinananzi al quale costruisce la compilazione
-- di a utilizzando soltanto il costruttore _::_

comp' : Aexp → Prog → Prog  
comp' (N n) p = (LOADI n) :: p
comp' (V x) p = (LOAD x) :: p
comp' (Plus a₁ a₂) p = comp' a₂ (comp' a₁ (ADD :: p))

-- Il seguente lemma stabilisce che comp' a p == comp a ++ p
-- onde possiamo definire il compilatore compile a = comp' a []

compile : Aexp → Prog
compile a = comp' a []

-- Suggerimento: nella prova si usi rewrite con l'inversa di ++-assoc

++-assoc2 : ∀{A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
++-assoc2 xs ys zs = symm (++-assoc xs ys zs)

lemma-comp : ∀(a : Aexp) (p : Prog) → comp a ++ p == comp' a p
lemma-comp (N x) p = refl
lemma-comp (V x) p = refl
lemma-comp (Plus a a₁) p =
  begin
    (comp a₁ ++ comp a ++ ADD :: []) ++ p ==⟨ ++-assoc2 (comp a₁) (comp a ++ ADD :: []) p ⟩
    comp a₁ ++ ((comp a ++ ADD :: []) ++ p) ==⟨ cong (comp a₁ ++_) (++-assoc2 (comp a) (ADD :: []) p) ⟩
    comp a₁ ++ comp a ++ ((ADD :: []) ++ p) ==⟨⟩
    comp a₁ ++ comp a ++ ADD :: p ==⟨ lemma-comp a₁ (comp a ++ ADD :: p) ⟩
    comp' a₁ (comp a ++ ADD :: p) ==⟨ cong (comp' a₁) (lemma-comp a (ADD :: p)) ⟩
    comp' a₁ (comp' a (ADD :: p)) ⟨⟩==
    comp' (Plus a a₁) p
  end

--------------------------------
-- Correttezza rispetto ad aval
--------------------------------

-- Il teorema stabilisce che l'esecuzione mediante un automa a pila
-- del risultato della compilazione di un'espressione a nello stato s
-- produce una pila il cui unico elemento è aval a s.

-- Per dimostrare il teorema si dimostri il seguente lemma, che
-- generalizza l'enunciato del teorema al caso in cui a sia compilato
-- dinanzi ad un programma p e che l'esecuzione inizi con uno stack
-- stk arbitrario
-- a₁

-- exec (i :: is) s stk = exec is s (exec1 i s stk)

Lemma : ∀(a : Aexp) (s : State) (stk : Stack) (p : Prog)
           → exec (comp' a p) s stk == exec p s ((aval a s) :: stk)
           
Lemma (N x) s stk p =
  begin
    exec (comp' (N x) p) s stk ==⟨⟩
    exec ((LOADI x) :: p) s stk ==⟨⟩
    exec p s (exec1 (LOADI x) s stk) ==⟨⟩
    exec p s (x :: stk) ==⟨⟩
    exec p s ((aval (N x) s) :: stk)
  end
Lemma (V x) s stk p =
  begin
    exec (comp' (V x) p) s stk ==⟨⟩
    exec((LOAD x) :: p) s stk ==⟨⟩
    exec p s (exec1 (LOAD x) s stk) ==⟨⟩
    exec p s ((s x) :: stk) ==⟨⟩
    exec p s ((aval (V x) s) :: stk)
  end
Lemma (Plus Aexpx Aexpy) s stk p =
  begin
    exec (comp' Aexpy (comp' Aexpx (ADD :: p))) s stk ==⟨⟩{!!}

-- A questo punto basta specializzare Lemma al caso in cui p == [] e stk == []

Teorema : ∀(a : Aexp) (s : State)
           → exec (compile a) s [] == [ (aval a s) ]
           
Teorema a s = {!!}
