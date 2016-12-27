module AgdaBasics where

{-# IMPORT System.IO #-}

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + zero = zero
zero + suc y = suc y
suc x + zero = suc x
suc x + suc y = suc (suc (x + y))

_*_ : Nat -> Nat -> Nat
zero * zero = zero
zero * suc y = zero
suc x * zero = zero
suc x * suc y = (((x * y) + x) + y) + (suc zero)

_or_ : Bool -> Bool -> Bool
false or x = x
true or _ = true

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

identity : (A : Set) -> A -> A
identity A x = x

zero' : Nat
zero' = identity Nat zero

id : {A : Set} -> A -> A
id x = x

true' : Bool
true' = id true

silly : {A : Set}{x : A} -> A
silly {_}{x} = x

false' : Bool
false' = silly {x = false}

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: x₁) = f x :: map f x₁

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: x₁) = f x :: vmap f x₁

data Vec₂ (A : Set) : Nat -> Set where
  nil : Vec₂ A zero
  cons : (n : Nat) -> A -> Vec₂ A n -> Vec₂ A (suc n)

vmap₃ : {A B : Set}(n : Nat) -> (A -> B) -> Vec₂ A n -> Vec₂ B n
vmap₃ zero f nil = nil
vmap₃ (suc n) f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

data Empty : Set where
  empty : Fin zero -> Empty

magic' : {A : Set} -> Empty -> A
magic' (empty ())

-- programs as proofs
data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < suc n = true
suc m < suc n = m < n

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: x₁) = (suc zero) + (length x₁)

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A
