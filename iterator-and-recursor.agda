-- developed with Agda version 2.6.2.1

variable A : Set

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Bool : Set where
  false : Bool
  true : Bool

-- iterator and recursor for ℕ

Itℕ : A → (A → A) → ℕ → A
Itℕ z s zero = z
Itℕ z s (suc n) = s (Itℕ z s n)

Rℕ : A → (ℕ → A → A) → ℕ → A
Rℕ z s zero = z
Rℕ z s (suc n) = s n (Rℕ z s n)

-- less than or equal to

_≤_ : ℕ → ℕ → Bool 
zero ≤ n = true
suc m ≤ zero = false
suc m ≤ suc n = m ≤ n

-- using the Recursor nested in itself

_≤-r_ : ℕ → ℕ → Bool 
_≤-r_ = Rℕ (λ n → true) (λ m m≤ → Rℕ false λ n _ → m≤ n)

-- whether an ∈ ℕ is even

-- with three patterns

even3 :  ℕ → Bool
even3 zero = true
even3 (suc zero) = false
even3 (suc (suc n)) = even3 n 

-- with two patterns

not : Bool → Bool
not true = false
not false = true

even2 : ℕ → Bool
even2 zero = true
even2 (suc n) = not (even2 n)

-- the version with three patterns using products and the Iterator

infixr 4 _,_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_

even3-aux : ℕ → Bool × Bool
even3-aux zero = true , false
even3-aux (suc n) = proj₂ (even3-aux n) , proj₁ (even3-aux n)

even3-aux-it : ℕ → Bool × Bool
even3-aux-it = Itℕ (true , false) (λ p → proj₂ p , proj₁ p)

even3-it : ℕ → Bool
even3-it n = proj₁ (even3-aux-it n)

-- the version with two patterns using the Iterator

even2-it : ℕ → Bool 
even2-it = Itℕ true not

-- summation

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

sum : ℕ → ℕ
sum zero = 0
sum (suc x) = x + sum x

-- using the Recursor

sum-r : ℕ → ℕ 
sum-r = Rℕ 0 (λ x sum → x + sum)

-- the greater of two ∈ ℕ

max : ℕ → ℕ → ℕ
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = 1 + max m n

-- using the Recursor and Iterator

pred-r : ℕ → ℕ 
pred-r = Rℕ 0 λ pred-n _ → pred-n

max-it : ℕ → ℕ → ℕ
max-it = Itℕ (λ m → m) (λ max-m suc-n → suc (max-m (pred-r suc-n)))

-- the value of an index in the Fibonacci sequence

fib : ℕ → ℕ
fib zero = 1
fib (suc zero) = 1
fib (suc (suc n)) = fib (suc n) + fib n

-- using the products and the Iterator

fib-aux : ℕ → ℕ × ℕ
fib-aux zero = 1 , 1
fib-aux (suc n) =  proj₂ (fib-aux n), proj₁ (fib-aux n) + proj₂ (fib-aux n)

fib-aux-it : ℕ → ℕ × ℕ 
fib-aux-it = Itℕ (1 , 1) (λ p → (proj₂ p) , proj₁ p + proj₂ p)

fib-it : ℕ → ℕ
fib-it n = proj₁ (fib-aux-it n)

-- equality of two ∈ ℕ

eq : ℕ → ℕ → Bool 
eq zero zero = true
eq zero (suc y) = false
eq (suc x) zero = false
eq (suc x) (suc y) = eq x y

-- using the Iterator nested in itself and the Recursor

eq-it : ℕ → ℕ → Bool
eq-it = Itℕ (Itℕ true (λ suc-y → false)) (λ eq-x → Rℕ false λ y _ → eq-x y)

-- remainder after division

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

rem-aux : (ℕ → ℕ) → ℕ → ℕ -- for use as `s` in Itℕ
rem-aux rem-m n 
  = if (eq (rem-m n) n) then 0 else (1 + (rem-m n))

rem : ℕ → ℕ → ℕ 
rem zero n = 0
rem (suc m) n = rem-aux (rem m) n

-- using the Iterator

rem-it : ℕ → ℕ → ℕ 
rem-it = Itℕ (λ _ → 0) rem-aux

-- integer division

div-aux : ℕ → (ℕ → ℕ) → ℕ → ℕ -- for use as `s` in Rℕ
div-aux m div-m n 
  = if eq (rem (suc m) n) 0 then 1 + div-m n else div-m n

div : ℕ → ℕ → ℕ
div zero n = 0
div (suc m) n = div-aux m (div m) n

-- using the Recursor

div-r : ℕ → ℕ → ℕ 
div-r = Rℕ (λ _ → 0) div-aux