-- developed with Agda version 2.6.2.1

variable A B C : Set

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

variable l m n : ℕ

infixr 5 _∷_
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- n-dimensional vector

Vector : ℕ → Set
Vector m = Vec ℕ m

-- m row, n column matrix

Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vector n) m

infix 6 _+_ 
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- vector added to vector

_v+v_ : Vector n → Vector n → Vector n
[] v+v [] = []
(x ∷ xs) v+v (y ∷ ys) = x + y ∷ (xs v+v ys)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n

-- scalar multiplied by vector

_s*v_ : ℕ → Vector n → Vector n
n s*v [] = []
zero s*v (x ∷ xs) =  0 ∷ (zero s*v xs)
suc n s*v (x ∷ xs) = (suc n) * x ∷ ((suc n) s*v xs)

-- vector multiplied by matrix

_v*m_ : Vector m → Matrix m n → Vector n
_v*m_ {.zero} {n} [] [] = zeros {n = n}
    where
        zeros : {n : ℕ} → Vector n
        zeros {zero} = []
        zeros {suc n} = zero ∷ zeros {n}
_v*m_ {.(suc _)} {n} (head_v ∷ tail_v) (head_m ∷ tail_m) 
    = (head_v s*v head_m) v+v (tail_v v*m tail_m)

-- matrix multiplied by matrix

_m*m_ : Matrix l m → Matrix m n → Matrix l n
_m*m_ {.zero} {m} {n} [] mn = []
_m*m_ {.(suc _)} {m} {n} (head_lm ∷ tail_lm) mn
    = (head_lm v*m mn) ∷ (tail_lm m*m mn)

-- transpose matrix

t : Matrix m n → Matrix n m
t [] = emptyVecs
    where
        emptyVecs : {n : ℕ} → Vec (Vec A zero) n
        emptyVecs {n = zero} = []
        emptyVecs {n = suc pred-n} = [] ∷ emptyVecs {n = pred-n}
t (head_mn ∷ tail_mn) = zipWith _∷_ head_mn (t tail_mn)
    where
        zipWith : {n : ℕ} → (A → B → C) → Vec A n → Vec B n → Vec C n 
        zipWith f [] [] = []
        zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys