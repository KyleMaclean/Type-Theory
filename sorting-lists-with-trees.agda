-- developed with Agda version 2.6.2.1

variable A B : Set

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data Tree (A : Set) : Set where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

ItList : B → (A → B → B) → List A → B
ItList mnil mcons [] = mnil
ItList mnil mcons (x ∷ xs) = mcons x (ItList mnil mcons xs)

ItTree : B → (B → A → B → B) → Tree A → B
ItTree mleaf mnode leaf = mleaf
ItTree mleaf mnode (node l x r) =
         mnode (ItTree mleaf mnode l) x (ItTree mleaf mnode r)

record _×_ (A B : Set) : Set where
   constructor _,_
   field
      proj₁ : A
      proj₂ : B
open _×_

RTree-it : B → (A → Tree A → B → Tree A → B → B) → Tree A → B 
RTree-it {B} {A} mleaf mnode leaf = mleaf 
RTree-it {B} {A} mleaf mnode (node l x r) = proj₂ (ItTree mleaf' mnode' (node l x r))
   where
      mleaf' : Tree A × B 
      mleaf' = leaf , mleaf 
      mnode' : Tree A × B → A → Tree A × B → Tree A × B
      mnode' lm a rm = node l x r , mnode a (proj₁ lm) (proj₂ lm) (proj₁ rm) (proj₂ rm)

data Bool : Set where
  false : Bool
  true : Bool

_≤_ : ℕ → ℕ → Bool
zero ≤ m = true
suc n ≤ zero = false
suc n ≤ suc m = n ≤ m

insert : ℕ → Tree ℕ → Tree ℕ 
insert x leaf = node leaf x leaf
insert x (node l n r) with x ≤ n 
... | true = node (insert x l) n r
... | false = node l n (insert x r)

insert-rtree-it : ℕ → Tree ℕ → Tree ℕ 
insert-rtree-it n tree = RTree-it (node leaf n leaf) (λ x l result-l r result-r → 
   if (n ≤ x) then (node result-l x r) else (node l x result-r)) tree
      where
         if_then_else_ : Bool → A → A → A
         if true then x else y = x
         if false then x else y = y

_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

collapse : Tree A → List A
collapse leaf = []
collapse (node l a r) = collapse l ++ (a ∷ collapse r)

collapse-it : Tree A → List A 
collapse-it = ItTree [] (λ l a r → l ++ ((a ∷ []) ++ r))

grow-aux : Tree ℕ → List ℕ → Tree ℕ 
grow-aux tree [] = tree
grow-aux tree (x ∷ list) = grow-aux (insert x tree) list

grow : List ℕ → Tree ℕ
grow = grow-aux leaf

grow-aux-it : Tree ℕ → List ℕ → Tree ℕ 
grow-aux-it tree = ItList tree (λ x xs → insert-rtree-it x xs)

grow-it : List ℕ → Tree ℕ 
grow-it = grow-aux-it leaf

sort : List ℕ → List ℕ
sort l = collapse (grow l)