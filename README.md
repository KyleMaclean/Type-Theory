The code in this repository was developed with Agda version 2.6.2.1 (https://agda.readthedocs.io/en/v2.6.2.1/).

Explanation of each file:

## classical-logical-operators.agda

Functions between variables which are closed under double negation are defined. Since they satisfy _reductio ad absurdo_, they can be used in proofs of classical logic.

## iterator-and-recursor.agda

Structural recursion with pattern matching is used to define some functions on ℕ. These definitions are then abstracted into applications of the Iterator and Recursor for ℕ.

## lambda-and-combinators.agda

Simple functions are defined using λ-abstraction and then a definition using only the S and K combinators is derived. Each step of the derivation is provided.

## library-of-propositional-logic.agda

Imported into `classical-logical-operators.agda` and `proofs-in-*.agda` to provide primitive logical functions and the ability to assume classical principles.

## matrix-operations.agda

A two-dimensional matrix is constructed from a type which represents vectors through being dependent on ℕ as the length of the vector. The standard operations of addition, multiplication and transposition are implemented.

## proofs-in-*-logic.agda

For each proposition, a proof is provided to show the case into which it falls. It can be one of the following:
- _intuitionistically_ true,
- classically true using either _reductio ad absurdo_ or _tertium non datur_,
- false for some set of impossible variable instantiations.

### * = predicate

All the propositions are in the first-order.

### * = propositional

All the propositions are in the zeroth-order.

## sorting-lists-with-trees.agda

The `treesort` algorithm is implemented on the `List` type. The intermediary functions which manipulate the `Tree` type are defined using structural recursion with pattern matching and then only using the Iterator for `List` and `Tree`.