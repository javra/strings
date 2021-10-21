# String Diagrams for Ring-and-Rope Puzzles

This repository contains a formalisation of string diagrams used to
solve ring-and rope puzzles.

Tested with Agda 2.6.0.1 (might be fragile due to the use of rewrite pragmas)

## Structure

* `StrictNat.agda` a version of the natural numbers strictified by some additional rewrite rules.
* `Diags.agda` contains the definition of the diagrams.
* `Arity.agda` contains short cuts for operations with greater arity.
* `Identities.agda` other identities derived from the diagram laws.
* `Sliding.agda` contains sliding laws.
* `Bracket.agda` formalises brackets over `n` strings.
* `BraidingNaturality.agda` proves the naturality of the braiding.
* `InverseBraiding.agda` constructs the inverse of the (lax) braiding.

## Examples

* `RingOnString.agda` formalises the solution of freeing a ring from a loop of string.
* `2x2Block.agda` formalises the puzzle (but not yet the solution) of a more complex puzzle.
