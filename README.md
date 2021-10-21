# String Diagrams for Ring-and-Rope Puzzles

This repository contains a formalisation of string diagrams used to
solve ring-and rope puzzles.

## Structure

* `Diags.agda` contains the definition of the diagrams.
* `Arity.agda` contains short cuts for operations with greater arity.
* `Sliding.agda` contains sliding laws.
* `Bracket.agda` formalises brackets over `n` strings.
* `BraidingNaturality.agda` proves the naturality of the braiding.
* `InverseBraiding.agda` constructs the inverse of the (lax) braiding.

## Examples

* `RingOnString.agda` formalises the solution of freeing a ring from a loop of string.
* `2x2Block.agda` formalises the puzzle (but not yet the solution) of a more complex puzzle.
