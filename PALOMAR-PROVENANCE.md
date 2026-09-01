# About the Palomar statement

[`comparator.json`](comparator.json) selects one result for Palomar: Conway's refinement
conjecture for omnific integers. This repository contains the proof itself; it is not a wrapper
around another formalization.

## The statement

If $a,b,c,d\in\mathbf{Oz}$ and $ab=cd$, the theorem gives $e,f,g,h\in\mathbf{Oz}$ such
that

$$
a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh.
$$

Here $\mathbf{Oz}$ is the ring of omnific integers. The statement has no nonzero assumptions:
zero and other degenerate cases are included.

[`Challenge.lean`](Challenge.lean) states this from first principles. It defines well-founded
Conway games, their arithmetic and order, numeric games, and omnific integers. An omnific integer
is recognized by Conway's cut equation $x=\{x-1\mid x+1\}$. Equality is written as
`Game.Equivalent`, which becomes equality in the quotient of numeric games.

The Challenge works in an arbitrary Lean universe. At any one universe level, its games have
set-sized families of options. It does not try to put the proper class of all surreal numbers
into one Lean type.

## Why I believe this is Conway's conjecture

Conway gives the four equations above in *On Numbers and Games* (1976), p. 46. On p. 45, he
attributes the cut description $x=\{x-1\mid x+1\}$ to Norton. These are the formula and the
definition used by the Challenge.

L'Innocente and Mantova state the same four-factor refinement property as Conjecture 1.1.1(2)
in *A factorisation theory for generalised power series and omnific integers* (2024). Their
earlier paper *Factorisation of germ-like series* (2017) states the corresponding refinement
conjecture for $K((\mathbb R^{\le 0}))$.

The Lean statement uses numeric-game representatives instead of defining a quotient type inside
the Challenge. The rest of this repository proves that the cut description used here agrees
with the usual generalised-power-series description of omnific integers. I do not know of any
other difference between the Lean statement and Conway's conjecture.

No surreal-number specialist has independently checked this comparison.

## Earlier work

The papers listed in [`formalization.yaml`](formalization.yaml) give the factorisation background
for this proof. The 2017 and 2024 papers above still state refinement as a conjecture.

On 1 September 2026, I searched the web and arXiv for Conway's refinement conjecture, its
four-factor formula, the refinement and pre-Schreier properties of omnific integers, and earlier
formalizations. I also followed the references through the papers listed in the metadata. I did
not find an earlier proof or formalization.

## How the proof was made and checked

I chose the problem, directed the work, decided what to keep, and am responsible for this
repository. ChatGPT and Claude supplied all of the mathematical and Lean work.

The Challenge imports only `Mathlib.Order.GameAdd` and contains one intentional `sorry` for the
theorem being submitted. [`Solution.lean`](Solution.lean) supplies the proof of the same
statement. CI checks that the Challenge remains an exact copy of the standalone statement, apart
from its local proof-file note, plus the Palomar wrapper. Comparator checks that Challenge and
Solution have the same type and that the Solution uses only `propext`, `Classical.choice`, and
`Quot.sound`.

Lean checks the proof terms. There has been no independent specialist review or peer review.

The repository is licensed under Apache-2.0.
