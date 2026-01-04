A formalization of the [Banach-Tarski Theorem](https://en.wikipedia.org/wiki/Banach%E2%80%93Tarski_paradox)

The main result is
```
theorem banach_tarski_paradox_B3 : Paradoxical G3 B3 
```
where
```
abbrev G3 := R3 ≃ᵢ R3 -- The Group of Isometries on Euclidean Space ℝ³ 
def B3 : Set R3 := Metric.closedBall (0 : R3) 1 -- The solid 3-dimensional ball of radius one centered at the origin of ℝ³.
```
and where "Paradoxical" is a predicate saying that we can take B3 
apart into finitely many pieces and rearrange those pieces 
using only members of G3 to obtain two copies of B3.

A classic text on this and other so-called "paradoxical decompositions" is:

Tomkowicz, Grzegorz, and Stan Wagon. *The Banach-Tarski Paradox*. Cambridge University Press, 2016.
