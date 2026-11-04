module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomComposition

/-!
# The square of global function rings of a flat base change

For the cartesian square of **Stacks 073J**,

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

the four ring maps on global regular functions of **Stacks 0732** form a square, and this file
records that it commutes.

That is the statement **Stacks 073K**, part (2) needs in order to be formed.  The part compares
`H^i(X, ℱ) ⊗_A B` with `H^i(X', ℱ')` for `A = Γ(Y, 𝒪_Y)` and `B = Γ(Y', 𝒪_{Y'})`, so the right
hand side has to be read as an `A`-module through `B`; the map available is
`AlgebraicGeometry.Space.cohomologyPullbackMap` for `g'`, which is linear over `Γ(X, 𝒪_X)` and
so reads it as an `A`-module through `Γ(X, 𝒪_X)`.  The two readings agree exactly because the
square below commutes.

## Main results

* `AlgebraicGeometry.Space.BaseChangeDiagram.globalSectionsRingHomSite_sq`: **the two ways round
  the square induce the same ring map** `Γ(Y, 𝒪_Y) ⟶ Γ(X', 𝒪_{X'})`.

## Implementation notes

This is a corollary of `AlgebraicGeometry.Space.globalSectionsRingHomSite_sq` and uses only
commutativity of the square, not that it is cartesian.

It is stated in a module of its own rather than in
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean`, where the square lives,
because importing the composition law there changes that file's instance environment:
`SheafOfModules.instAbelian` is then found with its module universe left open and the derived
functors of the base change map stop elaborating.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

namespace BaseChangeDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : BaseChangeDiagram B S hS)

/-- **The two ways round the square of Stacks 073J induce the same ring map on global regular
functions**: `Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'}) ⟶ Γ(X', 𝒪_{X'})` is
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})`.

Only commutativity of the square is used.  This is what makes the two sides of **Stacks
073K**, part (2) modules over one ring; see the module docstring. -/
theorem globalSectionsRingHomSite_sq :
    (globalSectionsRingHomSite B S hS D.g').comp (globalSectionsRingHomSite B S hS D.f) =
      (globalSectionsRingHomSite B S hS D.f').comp (globalSectionsRingHomSite B S hS D.g) :=
  AlgebraicGeometry.Space.globalSectionsRingHomSite_sq B S hS D.g' D.f D.f' D.g D.isPullback.w

end BaseChangeDiagram

end AlgebraicGeometry.Space

end
