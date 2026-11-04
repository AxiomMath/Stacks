module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormulaAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethFormulaSmooth
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham Künneth formula over an affine base

Let `S = Spec(A)` be affine and let `a : X ⟶ S`, `b : Y ⟶ S` be smooth and quasi-compact with
affine diagonal over `S`. [Stacks, Tag 0FMB] asserts that the de Rham Künneth map

`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`

is an isomorphism in `D(A)`.

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_deRhamGlobalKunnethMap_canonical`: **[Stacks, Tag 0FMB]**.

## Implementation notes

*The map.* It is `Stacks.Cohomology.BoxKunneth.deRhamGlobalKunnethMap` at the canonical global
cup product `Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical` of
[Stacks, Section 0FKU], the cup product from which the map of [Stacks, Tag 0FLR] is built.

*The proof.* The source derives the statement from [Stacks, Tag 0FLT] and [Stacks, Tag 0FMA].
Here it goes through the relative statement [Stacks, Tag 0FMC], which holds at the same
hypotheses, `isIso_deRhamRelativeKunnethMap_of_smooth`. `RΓ(S, -)` of the relative map is the
global map, read through the Leray isomorphisms. The global cup product on the affine base is
invertible at `(Ra_*Ω^•_{X/S}, Rb_*Ω^•_{Y/S})`, by [Stacks, Tag 06Z0] and [Stacks, Tag 0FLX].
Both steps are `isIso_deRhamGlobalKunnethMap_canonical_of_isIso_relative`.

*The hypotheses.* "Quasi-compact with affine diagonal over `S`" is `QuasiCompact a` with
`IsAffineHom (pullback.diagonal a)`. Over an affine `S` these are equivalent to `X` being
quasi-compact with affine absolute diagonal (`AlgebraicGeometry.isAffineHom_diagonal_of_isAffine`).

## References

* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Tag 0FMC](https://stacks.math.columbia.edu/tag/0FMC)
* [Stacks Project, Tag 0FLT](https://stacks.math.columbia.edu/tag/0FLT)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.BoxKunneth

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **[Stacks, Tag 0FMB].** Let `S = Spec(A)` be affine and let `a : X ⟶ S` and `b : Y ⟶ S` be
smooth and quasi-compact with affine diagonal over `S`. Then the de Rham Künneth map

`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`

is an isomorphism in `D(A)`. The map is `deRhamGlobalKunnethMap` at the canonical global cup
product of [Stacks, Section 0FKU]. Nothing is assumed: the relative isomorphism of
[Stacks, Tag 0FMC] holds at these hypotheses, and over the affine base it gives the global one. -/
@[stacks 0FMB "the isomorphism at the source's hypotheses (S affine; X, Y smooth and quasi-compact
  with affine diagonal over S), for the map built from the canonical global cup product of
  Section 0FKU; nothing is assumed"]
theorem isIso_deRhamGlobalKunnethMap_canonical [IsAffine S]
    [AlgebraicGeometry.Smooth a] [AlgebraicGeometry.Smooth b] [QuasiCompact a] [QuasiCompact b]
    [IsAffineHom (pullback.diagonal a)] [IsAffineHom (pullback.diagonal b)] :
    IsIso (deRhamGlobalKunnethMap a b (globalCupProductCanonical S.toRingedSpace)) :=
  isIso_deRhamGlobalKunnethMap_canonical_of_isIso_relative a b
    (isIso_deRhamRelativeKunnethMap_of_smooth a b)

end Stacks.Cohomology.BoxKunneth
