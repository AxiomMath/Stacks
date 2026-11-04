module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpacePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedGeometricPointIndependence

/-!
# Weakly associated points and pullback along a finite flat morphism of algebraic spaces

Let `f : X ⟶ Y` be a finite flat morphism of algebraic spaces over a scheme `S`, let `G` be an
`𝒪_Y`-module and let `x ∈ |X|` be a point with image `y ∈ |Y|`. Then `x` is weakly associated
to `f^*G` exactly when `y` is weakly associated to `G`.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_modulePullback_iff_of_isFinite_of_isFlat`:
  **Stacks 0CUT**.

## Implementation notes

Weak association of a point of an algebraic space,
`AlgebraicGeometry.Space.IsWeaklyAssociatedPoint`, is weak association of the maximal ideal of
the étale local ring to the geometric stalk at some geometric point above the point, and it does
not depend on the geometric point chosen,
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPrime`. Choosing a
geometric point `x̄` above `x` (Stacks 0488 (1),
`AlgebraicGeometry.Space.exists_geometricRepresentative`), its image `ȳ` lies above `y`, and the
statement becomes the equivalence at the étale local rings
`AlgebraicGeometry.Space.isWeaklyAssociatedPrime_geometricModuleStalk_modulePullback_iff`,
which is the étale localization of the scheme case (Stacks 05FN) used by the source.

The source takes `G` quasi-coherent; the argument does not use this, so the statement is made
for every `𝒪_Y`-module.

## References

* [Stacks Project, Tag 0CUT](https://stacks.math.columbia.edu/tag/0CUT)
* [Stacks Project, Tag 05FN](https://stacks.math.columbia.edu/tag/05FN)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0CUT.** Let `f : X ⟶ Y` be a finite flat morphism of algebraic spaces over a
scheme `S`, let `G` be an `𝒪_Y`-module and let `x ∈ |X|` be a point with image `y ∈ |Y|`.
Then `x ∈ WeakAss(f^*G)` if and only if `y ∈ WeakAss(G)`.

The source takes `G` quasi-coherent; that hypothesis is not needed. -/
@[stacks 0CUT]
theorem isWeaklyAssociatedPoint_modulePullback_iff_of_isFinite_of_isFlat (f : X ⟶ Y)
    (hfinite : IsFinite B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X ((modulePullback B S hS f).obj G) x ↔
      IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom x) := by
  obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X.1 x
  exact (isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPrime B S hS X
      ((modulePullback B S hS f).obj G) xbar.image xbar rfl).trans
    ((isWeaklyAssociatedPrime_geometricModuleStalk_modulePullback_iff B S hS f hfinite hflat
      xbar G).symm.trans
    (isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPrime B S hS Y G
      (pointsMap B S hS X.1 f.hom xbar.image) (geometricPointMap f.hom xbar) rfl).symm)

end AlgebraicGeometry.Space

end
