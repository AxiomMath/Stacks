module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedQuasiCompactPoints

/-!
# The point space of a quasi-compact formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`. The reduction of an affine formal
algebraic space over `S` is, by **Stacks 0AIN**, the universe-lifted Yoneda presheaf of an
object of the site with compact underlying scheme, and the inclusion of a reduction is
bijective on points. So the point space of an affine formal algebraic space is the image of a
compact space.

A quasi-compact formal algebraic space over `S` — condition (3) of **Stacks 0AJ9** — receives a
surjection of sheaves from an affine formal algebraic space, and a surjection of sheaves is
surjective on points. Composing, a quasi-compact formal algebraic space receives from a
represented presheaf with compact underlying scheme a morphism which is surjective on points.
That is the form in which quasi-compactness is used downstream: it survives base change along
an arbitrary morphism, whereas the affine formal atlas of condition (3) does not obviously do
so.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_compact_pointsSurjection_of_isAffineFormalAlgebraicSpace`:
  an affine formal algebraic space over `S` receives a morphism surjective on points from a
  represented presheaf with compact underlying scheme.
* `AlgebraicGeometry.FormalSpace.exists_compact_pointsSurjection_of_isQuasiCompactSpace`: the
  same for a quasi-compact formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.compactSpace_pointsULift_of_isQuasiCompactSpace`: the point
  space of a quasi-compact formal algebraic space over `S` is compact.

## Implementation notes

The compact source is supplied by
`AlgebraicGeometry.FormalSpace.exists_isReduction_uliftYoneda_of_isAffineFormalAlgebraicSpace`,
which records the reduction of an affine formal algebraic space as an object of the site with
compact underlying scheme; surjectivity on points of the inclusion of that reduction is
`AlgebraicGeometry.FormalSpace.IsReduction.bijective_pointsMapULift`. Nothing about the
directed presentation, the relative thickening property of its stages, or the comparison of
the sheafified and universe-lifted Yoneda embeddings is needed here: all of that is already
discharged inside those two results.

Surjectivity on points of the affine formal atlas is
`AlgebraicGeometry.FormalSpace.isSurjective_of_isLocallySurjective`; the étaleness and
representability of the atlas are not used.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] Space.pointTopologyULift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine formal algebraic space over `S` receives a morphism surjective on points from a
represented presheaf with compact underlying scheme.** Its reduction is, by Stacks 0AIN, the
universe-lifted Yoneda presheaf of an object of the site with compact underlying scheme, and
the inclusion of a reduction is bijective on points. -/
theorem exists_compact_pointsSurjection_of_isAffineFormalAlgebraicSpace
    (Z : FppfSheaf B S hS) (hZ : IsAffineFormalAlgebraicSpace B S hS Z) :
    ∃ (T : BigFppfOver B S hS) (a : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj T) ∧
      Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _ a) := by
  obtain ⟨T, Zred, i, hT, ⟨e⟩, hred⟩ :=
    exists_isReduction_uliftYoneda_of_isAffineFormalAlgebraicSpace B S hS Z hZ
  refine ⟨T, e.hom ≫ i.hom, hT, ?_⟩
  rw [Space.pointsMapULift_comp]
  exact hred.bijective_pointsMapULift.2.comp
    (Space.bijective_pointsMapULift_of_iso.{u + 1} B S hS e).2

/-- **A quasi-compact formal algebraic space over `S` receives a morphism surjective on points
from a represented presheaf with compact underlying scheme.** The affine formal algebraic space
surjecting onto it receives one, and a surjection of fppf sheaves is surjective on points. -/
theorem exists_compact_pointsSurjection_of_isQuasiCompactSpace
    (W : FppfSheaf B S hS) (hW : IsQuasiCompactSpace B S hS W) :
    ∃ (T : BigFppfOver B S hS) (a : (uliftYoneda.{u + 1}).obj T ⟶ W.obj),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj T) ∧
      Function.Surjective (Space.pointsMapULift.{u + 1} B S hS _ a) := by
  obtain ⟨-, Z, z, haffine, -, hzsurj⟩ := hW
  obtain ⟨T, a, hT, ha⟩ :=
    exists_compact_pointsSurjection_of_isAffineFormalAlgebraicSpace B S hS Z haffine
  refine ⟨T, a ≫ z.hom, hT, ?_⟩
  rw [Space.pointsMapULift_comp]
  exact Function.Surjective.comp (isSurjective_of_isLocallySurjective B S hS hzsurj) ha

/-- The point space of a quasi-compact formal algebraic space over `S` is compact: it is the
image of the compact point space of a represented presheaf under a continuous surjection. -/
theorem compactSpace_pointsULift_of_isQuasiCompactSpace
    (W : FppfSheaf B S hS) (hW : IsQuasiCompactSpace B S hS W) :
    CompactSpace (Space.pointsULift.{u + 1} B S hS W.obj) := by
  obtain ⟨T, a, hT, ha⟩ := exists_compact_pointsSurjection_of_isQuasiCompactSpace B S hS W hW
  exact @Function.Surjective.compactSpace _ _ _ _ _ (Space.continuous_pointsMapULift B S hS a)
    (Space.compactSpace_pointsULift_uliftYoneda.{u + 1} B S hS T hT) ha

end AlgebraicGeometry.FormalSpace

end
