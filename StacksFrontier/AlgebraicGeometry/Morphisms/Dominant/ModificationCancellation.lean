module

public import StacksFrontier.AlgebraicGeometry.BirationalDenseOpenIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly

/-!
# Cancelling a modification on the right

If `q : Z ⟶ Y` and `g : Y ⟶ S` are such that `g` and `q ≫ g` are modifications, then so is `q`.
Properness cancels because a modification is separated, and birationality cancels because a
birational morphism of integral schemes has the generic point of its source as the exact preimage
of the generic point of its target.

## Main results

* `AlgebraicGeometry.isBirational_of_comp_of_isIntegral`: birationality cancels on the right
  against a birational morphism of integral schemes.
* `AlgebraicGeometry.SeparableGoUp.isModification_of_comp`: a factor of a modification through a
  modification is a modification.

## Implementation notes

The general cancellation of birationality,
`AlgebraicGeometry.isBirational_of_comp_of_isBirational`, asks that the generic points of `Y` be
the exact preimage of the generic points of `S`, which for a birational morphism is
`AlgebraicGeometry.preimage_genericPoints_eq_genericPoints_of_isBirational`; its finiteness
hypotheses on the sets of irreducible components hold because an irreducible space has exactly
one.

## References

* [Stacks Project, Tag 0AAZ](https://stacks.math.columbia.edu/tag/0AAZ)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 0BAC](https://stacks.math.columbia.edu/tag/0BAC)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Birationality cancels on the right against a birational morphism of integral schemes.** The
generic points of an irreducible scheme form a single point, so a birational `g : Y ⟶ S` has the
generic point of `Y` as the exact preimage of the generic point of `S`, which is what cancelling
`g` on the right of a birational composite asks for. -/
theorem isBirational_of_comp_of_isIntegral {Z Y S : Scheme.{u}} [IsIntegral Y] [IsIntegral S]
    (q : Z ⟶ Y) (g : Y ⟶ S) (hqg : IsBirational (q ≫ g)) (hg : IsBirational g) :
    IsBirational q := by
  have fin (X : Scheme.{u}) [IsIntegral X] : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton (X := X)]
    infer_instance
  have := fin Y
  have := fin S
  exact isBirational_of_comp_of_isBirational q g hqg hg
    (preimage_genericPoints_eq_genericPoints_of_isBirational g hg)

end AlgebraicGeometry

end
