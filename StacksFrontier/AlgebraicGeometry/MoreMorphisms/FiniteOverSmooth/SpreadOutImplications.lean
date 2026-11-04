module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalMorphismIrreducibleOpen

/-!
# The 057K chain above Tag 055W

Tag 057J is proved in this directory from Tag 055W, and Tag 057K from Tag 057J. This file ties
the two together, so that the only input the chain still lacks is Tag 055W itself: once that is
available, Tag 057K is one application of
`AlgebraicGeometry.exists_finite_over_smooth_geometricallyIntegral_of_statement055W`.

## Main results

* `AlgebraicGeometry.statement057J_of_statement055W`: Tag 055W implies Tag 057J. This also
  records that the conditional Tag 057J proved here has exactly the binders of
  `AlgebraicGeometry.Statement057J`.
* `AlgebraicGeometry.exists_finite_over_smooth_geometricallyIntegral_of_statement055W`: Tag 057K,
  with Tag 055W as its only hypothesis.

## Implementation notes

Both results are applications; the mathematics is in
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_open_geometricallyIntegral_of_statement055W`
and in `AlgebraicGeometry.exists_finite_over_smooth_of_locallyOfFiniteType`. The point of stating
them is that they are type-checked, so the chain is known to compose.

## References

* [Stacks Project, Tag 057K](https://stacks.math.columbia.edu/tag/057K)
* [Stacks Project, Tag 057J](https://stacks.math.columbia.edu/tag/057J)
* [Stacks Project, Tag 055W](https://stacks.math.columbia.edu/tag/055W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 057J** follows from Tag 055W. -/
theorem statement057J_of_statement055W (h055W : Statement055W.{u}) : Statement057J.{u} :=
  fun h s T hfp hnormal ↦
    exists_elementaryEtaleNeighborhood_open_geometricallyIntegral_of_statement055W
      h055W h s T hfp hnormal

/-- **Stacks Project, Tag 057K**, conditional on Tag 055W alone. -/
theorem exists_finite_over_smooth_geometricallyIntegral_of_statement055W
    (h055W : Statement055W.{u}) {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    ∃ (n : ℕ) (_ : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = n)
      (U : EtaleNeighborhood X x) (V : EtaleNeighborhood S (f x))
      (Y : Scheme.{u}) (h : Y ⟶ V.scheme) (π : U.scheme ⟶ Y),
      U.IsElementary ∧ V.IsElementary ∧ (U.toBase ≫ f = π ≫ h ≫ V.toBase) ∧
        SmoothOfRelativeDimension n h ∧
        (∀ s' : V.scheme, GeometricallyIntegral (h.fiberToSpecResidueField s')) ∧
        IsFinite π ∧ (∀ z : U.scheme, π z = π U.point ↔ z = U.point) ∧
        (∃ heq : h (π U.point) = V.point,
          letI : Algebra (V.scheme.residueField V.point) (Y.residueField (π U.point)) :=
            ((V.scheme.residueFieldCongr heq).inv ≫ h.residueFieldMap (π U.point)).hom.toAlgebra
          PurelyTranscendental (V.scheme.residueField V.point)
            (Y.residueField (π U.point))) ∧
        (LocallyOfFinitePresentation f → FinitePresentation π) :=
  exists_finite_over_smooth_geometricallyIntegral_of_statement057J
    (statement057J_of_statement055W h055W) f x

end AlgebraicGeometry

end
