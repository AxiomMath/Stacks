module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor

/-!
# The points of a sum of closed subspaces

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`D₁, D₂ ⊆ X` be closed subspaces.  The sum `D₁ + D₂` of Stacks 083U is cut out by the product
`𝓘_{D₁} 𝓘_{D₂}` of the two defining ideals, and the vanishing locus of a product of ideals is
the union of the two vanishing loci.  So the point set of the sum is the union of the point sets
of the summands, `|D₁ + D₂| = |D₁| ∪ |D₂|`, as is seen on a scheme chart of `X`, where the point
set of a closed subspace is the support of the chart ideal sheaf.

## Main results

* `AlgebraicGeometry.Space.image_preimage_subspacePointSet_eq_supportSet_chartKer`: on a scheme
  chart of `X` the point set of a closed subspace is the support of the chart ideal sheaf.

## References

* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The point set of a closed subspace, read on a scheme chart.**  The inverse image along a
scheme chart `g : h_U ⟶ X` of the point set of a closed subspace `Z ⊆ X` corresponds, under the
identification of the point space of `h_U` with the space of the scheme `U`, to the support of
the chart ideal sheaf `AlgebraicGeometry.Space.chartKer` of `Z` on `U`. -/
theorem image_preimage_subspacePointSet_eq_supportSet_chartKer
    (Z : ClosedSubspaces B S hS X.1) {U : BigFppfOver B S hS} (g : yoneda.obj U ⟶ X.1) :
    pointsToScheme B S hS U ''
        (pointsMap B S hS (yoneda.obj U) g ⁻¹' subspacePointSet B S hS X.1 Z.1) =
      (chartKer B S hS X Z g).supportSet := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd g)) := Z.2.2.property_snd g
  rw [preimage_range_pointsMap_eq_range_pointsMap_snd B S hS Z.2.2.rep g]
  have hfun : pointsToScheme B S hS U ∘
      pointsMap B S hS (yoneda.obj (Z.2.2.rep.pullback g))
        (yoneda.map (Z.2.2.rep.snd g)) =
      ⇑((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd g)) ∘
        pointsToScheme B S hS (Z.2.2.rep.pullback g) :=
    funext fun w => pointsToScheme_pointsMap_yoneda B S hS (Z.2.2.rep.snd g) w
  have hclosed : IsClosed
      (Set.range ⇑((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd g))) :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mp hci).2
  have hrange : Set.range ⇑((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd g)) =
      (chartKer B S hS X Z g).supportSet := by
    have h := Scheme.Hom.support_ker ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd g))
    rw [hclosed.closure_eq] at h
    exact h.symm
  rw [← Set.image_univ, ← Set.image_comp, hfun, Set.image_comp, Set.image_univ,
    (surjective_pointsToScheme B S hS (Z.2.2.rep.pullback g)).range_eq, Set.image_univ, hrange]

end AlgebraicGeometry.Space

end
