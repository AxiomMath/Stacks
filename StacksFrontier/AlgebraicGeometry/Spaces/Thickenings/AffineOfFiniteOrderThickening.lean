module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfLiftedEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderChartLift

/-!
# A finite-order thickening of an affine algebraic space is affine

Let `G ⊆ X` be a finite-order thickening of algebraic spaces over a scheme `S`. If the closed
member `G` is affine then so is `X`. This is the case of Stacks 05ZR (a thickening of a scheme is
a scheme) for which the source gives a direct proof, specialised to an affine closed member, with
nothing granted.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isFiniteOrderThickening`.

## Implementation notes

The proof is the source's: the global functions of `G` lift to `X`, and a thickening of an affine
space whose functions lift is affine. The two halves are separate files.

* The lift is `AlgebraicGeometry.Space.exists_lift_invariant_of_isFiniteOrderThickening`, read on
  an affine surjective étale chart of `X`
  (`AlgebraicGeometry.Space.exists_affine_surjective_etale_chart_of_isThickening`). It replaces
  the vanishing of `H¹` of the quasi-coherent ideal of the source (Stacks 05ZQ) by a Čech argument
  on the chart, and it is where the finite order is used.
* The affineness from lifted functions is
  `AlgebraicGeometry.Space.isAffineSpace_of_forall_exists_lift`. It replaces the source's
  comparison morphism `X → Spec Γ(X, 𝒪_X)` of Stacks 05Z1, which needs a terminal base here, by a
  lifted étale presentation and topological invariance of the étale site (Stacks 05ZH).

No `@[stacks]` attribute is attached: the statement is the affine finite-order case of Stacks
05ZR, not the tag, and the general case is assembled elsewhere.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A finite-order thickening of an affine algebraic space is affine.** If `G ⊆ X` is a
finite-order thickening of algebraic spaces over `S` and `G` is affine, then `X` is affine. -/
theorem isAffineSpace_of_isFiniteOrderThickening {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    (hG : IsFiniteOrderThickening B S hS X G) (hGaff : IsAffineSpace B S hS G.toFunctor) :
    IsAffineSpace B S hS X.1 := by
  obtain ⟨TG, hTG, ⟨eG⟩⟩ := hGaff
  have hGt : IsThickening B S hS X G := hG.choose_spec.1
  obtain ⟨V, φ, hV, hφs, hφe⟩ :=
    exists_affine_surjective_etale_chart_of_isThickening B S hS hGt ⟨TG, hTG, ⟨eG⟩⟩
  obtain ⟨U, j, p, hpb, -⟩ := exists_thickening_chart_pullback_subfunctor B S hS hGt V φ
  obtain ⟨πU, hπU⟩ := yoneda.map_surjective (p ≫ eG.hom)
  have sqU : IsPullback (yoneda.map j) (yoneda.map πU ≫ eG.inv) φ G.ι := by
    rw [hπU, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hpb.flip
  exact isAffineSpace_of_forall_exists_lift B S hS X G hGt hTG eG hV φ hφs hφe j πU sqU
    (exists_lift_invariant_of_isFiniteOrderThickening B S hS X G hG hTG eG hV φ hφs hφe j πU
      sqU)

end AlgebraicGeometry.Space

end
