module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedPrimeOverSpecialization
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkDepthGeneralization
public import StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthInequalitiesDepthOne

/-!
# Positive depth from a specialization at distance one

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `ℱ` be a coherent `𝒪_U`-module whose completion
along `I𝒪_U` satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3]. Suppose
`x ⤳ y` in `U` with `y` lying on `Y` at distance exactly one from `Z`, and suppose the
codimension of `y` inside `\overline{\{x\}}` is at most `d`. Then `depth(ℱ_x) ≥ 1`.

## Main results

* `Stacks.Algebraization.one_le_depth_stalk_of_specializes_of_distanceToZ_eq_one` — the depth
  bound above.

## Implementation notes

The hypothesis `¬ I ≤ 𝔭_x` is what makes `I𝒪_{U,y}^∧` miss the prime over `𝔭_x`; it is not
implied by the others.

## References

* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3)
* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5)
* [Stacks Project, Tag 0EJ8](https://stacks.math.columbia.edu/tag/0EJ8)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- **Positive depth from a specialization at distance one.** Let `ℱ` be a coherent
`𝒪_U`-module whose completion satisfies the strict `(1, 1 + d)`-inequalities of
[Stacks, Tag 0EJ3], let `A` be universally catenary, and let `x ⤳ y` be a specialization in `U`
with `y` lying over a point `r` of `Y` at distance exactly `1` from `Z`. If `I` is not contained
in the prime of `x` and the image of the prime of `y` in `A/𝔭_x` has height at most `d`, then

  `depth(ℱ_x) ≥ 1`. -/
public theorem one_le_depth_stalk_of_specializes_of_distanceToZ_eq_one
    (S : AlgebraizationSituation.{u})
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 0 ≤ d)
    (hcat : Ring.IsUniversallyCatenary S.A)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (x y : S.U.toScheme) (hxy : x ⤳ y) (r : S.Y) (hyr : S.U.ι.base y = S.Yι.base r)
    (hdist : S.distanceToZ r = 1)
    (hInotp : ¬ S.I ≤ (S.U.ι.base x).asIdeal)
    (hheight : ((S.U.ι.base y).asIdeal.map
      (Ideal.Quotient.mk (S.U.ι.base x).asIdeal)).height ≤ (d.toNat : ℕ∞)) :
    1 ≤ Module.depth (S.U.toScheme.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk x))
      ((stalkModuleFunctor x).obj F.obj) := by
  let _ : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  let _ : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
    (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
  obtain ⟨P, hover, hmin, hJnot, hdimP⟩ :=
    exists_primeSpectrum_completedLocalRing_of_specializes S x y hxy r hyr hcat hInotp d hd
      hheight
  let _ := hover
  exact one_le_depth_stalk_of_one_le_completedStalkDepth (idealOnOpen S) F hxy P hmin
    (one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) d hstrict y r hyr hdist P hJnot
      hdimP)

end Stacks.Algebraization

end
