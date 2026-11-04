module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorAxiomAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorLogClass

/-!
# Axiom (A4) for Hodge cohomology

Remark 0FWE of the Stacks project asserts that Hodge cohomology `X ↦ H^*_{Hodge}(X/k)` with
`c₁^{Hodge}` is a Weil cohomology theory; one of the axioms to check is (A4) of Section 0FID: for
`i : Y ⟶ X` the inclusion of an effective Cartier divisor `D`, with `X` and `Y` smooth projective
over `k`, and `a ∈ H^*_{Hodge}(X/k)` with `i^* a = 0`, one has `a ∪ c₁^{Hodge}(𝒪_X(D)) = 0`.

This is the Hodge analogue of Tag 0FMX. The proof:

* `c₁^{Hodge}(𝒪_X(D))` maps to zero in `H^1(X, Ω^1_{X/k}(log D))`
  (`Stacks.HodgeWeil.cohomologyMap_logPolesFormsBaseInclusion_hodgeFirstChernClassModule_eq_zero`):
  on a cover by charts with local equations `t_j`, its Čech cocycle `d log(t_j / t_i)` is the
  coboundary of the forms `d log t_j` with logarithmic poles;
* a class `a` restricting to zero on `D` lifts to the forms `𝒦^p` vanishing on `D`, and the wedge
  product `𝒦^p ⊗ Ω^1 ⟶ Ω^{p+1}` extends to `𝒦^p ⊗ Ω^1(log D) ⟶ Ω^{p+1}`, so `a ∪ c` only depends
  on the image of `c` in `H^1(X, Ω^1(log D))`
  (`Stacks.HodgeWeil.mul_hodgeClass_eq_zero_of_pull_eq_zero`).

## Main results

* `Stacks.HodgeWeil.hodge_divisorAxiom`: **axiom (A4) for Hodge cohomology**.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FMX](https://stacks.math.columbia.edu/tag/0FMX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.HodgeWeil

variable (k : Type u) [Field k]

/-- **Axiom (A4) for Hodge cohomology** (Remark 0FWE, Section 0FID): for `X`, `Y` smooth
projective over `k`, `i : Y ⟶ X` the inclusion of an effective Cartier divisor `D` and
`a ∈ H^*_{Hodge}(X/k)` with `i^* a = 0`, `a ∪ c₁^{Hodge}(𝒪_X(D)) = 0`. -/
theorem hodge_divisorAxiom : (hodgeFirstChernClassData k).DivisorAxiom := by
  intro X Y i D hD e he a ha
  apply (tateTwistCoordinates (V := hodgeAlgebraOf X) (LinearEquiv.refl k k) 1).injective
  refine (tateTwistCoordinates_tateCupLeft (LinearEquiv.refl k k)
    ((hodgeFirstChernClassData k).cup X) 1 a _).trans ?_
  refine Eq.trans ?_
    (tateTwistCoordinates (V := hodgeAlgebraOf X) (LinearEquiv.refl k k) 1).map_zero.symm
  show (show hodgeAlgebraOf X from a) *
    (tateTwistCoordinates (V := hodgeAlgebraOf X) (LinearEquiv.refl k k) 1)
    ((tateTwistCoordinates (V := hodgeAlgebraOf X) (LinearEquiv.refl k k) 1).symm
      ((DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 2)
        (hodgeFirstChernClassPiece X _))) = 0
  rw [LinearEquiv.apply_symm_apply]
  exact mul_hodgeClass_eq_zero_of_pull_eq_zero i D hD e he _
    (cohomologyMap_logPolesFormsBaseInclusion_hodgeFirstChernClassModule_eq_zero X.obj.hom D hD)
    a ha

end Stacks.HodgeWeil

end
