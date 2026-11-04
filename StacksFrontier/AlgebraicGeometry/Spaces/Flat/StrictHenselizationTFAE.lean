module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationConditionsTwo
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationQuasiFinite

/-!
# Stacks 0CVB

In Situation 0CV6 let `ȳ` be a geometric point of `Y` lying over `y`, and let
`Y^{sh} = Spec 𝒪_{Y, ȳ}`, `X^{sh} = X ×_Y Y^{sh}` and `ℱ^{sh}` the pullback of `ℱ` to `X^{sh}`.
The four conditions of the source are equivalent:

1. there is an impurity `(Y^{sh} ⟶ Y, y' ⤳ ȳ, ξ)` of `ℱ` above `y`,
2. some point of `Ass_{X^{sh}/Y^{sh}}(ℱ^{sh})` does not specialize to a point of the closed fibre
   `X_ȳ` (the corrected reading of the source's (2), see
   `StacksFrontier/AlgebraicGeometry/Spaces/Flat/StrictHenselizationConditions.lean`),
3. there is an impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `ℱ` above `y` with `(T, t) ⟶ (Y, y)` an étale
   neighbourhood,
4. there is an impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `ℱ` above `y` with `T ⟶ Y` quasi-finite at `t`.

## Main results

* `AlgebraicGeometry.Space.tfae_hasImpurityOverStrictHenselization`: **Stacks 0CVB.**

## References

* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0CVB.** In Situation 0CV6, for a geometric point `ȳ` of `Y` lying over `y`, the four
conditions of the source are equivalent: an impurity of `ℱ` above `y` over `Y^{sh}` with
specialized point `ȳ`; a point of `Ass_{X^{sh}/Y^{sh}}(ℱ^{sh})` not specializing into the closed
fibre; an impurity over an étale neighbourhood of `y`; an impurity whose structure morphism is
quasi-finite at its specialized point. -/
@[stacks 0CVB "condition (2) in the corrected reading recorded in the note of \
StrictHenselizationConditions: some associated point does not specialize into the closed fibre"]
theorem tfae_hasImpurityOverStrictHenselization (P : PrePureSituation.{u, u} B S hS)
    (ybar : GeometricPoint B S hS P.Y) (hybar : ybar.LiesOver P.y) :
    [HasImpurityOverStrictHenselization P ybar,
      HasRelativeAssociatedPointAvoidingClosedFibre P ybar,
      HasImpurityOverEtaleNeighborhood P,
      HasImpurityQuasiFiniteAtPoint P].TFAE := by
  tfae_have 1 ↔ 2 :=
    hasImpurityOverStrictHenselization_iff_hasRelativeAssociatedPointAvoidingClosedFibre P ybar
      hybar
  tfae_have 1 → 3 := hasImpurityOverEtaleNeighborhood_of_hasImpurityOverStrictHenselization P ybar
  tfae_have 3 → 4 := hasImpurityQuasiFiniteAtPoint_of_hasImpurityOverEtaleNeighborhood P
  tfae_have 4 → 1 := hasImpurityOverStrictHenselization_of_hasImpurityQuasiFiniteAtPoint P ybar
    hybar
  tfae_finish

end AlgebraicGeometry.Space

end
