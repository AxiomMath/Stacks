module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhEtaleHigherDirectImageReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional

/-!
# Torsion étale sheaves are acyclic for the ph-to-étale comparison of algebraic spaces

Let `X` be an algebraic space, `ε_X : (Spaces/X)_ph ⟶ (Spaces/X)_étale` the comparison of the big
ph and big étale topoi, and `a_X = π_X ∘ ε_X` the comparison with the small étale topos (Stacks
0DGW). For a torsion abelian sheaf `ℱ` on `X_étale` the higher direct images `R^i ε_{X,*}(a_X⁻¹ℱ)`
vanish for `i > 0` (Stacks 0DGT, part (2)).

The proof is the source's. By
`AlgebraicGeometry.BigPHSpaceSite.isZero_rightDerived_phToBigEtale_abelianInverseImage_of_schemes`
the statement reduces to the case of schemes, which is the second half of Stacks 0DE4, part (1)
(`AlgebraicGeometry.phComparison_smallEtaleInclusion`). That rests on the proper base change
theorem in degree zero for sheaves of sets (Stacks 0A3U,
`AlgebraicGeometry.isIso_smallEtaleSetBaseChange_of_isProper_forall`) and on the proper base change
theorem for torsion sheaves (Stacks 095T,
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`).

Part (1) of Stacks 0DGT is
`AlgebraicGeometry.BigPHSpaceSite.isIso_phToBigEtale_unit_app_inverseImage` and
`AlgebraicGeometry.BigPHSpaceSite.isIso_phToSmallEtale_unit_app`.

## Main results

* `AlgebraicGeometry.phEtaleHigherDirectImageVanishingOnSchemes` — the scheme case: Stacks 0DE4,
  part (1), second half, unconditionally.
* `AlgebraicGeometry.BigPHSpaceSite.isZero_rightDerived_phToBigEtale_abelianInverseImage` — Stacks
  0DGT, part (2).

## References

* [Stacks Project, Tag 0DE4](https://stacks.math.columbia.edu/tag/0DE4)
* [Stacks Project, Tag 0DGT](https://stacks.math.columbia.edu/tag/0DGT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The higher direct images of the ph-to-étale comparison vanish on torsion sheaves, for the
schemes of a big ph site** (Stacks 0DE4, part (1), second half). For a scheme `X` of a big ph site
`B` and a torsion abelian sheaf `F` on `X_étale`, `R^i ε_{X,*}(a_X⁻¹F) = 0` for `i ≥ 1`. This is
`AlgebraicGeometry.phComparison_smallEtaleInclusion` with its two inputs, Stacks 0A3U and Stacks
095T, supplied by their proofs. -/
public theorem phEtaleHigherDirectImageVanishingOnSchemes (B : BigPHSite.{u}) :
    PhEtaleHigherDirectImageVanishingOnSchemes B :=
  fun X F hF i hi =>
    (phComparison_smallEtaleInclusion B isIso_smallEtaleSetBaseChange_of_isProper_forall
      (@fun _ _ f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f)
      X F hF).2 i hi

namespace BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite)

/-- **Stacks 0DGT, part (2).** Let `X` be an algebraic space and `ℱ` a torsion abelian sheaf on
`X_étale`. Then `R^i ε_{X,*}(a_X⁻¹ℱ) = 0` for `i > 0`. Here
`ε_X : (Spaces/X)_ph ⟶ (Spaces/X)_étale` is the comparison of Stacks 0DGW, `ε_{X,*}` is
restriction of abelian sheaves along the identity-on-spaces functor of slices, `a_X⁻¹` is the
abelian inverse image (Stacks 04JC) of `a_X = π_X ∘ ε_X`, and `R^i` is the right derived
functor. -/
@[stacks 0DGT "part (2)"]
public theorem isZero_rightDerived_phToBigEtale_abelianInverseImage (X : P.Spaces)
    (ℱ : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1})
    (hℱ : Stacks.Torsion.torsionSheafProperty
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X)) ℱ)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((phToBigEtaleAbelianPushforward P E h X).rightDerived i).obj
      ((phToSmallEtaleAbelianInverseImage P E h X).obj ℱ)) :=
  isZero_rightDerived_phToBigEtale_abelianInverseImage_of_schemes P E h X
    (phEtaleHigherDirectImageVanishingOnSchemes P.schemeSite) ℱ hℱ i hi

end BigPHSpaceSite

end AlgebraicGeometry

end
