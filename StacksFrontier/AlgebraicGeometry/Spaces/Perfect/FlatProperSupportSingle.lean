module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients

/-!
# A single coherent module, flat with proper support, as a complex

A coherent `𝒪_X`-module `𝒢`, flat over `Y` with support proper over `Y`, placed in degree zero is
a bounded complex of coherent modules flat over `Y` with support proper over `Y`, the
hypothesis on `𝒢^•` in Stacks 0DKJ and Stacks 0DKK.

## Main results

* `AlgebraicGeometry.Space.flatProperSupportComplex_single`: `𝒢[0]` satisfies the hypotheses of
  Stacks 0DKJ.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 0DKK](https://stacks.math.columbia.edu/tag/0DKK)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- A coherent module flat over `Y` with support proper over `Y`, placed in degree zero, is a
bounded complex of coherent modules flat over `Y` whose support lies in a closed subset proper over
`Y`: the hypothesis on `𝒢^•` in Stacks 0DKJ and Stacks 0DKK. -/
theorem flatProperSupportComplex_single (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hGc : IsCoherent B S hS X.1 X.2 G)
    (hflat : IsFlatOver B S hS X.2 f.hom G)
    (hcl : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G)))
    (hproper : IsProperOver B S hS X.2 Y.2 f.hom hf
      (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G)) hcl) :
    FlatProperSupportComplex B S hS f hf
      ((HomologicalComplex.single (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) 0).obj
        G) where
  bounded := ⟨0, 0, fun q hq => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  isCoherent q := by
    by_cases hq : q = 0
    · subst hq
      exact isCoherent_of_iso B S hS X.2 (HomologicalComplex.singleObjXSelf _ _ G).symm hGc
    · exact IsCoherent.of_isZero B S hS X.1 X.2
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)
  isFlatOver q := by
    by_cases hq : q = 0
    · subst hq
      exact IsFlatOver.of_iso B S hS X.2 (HomologicalComplex.singleObjXSelf _ _ G).symm hflat
    · exact isFlatOver_of_isZero B S hS f (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)
  properSupport := by
    refine ⟨_, hcl, hproper, fun q => ?_⟩
    by_cases hq : q = 0
    · subst hq
      exact (supportOfSheaf_eq_of_iso B S hS X (HomologicalComplex.singleObjXSelf _ _ G)).le
    · rw [(supportOfSheaf_eq_empty_iff_isZero B S hS X _).2
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)]
      exact Set.empty_subset _

end AlgebraicGeometry.Space

end
