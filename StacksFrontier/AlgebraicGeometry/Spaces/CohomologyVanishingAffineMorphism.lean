module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# First cohomology of a space affine over one with vanishing first cohomology

Let `X` be a quasi-compact, quasi-separated algebraic space all of whose quasi-coherent modules
have vanishing first cohomology, that is the data of Stacks 07UY, and let `f : X' ⟶ X` be an
affine morphism of algebraic spaces.  Clause (1) of Stacks 07V0 asserts that then
`H¹(X', 𝓕') = 0` for every quasi-coherent `𝒪_{X'}`-module `𝓕'`.

## Main results

All names are in the namespace `AlgebraicGeometry.Space.CohomologyVanishingSituation`.

* `isZero_rightDerived_one_globalSectionsFunctor`: in Situation 07UY, `H¹(X, 𝓕) = 0` for every
  quasi-coherent `𝓕` whose sections lie in the universe of the structure sheaf.
* `isZero_rightDerived_one_globalSectionsFunctor_of_isAffineHom`: **clause (1) of Stacks 07V0.**

## Implementation notes

*Which cohomology.*  The cohomology of `𝒪_{X'}`-modules is the right derived functor of
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}` on the small étale ringed
site, for modules whose sections lie in the universe `u` of the structure rings.  That is the
universe at which the direct image of modules exists, and the one at which Stacks 0D2U,
`AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom`, compares `H^i(X', 𝓕')` with
`H^i(X, f_*𝓕')`.

*The universe of the situation.*  The vanishing hypothesis of
`AlgebraicGeometry.Space.CohomologyVanishingSituation.{u, u}` is imposed on modules with sections
in `Type (u + 1)`, the smallest universe at which the first cohomology of the small étale site of
the source's definition can be formed; the results here are about modules with sections in
`Type u`.  As for Stacks 07V1, 07V4 and 07V5, the situation is the one at `m := u`.

*Quasi-compactness and quasi-separatedness* of the space of the situation are not used.

## References

* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V1](https://stacks.math.columbia.edu/tag/07V1)
* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 07V5](https://stacks.math.columbia.edu/tag/07V5)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, u})

/-- **In Situation 07UY the first cohomology of a quasi-coherent module vanishes at the module
universe of the structure sheaf.**  For a quasi-coherent `𝒪_X`-module `𝓕` whose sections lie in
the universe of the schemes, `H¹(X, 𝓕) = 0`. -/
theorem isZero_rightDerived_one_globalSectionsFunctor
    (F : Modules.{u, u} T.site T.base T.containsBase T.space.1 T.space.2)
    (hF : F.IsQuasicoherentOnSite) :
    have := enoughInjectives_modules T.site T.base T.containsBase T.space.1 T.space.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite T.site T.base T.containsBase T.space.1 T.space.2).O)).rightDerived
        1).obj F) := by
  have := enoughInjectives_modules T.site T.base T.containsBase T.space.1 T.space.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf T.site T.base
    T.containsBase T.space.1 T.space.2
  let Γ := globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite T.site T.base T.containsBase T.space.1 T.space.2).O)
  let Q : ShortComplex (Modules.{u, u} T.site T.base T.containsBase T.space.1 T.space.2) :=
    ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hQ : Q.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
      mono_f := inferInstanceAs (Mono (Injective.ι F))
      epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι F))) }
  have hker : (SheafOfModules.Submodule.ker Q.g).toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((SheafOfModules.Submodule.kerIsoKernel Q.g).trans
        (hQ.exact.fIsKernel.conePointUniqueUpToIso (kernelIsKernel Q.g)).symm).symm hF
  have hepi : Epi (Γ.map Q.g) :=
    (ModuleCat.epi_iff_surjective _).2 (T.surjective_sectionsMap_of_epi Q.g hQ.epi_g hker)
  have hepi0 : Epi ((Γ.rightDerived 0).map Q.g) := by
    rw [← NatIso.naturality_2 Γ.rightDerivedZeroIsoSelf Q.g]
    infer_instance
  have : Injective Q.X₂ := inferInstanceAs (Injective (Injective.under F))
  exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁_of_epi hQ Γ 0 hepi0
    (Γ.isZero_rightDerived_obj_injective_succ 0 Q.X₂)

/-- **Clause (1) of Stacks 07V0.** In the situation of Stacks 07UY, let `f : X' ⟶ X` be an affine
morphism of algebraic spaces and let `𝓕'` be a quasi-coherent `𝒪_{X'}`-module.  Then
`H¹(X', 𝓕') = 0`. -/
@[stacks 07V0 "part (1); cohomology of modules at the universe of the structure sheaf"]
theorem isZero_rightDerived_one_globalSectionsFunctor_of_isAffineHom
    {X' : AlgebraicSpaces T.site T.base T.containsBase} (f : X' ⟶ T.space)
    (hf : IsAffineHom T.site T.base T.containsBase f.hom)
    (F : Modules.{u, u} T.site T.base T.containsBase X'.1 X'.2)
    (hF : F.IsQuasicoherentOnSite) :
    have := enoughInjectives_modules T.site T.base T.containsBase X'.1 X'.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite T.site T.base T.containsBase X'.1 X'.2).O)).rightDerived 1).obj F) := by
  have := enoughInjectives_modules T.site T.base T.containsBase X'.1 X'.2
  have := hasInjectiveResolutions_modules T.site T.base T.containsBase X'.1 X'.2
  have := hasInjectiveResolutions_modules T.site T.base T.containsBase T.space.1 T.space.2
  have hpush : ((modulePushforward T.site T.base T.containsBase f).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional _ _ _ f hf _ hF
  exact _root_.isZero_of_faithful (forget₂ _ AddCommGrpCat.{u + 1})
    ((Functor.map_isZero (forget₂ _ AddCommGrpCat.{u + 1})
      (T.isZero_rightDerived_one_globalSectionsFunctor _ hpush)).of_iso
        (cohomologyIsoOfIsAffineHom T.site T.base T.containsBase f hf F hF 1))

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end

end
