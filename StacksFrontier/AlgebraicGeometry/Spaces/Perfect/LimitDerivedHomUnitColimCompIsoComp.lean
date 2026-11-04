module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCompIsoCross
public import StacksFrontier.CategoryTheory.Localization.LimitDerivedHomUnitColimCompIsoModelComp

/-!
# K-flat complexes compute the derived pullback on the spaces-étale models

The composition law of the crossing isomorphism
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso` — that the crossing isomorphism at
`f ≫ g` agrees with the one at `g` followed by the one at `f`, modulo the composition comparison of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` on one side and
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso` on the other — is
`Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp`, whose inputs are the factorisation of
each of the three isomorphisms through the comparisons of derived and underived pullback, together
with the statement that every object of the derived category of the model is, up to isomorphism, a
complex at which the comparison is invertible.  This file proves that last input.

The other inputs are the factorisation of the composition comparison on the models, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleModelHomCompCocycle.lean`, and
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_hom_app_comp` for the crossing
isomorphism itself.  The one that is still missing is the factorisation of the composition
comparison of the datum through the *transported* comparison
`AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison`: the composition
comparison of the datum is characterized (Stacks 0D6D,
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_eq`) through the comparison on the
small étale sites, and converting that into a statement about the transported comparison needs the
identification `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso` of the underived
pullbacks to be compatible with the two underived composition comparisons — the one of
`AlgebraicGeometry.Space.spacesEtaleModelPullbackComp` on the models and the one of
`AlgebraicGeometry.Space.pullbackModulesCompTransport` on the small étale sites.  That underived
compatibility is proved nowhere.

## Main results

* `AlgebraicGeometry.Space.exists_iso_Qh_isIso_derivedPullbackComparison_spacesEtaleModelHom`

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every object of the derived category of the model is, up to isomorphism, a complex that
computes the derived pullback.**  A K-flat complex with flat terms resolves it (Stacks 06YS) and
the comparison `Lf^* ⟶ f^*` is invertible there (Stacks 06YY). -/
theorem exists_iso_Qh_isIso_derivedPullbackComparison_spacesEtaleModelHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules) :
    ∃ (M : HomotopyCategory (spacesEtaleModelRingedTopos B S hS Y).Modules (ComplexShape.up ℤ))
      (_ : K ≅ DerivedCategory.Qh.obj M),
      IsIso ((derivedPullbackComparison (spacesEtaleModelHom B S hS f)).app M) := by
  obtain ⟨P, hP, s, hs⟩ := hasResolutions_isKFlat
    (Y := spacesEtaleModelRingedTopos B S hS Y) (DerivedCategory.Qh.objPreimage K)
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ hs
  refine ⟨P, (DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫
    (asIso (DerivedCategory.Qh.map s)).symm, ?_⟩
  open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi in
  exact isIso_derivedPullbackComparison_app_of_isKFlat (spacesEtaleModelHom B S hS f)
    (isMorphismOfSites_spacesEtaleModelHom B S hS f) P hP

end AlgebraicGeometry.Space

end
