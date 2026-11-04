module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilySectionsLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIdealModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SectionsLiftFibre

/-!
# Zariski and étale first cohomology on a represented space

For a quasi-coherent module `M` on a scheme `V` of the site, the vanishing of its Zariski `H¹`
gives the vanishing of the étale `H¹` of the associated module `Φ M` on the represented algebraic
space `h_V`.

## Main definitions

* `AlgebraicGeometry.C1590Private.RepresentedFirstCohomologyVanishing`: the statement that the
  vanishing of the Zariski `H¹` of a quasi-coherent `M` gives the vanishing of the étale `H¹` of
  `Φ M` on `h_V`.

## Main results

* `AlgebraicGeometry.C1590Private.representedFirstCohomologyVanishing`: that statement holds.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.C1590Private

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] Space.hasInjectiveResolutions_modules

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The statement that, for a quasi-coherent module `M` on a scheme `V` of the site, the vanishing
of its Zariski `H¹` gives the vanishing of the étale `H¹` of the associated module `Φ M` on the
represented algebraic space `h_V`. -/
def RepresentedFirstCohomologyVanishing : Prop :=
  ∀ (V : BigFppfOver B S hS) (M : ((BigFppfOver.toScheme B S hS).obj V).Modules),
    SheafOfModules.IsQuasicoherent M →
    IsZero (Hgroup ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf ⊤ 1 M) →
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS
        (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived 1).obj
      ((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).obj M))

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- For a quasi-coherent module `M` on a scheme `V` of the site, the vanishing of its Zariski `H¹`
gives the vanishing of the étale `H¹` of the associated module `Φ M` on `h_V`. -/
theorem representedFirstCohomologyVanishing : RepresentedFirstCohomologyVanishing B S hS := by
  intro W M hMq hM
  let K := (Space.representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)).obj M
  have hK : K.IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_representedAssociatedModule B S hS W _ M hMq
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS
    (schemeSpace W).1 (schemeSpace W).2).O
  let A := Space.idEtaleChart B S hS W
  let X : (Space.SmallEtale B S hS (schemeSpace W).1)ᵒᵖ := op A
  have hX : IsInitial X := (Space.isTerminalIdEtaleChart B S hS W).op
  obtain ⟨e⟩ := Space.nonempty_chartZariskiPushforward_idEtaleChart_iso B S hS W M hMq
  have hZar0 := (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf ⊤ 1 M).2 hM
  have hZar := (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    (Space.chartScheme A).ringCatSheaf ⊤ 1 _).1 (hZar0.of_iso (Functor.mapIso _ e))
  have : (SheafOfModules.evaluation O X).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have h0 : IsZero (((SheafOfModules.evaluation O X).rightDerived 1).obj K) :=
    Space.isZero_rightDerived_evaluation_of_isZero_hgroup B S hS (schemeSpace W) A K hK 1
      (by omega) hZar
  let e' := globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O X hX
  have h1 : IsZero ((forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}).obj
      (((globalSectionsFunctor.{u + 1, u, u, u} O).rightDerived 1).obj K)) :=
    IsZero.of_iso (Functor.map_isZero (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) h0)
      (((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u} O)
          (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}) 1).app K).symm
              ≪≫
        (ModuleSheafCohomology.rightDerivedIso e' 1).app K ≪≫
          (Functor.rightDerivedCompIso (SheafOfModules.evaluation O X)
            (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}) 1).app K)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 h1

end AlgebraicGeometry.C1590Private

end
