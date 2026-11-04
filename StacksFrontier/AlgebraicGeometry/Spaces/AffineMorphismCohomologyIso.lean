module

public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialForget

/-!
# Higher direct images and cohomology along an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and `𝓕` a quasi-coherent
`𝒪_X`-module.  This file proves, without carried hypotheses:

* `isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite`:
  Stacks 073H, `R^n f_* 𝓕 = 0` for `n > 0`;
* `AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isAffineHom`: the same vanishing
  for the chart base changes of `f`, through
  `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_iff_chartwise`;
* `AlgebraicGeometry.Space.acyclicPushforwardOfInjective`: the direct image of an injective
  module is acyclic for global sections (Stacks 072Z read through part (3) of Stacks 0731);
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isAffine`: a
  quasi-coherent module on an affine scheme has no higher cohomology on the small étale site;
* `AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom`: Stacks 0D2U,
  `H^i(X, 𝓕) ≅ H^i(Y, f_*𝓕)` as abelian groups.

`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom` and
`AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom` state the reductions with the two
inputs `h03DW` and `h072Z` carried; the declarations here discharge them.

## Implementation notes

The route to Stacks 073H reduces all the way to *affine* étale charts `W` of `Y`, over which
`W ×_Y X` is an affine étale chart of `X`: Stacks 072W, in the form
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`,
reduces the vanishing of `R^n f_* 𝓕` to that of `H^n(W ×_Y X, 𝓕)` for `W` in a family of affine
étale charts covering each chart of `Y` (a dense subsite, Stacks 04JS), and there the higher
cohomology of a quasi-coherent module vanishes,
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`.

## References

* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 073H -/

/-- **A higher direct image along a representable morphism vanishes exactly when it vanishes
chart by chart.**

If `f : X ⟶ Y` is a representable morphism of algebraic spaces over `S`, then `R^n f_* 𝓕 = 0`
exactly when the degree-`n` higher direct images of the chart base changes of `f` vanish.

A module on the small étale site of `Y` is zero exactly when its restriction to every étale
scheme chart is zero, and over the chart `V` that restriction is `R^n f'_*(𝓕|_{V ×_Y X})` by
Equation 69.3.0.1, `AlgebraicGeometry.Space.moduleHigherPushforwardChartBaseChangeIso`.  Because
the statement is about vanishing of objects, only the existence of that isomorphism is used,
not its identification with the canonical base-change map. -/
theorem isZero_rightDerived_modulePushforward_iff_chartwise {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.obj X.property
    IsZero (((modulePushforward B S hS f).rightDerived n).obj F) ↔
      ChartwiseIsZeroHigherDirectImage B S hS f hf F n := by
  have := hasInjectiveResolutions_modules B S hS X.obj X.property
  dsimp only
  rw [isZero_iff_forall_isZero_etaleModulePullback_chartToSpace]
  refine forall_congr' fun V => ?_
  have := hasInjectiveResolutions_modules B S hS
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
    (chartSpace B S hS X ((smallBaseChange B S hS f hf).obj V)).property
  exact (Iso.isZero_iff ((moduleHigherPushforwardChartBaseChangeIso B S hS f hf V n).app F)).symm

/-- The affine étale charts of an algebraic space mapping to an étale chart `V` generate a
covering sieve of `V`: the affine étale charts form a dense subsite (Stacks 04JS). -/
theorem generate_isAffineChart_mem_topology (Y : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Y.obj) :
    Sieve.generate (fun W (_ : W ⟶ V) => IsAffineChart B S hS Y.obj W) ∈
      SmallEtale.topology B S hS Y.obj V := by
  have : (AffineEtale.inclusion B S hS Y.obj).IsCoverDense (SmallEtale.topology B S hS Y.obj) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.obj Y.property).2.isCoverDense'
  refine (SmallEtale.topology B S hS Y.obj).superset_covering ?_
    ((AffineEtale.inclusion B S hS Y.obj).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS Y.obj) V)
  rintro W g ⟨h⟩
  exact ⟨_, h.lift, h.map, h.obj.property, h.fac⟩

/-- **Stacks 073H, unconditionally.** Let `f : X ⟶ Y` be an affine morphism of algebraic spaces
over `S` and `𝓕` a quasi-coherent `𝒪_X`-module.  Then `R^n f_* 𝓕 = 0` for every `n > 0`.

An affine morphism is representable, so the direct image of modules is restriction along base
change of étale scheme charts, `AlgebraicGeometry.Space.modulePushforwardChartIso`.  By
Stacks 072W in the form
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`, the
higher direct image then vanishes as soon as every étale chart of `Y` is covered by charts `W`
with `H^n(W ×_Y X, 𝓕) = 0`.  The affine charts `W` of `Y` cover, `W ×_Y X` is an affine chart of
`X` because `f` is affine (`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`), and the higher
cohomology of a quasi-coherent module on an affine étale chart vanishes
(`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`, the étale-site form
of Stacks 03DW on the affine scheme `W ×_Y X`). -/
theorem isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite {X Y :
    AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (hF : F.IsQuasicoherentOnSite)
    (n : ℕ) (hn : 0 < n) :
    have := hasInjectiveResolutions_modules B S hS X.obj X.property
    IsZero (((modulePushforward B S hS f).rightDerived n).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.obj X.property
  have hrep := relativelyRepresentable_of_isAffineHom B S hS f hf
  let G : Modules.{u, u} B S hS X.obj X.property ⥤ Modules.{u, u} B S hS Y.obj Y.property :=
    smallBaseChangeModulePushforward.{u, u} B S hS f hrep
  let e : modulePushforward B S hS f ≅ G := modulePushforwardChartIso B S hS f hrep
  have : G.Additive := Functor.additive_of_iso e
  have := isContinuous_smallBaseChange B S hS f hrep
  have : EnoughInjectives (SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.obj X.property)) :=
    enoughInjectives_modules B S hS X.obj X.property
  refine IsZero.of_iso ?_ ((ModuleSheafCohomology.rightDerivedIso e n).app F)
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (smallBaseChange B S hS f hrep) _ _ (smallBaseChangeSharp B S hS f hrep) n F
    (fun V => ⟨_, generate_isAffineChart_mem_topology B S hS Y V, fun W _ hW =>
      isZero_rightDerived_evaluation_of_isAffineChart B S hS X.obj X.property F hF _
        (isAffine_smallBaseChange_obj B S hS f hrep hf W hW) n hn⟩)

/-- **The chart base changes of an affine morphism have vanishing higher direct images** on the
restrictions of a quasi-coherent module: the forward implication of
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_iff_chartwise` applied to
Stacks 073H,
`isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite`. -/
theorem chartwiseIsZeroHigherDirectImage_of_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) (hrep : yoneda.relativelyRepresentable f.hom)
    (F : Modules.{u, u} B S hS X.obj X.property) (hF : F.IsQuasicoherentOnSite)
    (n : ℕ) (hn : 0 < n) :
    ChartwiseIsZeroHigherDirectImage B S hS f hrep F n :=
  (isZero_rightDerived_modulePushforward_iff_chartwise B S hS f hrep F n).1
    (isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite B S hS f hf F hF
        n hn)

/-! ### Quasi-coherent cohomology of an affine scheme -/

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **A quasi-coherent module on an affine scheme has no higher cohomology**, on the small étale
site of the algebraic space it represents: `H^n(T, M) = 0` for `n > 0`.

The identity chart of `T` is terminal in the small étale site, so global sections are sections
over it (`Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation`, on underlying
abelian groups); both forgetful functors are exact, so the right derived functors of global
sections are those of evaluation at the identity chart, which vanish on a quasi-coherent module
by `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart` (Stacks 03DW). -/
theorem isZero_rightDerived_globalSectionsFunctor_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (hM : M.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace T).1
        (schemeSpace T).2).O)).rightDerived n).obj M) := by
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace T).1
        (schemeSpace T).2).O
  let X : (SmallEtale B S hS (schemeSpace T).1)ᵒᵖ := Opposite.op (idEtaleChart B S hS T)
  have hX : IsInitial X := (isTerminalIdEtaleChart B S hS T).op
  let e := globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u} O X hX
  have : (SheafOfModules.evaluation O X).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have h0 : IsZero (((SheafOfModules.evaluation O X).rightDerived n).obj M) :=
    isZero_rightDerived_evaluation_of_isAffineChart B S hS _ _ M hM (idEtaleChart B S hS T) hT n
      hn
  have h1 : IsZero ((forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}).obj
      (((globalSectionsFunctor.{u + 1, u, u, u} O).rightDerived n).obj M)) :=
    IsZero.of_iso (Functor.map_isZero (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) h0)
      (((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u} O)
          (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}) n).app M).symm
              ≪≫
        (ModuleSheafCohomology.rightDerivedIso e n).app M ≪≫
          (Functor.rightDerivedCompIso (SheafOfModules.evaluation O X)
            (forget₂ (ModuleCat.{u} (O.obj.obj X)) AddCommGrpCat.{u} ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}) n).app M)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 h1

/-! ### Stacks 0D2U -/

section Cohomology

variable {X Y : AlgebraicSpaces B S hS}

/-- The direct image along any morphism of algebraic spaces of an injective `𝒪_X`-module is
acyclic for global sections on `Y`: this is
`AlgebraicGeometry.Space.acyclic_globalSectionsFunctor_modulePushforward_of_injective`, Stacks 072Z
read through part (3) of Stacks 0731. -/
theorem acyclicPushforwardOfInjective (f : X ⟶ Y) : AcyclicPushforwardOfInjective B S hS f :=
  fun Z _ => acyclic_globalSectionsFunctor_modulePushforward_of_injective B S hS f Z

/-- **Stacks 0D2U.**  Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and `𝓕`
a quasi-coherent `𝒪_X`-module.  Then `H^i(X, 𝓕) ≅ H^i(Y, f_*𝓕)` for every `i ≥ 0`, as abelian
groups.

Both sides are the right derived functors of global sections of modules, read in abelian groups.
Global sections of `f_*` are global sections on `X`
(`AlgebraicGeometry.Space.globalSectionsModulePushforwardIso`), forgetting to abelian groups is
exact, and the Leray collapse `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`,
whose two hypotheses are discharged by Stacks 073H and Stacks 072Z, identifies the derived
functors of `Γ(Y, f_* −)` with the cohomology of `f_*𝓕`. -/
def cohomologyIsoOfIsAffineHom (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
    (forget₂ _ AddCommGrpCat.{u + 1}).obj (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1
            X.2).O)).rightDerived i).obj F) ≅
      (forget₂ _ AddCommGrpCat.{u + 1}).obj (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1
            Y.2).O)).rightDerived i).obj
          ((modulePushforward B S hS f).obj F)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have := modulePushforward_additive B S hS f
  ((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (forget₂ _ AddCommGrpCat.{u + 1}) i).app F).symm ≪≫
    ((Functor.rightDerivedIsoOfNatIso (globalSectionsModulePushforwardIso B S hS f).symm i).app
      F) ≪≫
    (Functor.rightDerivedCompIso (modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u,
      u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      (forget₂ _ AddCommGrpCat.{u + 1}) i).app F ≪≫
    (forget₂ _ AddCommGrpCat.{u + 1}).mapIso (cohomologyCollapseIsoOfIsAffineHom B S hS f hf F
      (fun n hn => chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f hf _ F hF n hn)
      (acyclicPushforwardOfInjective B S hS f) i)

end Cohomology

end AlgebraicGeometry.Space

end

end
