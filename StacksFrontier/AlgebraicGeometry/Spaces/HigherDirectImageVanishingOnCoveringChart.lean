module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure

/-!
# Vanishing of a higher direct image from one covering chart

Let `p : X ⟶ Y` be a representable, quasi-compact and quasi-separated morphism of algebraic spaces
and let `U` be an affine étale chart of `Y` which covers the final object of the small étale site
of `Y`.  This file proves that `R^q p_* M = 0`, for a quasi-coherent `𝒪_X`-module `M`, as soon as
the cohomology `H^q(X ×_Y U, M)` of the base change over the single chart `U` vanishes.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_sections_of_coversTop`: a sheaf of modules on the
  small étale site of an algebraic space is zero once its sections vanish over every chart mapping
  to a chart which covers the final object.
* `AlgebraicGeometry.Space.isZero_of_isAffineSpace_of_isZero_globalSections`: a quasi-coherent
  module on an affine algebraic space with no global sections is zero.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_coveringChart`: if
  `H^q(X ×_Y U, M) = 0` for an affine chart `U` covering the final object, then `R^q p_* M = 0`.

## References

* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf of modules on the small étale site is zero if every section restricts to zero along
every arrow of some covering sieve. -/
private theorem isZero_of_forall_locally_restrict_eq_zero (Y : AlgebraicSpaces B S hS)
    (K : Modules.{u, u} B S hS Y.1 Y.2)
    (h : ∀ V : SmallEtale B S hS Y.1, ∃ T ∈ (SmallEtale.topology B S hS Y.1) V,
      ∀ ⦃W : SmallEtale B S hS Y.1⦄ (g : W ⟶ V), T g → ∀ x : K.val.obj (op V),
        K.val.map g.op x = 0) :
    IsZero K := by
  rw [SheafOfModules.isZero_iff_forall_isZero_obj]
  intro V
  rw [ModuleCat.isZero_iff_subsingleton]
  obtain ⟨T, hT, hT0⟩ := h V
  exact subsingleton_of_forall_eq 0 fun x ↦
    Stacks.SheafOfModules.eq_zero_of_locally_eq_zero x hT fun _ g hg ↦ hT0 g hg x

/-- A sheaf of modules `K` on the small étale site of `Y` is zero if its sections vanish over every
chart mapping to a chart `U` which covers the final object. -/
theorem isZero_of_isZero_sections_of_coversTop (Y : AlgebraicSpaces B S hS)
    (K : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS Y.1)
    (hU : (SmallEtale.topology B S hS Y.1).CoversTop (fun _ : Unit => U))
    (h : ∀ W : SmallEtale B S hS Y.1, Nonempty (W ⟶ U) → IsZero (K.val.obj (op W))) :
    IsZero K := by
  refine isZero_of_forall_locally_restrict_eq_zero B S hS Y K fun V ↦ ⟨_, hU V, fun {W} g hg x ↦ ?_⟩
  obtain ⟨_, hφ⟩ := hg
  exact (ModuleCat.subsingleton_of_isZero (h W hφ)).allEq _ _

/-- A quasi-coherent module on an affine algebraic space with no global sections is zero. -/
theorem isZero_of_isAffineSpace_of_isZero_globalSections (Y : AlgebraicSpaces B S hS)
    (hY : IsAffineSpace B S hS Y.1) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : M.IsQuasicoherentOnSite)
    (h : IsZero ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj M)) :
    IsZero M := by
  obtain ⟨V, ⟨hV⟩, hVaff⟩ := exists_isTerminal_isAffine_chart B S hS Y hY
  have hzV : IsZero (M.val.obj (op V)) := by
    have hz := h.of_iso ((globalSectionsIsoEvaluation
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) hV).app M).symm
    rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
    exact ⟨fun a b ↦ congrArg ULift.down (@Subsingleton.elim _ hz (ULift.up a) (ULift.up b))⟩
  have hcart := SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 M hM
  have hzaff : ∀ W : SmallEtale B S hS Y.1, IsAffineChart B S hS Y.1 W →
      IsZero (M.val.obj (op W)) := by
    intro W hW
    have hsurj := (hcart V W hVaff hW (hV.from W)).2
    have : Subsingleton (M.val.obj (op V)) := ModuleCat.subsingleton_of_isZero hzV
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    let := chartAlgebra (hF := Y.2) (hV.from W)
    have hsub : Subsingleton (TensorProduct (chartRing B S hS Y.1 Y.2 V)
        (chartRing B S hS Y.1 Y.2 W) (M.val.obj (op V))) := inferInstance
    rw [@Subsingleton.elim _ hsub x y]
  refine isZero_of_forall_locally_restrict_eq_zero B S hS Y M fun V' ↦
    ⟨_, generate_isAffineChart_mem_topology B S hS Y V', fun {W} g hg x ↦ ?_⟩
  obtain ⟨W', g', g'', hW', rfl⟩ := hg
  have h0 : M.val.map g''.op x = 0 :=
    (ModuleCat.subsingleton_of_isZero (hzaff W' hW')).allEq _ _
  exact (PresheafOfModules.map_comp_apply M.val g''.op g'.op x).trans
    ((congrArg (M.val.map g'.op) h0).trans (map_zero _))

/-- Let `p : X ⟶ Y` be a representable, quasi-compact and quasi-separated morphism of algebraic
spaces, `U` an affine étale chart of `Y` covering the final object of the small étale site, `M` a
quasi-coherent `𝒪_X`-module and `q` a degree. If the cohomology `H^q(X ×_Y U, M)` of the base
change over `U` vanishes, then `R^q p_* M = 0`. -/
theorem isZero_rightDerived_modulePushforward_of_coveringChart {X Y : AlgebraicSpaces B S hS}
    (p : X ⟶ Y) (hp : yoneda.relativelyRepresentable p.hom)
    (hpqc : IsQuasiCompact B S hS p.hom) (hpqs : IsQuasiSeparated B S hS p.hom)
    (U : SmallEtale B S hS Y.1) (hUaff : IsAffineChart B S hS Y.1 U)
    (hU : (SmallEtale.topology B S hS Y.1).CoversTop (fun _ : Unit => U))
    (M : Modules.{u, u} B S hS X.1 X.2) [hM : M.IsQuasicoherentOnSite] (q : ℕ)
    (h :
      have := hasInjectiveResolutions_modules B S hS
          (chartSpace B S hS X ((smallBaseChange B S hS p hp).obj U)).1
          (chartSpace B S hS X ((smallBaseChange B S hS p hp).obj U)).2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS
          (chartSpace B S hS X ((smallBaseChange B S hS p hp).obj U)).1
          (chartSpace B S hS X ((smallBaseChange B S hS p hp).obj U)).2).O)).rightDerived q).obj
        ((etaleModulePullback B S hS
          (chartToSpace B S hS X ((smallBaseChange B S hS p hp).obj U))
          (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS p hp).obj U))).obj M))) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS p).rightDerived q).obj M) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  set XU := chartSpace B S hS X ((smallBaseChange B S hS p hp).obj U)
  set YU := chartSpace B S hS Y U
  have := hasInjectiveResolutions_modules B S hS XU.1 XU.2
  have := enoughInjectives_modules B S hS YU.1 YU.2
  set pU := smallBaseChangeChartMap B S hS p hp U
  set MU := (etaleModulePullback B S hS
    (chartToSpace B S hS X ((smallBaseChange B S hS p hp).obj U))
    (isEtale_chartToSpace B S hS X ((smallBaseChange B S hS p hp).obj U))).obj M
  have hYU : IsAffineSpace B S hS YU.1 :=
    isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj U) hUaff
  have hqcK : ∀ j : ℕ,
      (((modulePushforward B S hS p).rightDerived j).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS p hpqc hpqs M
  have hqcKU : ∀ j : ℕ, ((etaleModulePullback B S hS (chartToSpace B S hS Y U)
      (isEtale_chartToSpace B S hS Y U)).obj
        (((modulePushforward B S hS p).rightDerived j).obj M)).IsQuasicoherentOnSite :=
    fun j ↦ isQuasicoherentOnSite_etaleModulePullback B S hS _ _ _ (hqcK j)
  have hcoh : AcyclicHigherDirectImages B S hS pU MU := by
    intro j n hn
    have e := (moduleHigherPushforwardChartBaseChangeIso B S hS p hp U j).app M
    exact IsZero.of_iso (isZero_rightDerived_globalSectionsFunctor_of_isAffine B S hS
      ((SmallEtale.toOver B S hS Y.1).obj U) hUaff _ (hqcKU j) n hn)
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS YU.1 YU.2).O)).rightDerived n).mapIso e)
  have hΓ : IsZero ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS YU.1 YU.2).O)).obj
        ((etaleModulePullback B S hS (chartToSpace B S hS Y U)
          (isEtale_chartToSpace B S hS Y U)).obj
          (((modulePushforward B S hS p).rightDerived q).obj M))) := by
    refine IsZero.of_iso ?_ (cohomologyChartIsoSectionsHigherDirectImage_of_representable B S hS
      p hp M U q (acyclicPushforwardOfInjective B S hS pU) hcoh).symm
    refine IsZero.of_iso ?_ ((derivedGlobalSectionsPushforwardIso B S hS pU q).app MU)
    exact (globalSectionsRestrictScalars B S hS pU).map_isZero h
  have hKU := isZero_of_isAffineSpace_of_isZero_globalSections B S hS YU hYU _ (hqcKU q) hΓ
  refine isZero_of_isZero_sections_of_coversTop B S hS Y _ U hU (fun W ⟨φ⟩ ↦ ?_)
  have e := (etaleModulePullbackComp B S hS (chartMap B S hS Y φ) (chartToSpace B S hS Y U)
    (isEtale_chartMap B S hS Y φ) (isEtale_chartToSpace B S hS Y U)
    (by rw [chartMap_comp_chartToSpace]; exact isEtale_chartToSpace B S hS Y W)).app
      (((modulePushforward B S hS p).rightDerived q).obj M)
  have hzW : IsZero ((etaleModulePullback B S hS (chartMap B S hS Y φ ≫ chartToSpace B S hS Y U)
      (by rw [chartMap_comp_chartToSpace]; exact isEtale_chartToSpace B S hS Y W)).obj
        (((modulePushforward B S hS p).rightDerived q).obj M)) := by
    have := etaleModulePullback_additive.{u, u} B S hS (chartMap B S hS Y φ)
      (isEtale_chartMap B S hS Y φ)
    exact IsZero.of_iso ((etaleModulePullback B S hS (chartMap B S hS Y φ)
      (isEtale_chartMap B S hS Y φ)).map_isZero hKU) e.symm
  have key : ∀ (g : chartSpace B S hS Y W ⟶ Y) (hg : IsEtale B S hS g.hom),
      g = chartToSpace B S hS Y W →
      IsZero ((etaleModulePullback B S hS g hg).obj
        (((modulePushforward B S hS p).rightDerived q).obj M)) →
      IsZero ((etaleModulePullback B S hS (chartToSpace B S hS Y W)
        (isEtale_chartToSpace B S hS Y W)).obj
          (((modulePushforward B S hS p).rightDerived q).obj M)) := by
    rintro g hg rfl hz
    exact hz
  exact (SheafOfModules.isZero_iff_forall_isZero_obj _ _).mp
    (key _ _ (chartMap_comp_chartToSpace B S hS Y φ) hzW)
    (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj W))

end AlgebraicGeometry.Space

end
