module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts

/-!
# Cohomology of the module associated with a quasi-coherent module on a scheme

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let `𝓕` be a
quasi-coherent `𝒪_T`-module.  Through Descent, Proposition 03DX, `𝓕` is a quasi-coherent module
`𝓕ᵃ` on the small étale site of the algebraic space `yoneda.obj U`
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`).  This file records that
the cohomology of `𝓕ᵃ` over the identity chart of `yoneda.obj U` vanishes in every positive
degree in which the Zariski cohomology of `𝓕` on `T` vanishes, and that `𝓕ᵃ` is coherent when
`𝓕` is of finite type and `T` is locally Noetherian.

## Main results

* `AlgebraicGeometry.Space.nonempty_chartZariskiPushforward_idEtaleChart_iso`: the restriction of
  `𝓕ᵃ` to the Zariski site of `T` along the identity chart is `𝓕`.
* `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_idEtaleChart_of_isZero_hgroup`:
  `H^q(T, 𝓕) = 0` implies `H^q(yoneda.obj U, 𝓕ᵃ) = 0` over the identity chart.
* `AlgebraicGeometry.Space.isCoherent_representedQuasicoherentSchemeEquivalence`: `𝓕ᵃ` is
  coherent.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 5000] SheafOfModules.instAbelian

/-- The `𝒪`-modules on the small étale site of an algebraic space, at the universe of the
structure rings, have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_represented
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-- The comparison functor of the identity chart of a representable algebraic space is
continuous: this is `AlgebraicGeometry.Space.isContinuous_chartComparisonFunctor`, restated at
the spelling of the identity chart, which instance search does not reach. -/
local instance isContinuous_chartComparisonFunctor_idEtaleChart (U : BigFppfOver B S hS) :
    (chartComparisonFunctor B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) (idEtaleChart B S hS U)).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  isContinuous_chartComparisonFunctor B S hS
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
    (idEtaleChart B S hS U)

/-- **The restriction of an associated module to the Zariski site of the scheme along the
identity chart is the module one started with.**  The restriction along the identity chart is
the restriction along the inclusion of the small Zariski site
(`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`), and that inclusion's restriction
is a one-sided inverse of the associated-module functor on quasi-coherent modules, by
Stacks 03DX. -/
theorem nonempty_chartZariskiPushforward_idEtaleChart_iso (U : BigFppfOver B S hS)
    (F : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hF : SheafOfModules.IsQuasicoherent F) :
    Nonempty ((SheafOfModules.pushforward.{u}
        (chartComparisonRingMap B S hS
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
          (idEtaleChart B S hS U))).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).obj ≅ F) := by
  have hunit := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟨F, hF⟩
  exact ⟨(restrictToChartSchemeIsoChartComparisonPushforward B S hS
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
      (idEtaleChart B S hS U) _).symm ≪≫
    restrictToChartSchemeIdEtaleChartIso B S hS U _ ≪≫
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS U).unitIso.app _).symm ≪≫
    (@asIso _ _ _ _ _ hunit).symm⟩

/-- **The cohomology of an associated module over the identity chart vanishes with the Zariski
cohomology of the module.**  If `H^q(T, 𝓕) = 0` for some `q > 0` then the `q`-th right derived
functor of sections over the identity chart of `yoneda.obj U` vanishes at `𝓕ᵃ`.  This is
`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isZero_hgroup` at the identity chart,
through `AlgebraicGeometry.Space.nonempty_chartZariskiPushforward_idEtaleChart_iso`. -/
theorem isZero_rightDerived_evaluation_idEtaleChart_of_isZero_hgroup (U : BigFppfOver B S hS)
    (F : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hF : SheafOfModules.IsQuasicoherent F)
    (q : ℕ) (hq : 0 < q)
    (h : IsZero (Hgroup ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⊤ q F)) :
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) (op (idEtaleChart B S hS U))).rightDerived q).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).obj) := by
  obtain ⟨e⟩ := nonempty_chartZariskiPushforward_idEtaleChart_iso B S hS U F hF
  exact isZero_rightDerived_evaluation_of_isZero_hgroup B S hS
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
    (idEtaleChart B S hS U) _
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).property q hq
    (h.of_iso ((Hfunctor ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⊤ q).mapIso e))

/-- **The cohomology over a chart of an associated module vanishes with the Zariski cohomology
of the pulled-back module.**  Let `A` be an étale chart of `yoneda.obj U`, with scheme `T_A`, and
let `g : A ⟶ id` be its morphism to the identity chart.  If `H^q(T_A, g^*𝓕) = 0` for some
`q > 0`, then the cohomology over the identity chart of the chart space of `A` of the restriction
of `𝓕ᵃ` vanishes in degree `q`.

The Zariski reading of that restriction is the chart restriction of `𝓕ᵃ` at `A`
(`AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback_idEtaleChart`), which is the
pullback along `g` of its chart restriction at the identity chart
(`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_chartBaseChange`), that is of `𝓕`. -/
theorem isZero_rightDerived_evaluation_etaleModulePullback_of_isZero_hgroup
    (U : BigFppfOver B S hS) (F : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hF : SheafOfModules.IsQuasicoherent F)
    (A : SmallEtale B S hS (yoneda.obj U)) (q : ℕ) (hq : 0 < q)
    (h : IsZero (Hgroup (chartScheme A).ringCatSheaf ⊤ q
      ((Scheme.Modules.pullback (chartSchemeMap ((isTerminalIdEtaleChart B S hS U).from A))).obj
        F))) :
    IsZero (((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartSpace B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) A).1
        (chartSpace B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) A).2).O))
      (op (idEtaleChart B S hS (chartFppfObject B S hS
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
          A)))).rightDerived
        q).obj
      ((etaleModulePullback B S hS
        (chartToSpace B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) A)
        (isEtale_chartToSpace B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) A)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).obj)) := by
  have hN : (((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
      ⟨F, hF⟩).obj).IsQuasicoherentOnSite :=
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).property
  have hN' := isQuasicoherentOnSite_etaleModulePullback_chartToSpace B S hS
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) _ hN A
  obtain ⟨e₁⟩ := nonempty_chartZariskiPushforward_idEtaleChart_iso B S hS U F hF
  obtain ⟨e₂⟩ := nonempty_restrictToChartScheme_chartBaseChange B S hS
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) _ hN
    ((isTerminalIdEtaleChart B S hS U).from A)
  have i₁ := (restrictToChartSchemeIsoChartComparisonPushforward B S hS
    (chartSpace B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) A)
    (idEtaleChart B S hS (chartFppfObject B S hS
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) A))
    ((etaleModulePullback B S hS
        (chartToSpace B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) A)
        (isEtale_chartToSpace B S hS (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) A)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).obj)).symm
  have i₂ := restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).obj A
  have i₃ := (restrictToChartSchemeIsoChartComparisonPushforward B S hS
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)
    (idEtaleChart B S hS U)
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).obj) ≪≫ e₁
  refine isZero_rightDerived_evaluation_of_isZero_hgroup B S hS _ _ _ hN' q hq
    (h.of_iso ((Hfunctor (chartScheme A).ringCatSheaf ⊤ q).mapIso
      (i₁ ≪≫ eqToIso i₂ ≪≫ e₂.symm ≪≫
        (Scheme.Modules.pullback (chartSchemeMap ((isTerminalIdEtaleChart B S hS U).from A))).mapIso
          i₃)))

/-- **An associated module of finite type is coherent** on the algebraic space represented by a
locally Noetherian scheme: it is quasi-coherent, of finite type by Stacks 03DM
(`AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence`), and on a
locally Noetherian algebraic space those two make it coherent, by Stacks 07UB. -/
theorem isCoherent_representedQuasicoherentSchemeEquivalence (U : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (F : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hF : SheafOfModules.IsQuasicoherent F)
    (hft : SheafOfModules.IsFiniteType F) :
    IsCoherent B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).obj := by
  have : Fact (HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_of_representable B S hS _ _ U (Iso.refl _) inferInstance⟩
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) _).2
    ⟨((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨F, hF⟩).property,
      Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _
        (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS U F hF hft)⟩

/-! ### Vanishing at a terminal affine chart -/

/-- **A quasi-coherent module with no sections over a terminal affine chart is zero.**  Let `W` be
a terminal étale chart of `X` whose scheme is affine and let `𝓜` be quasi-coherent with `𝓜(W) = 0`.
Over every affine chart `V` the sections are `𝒪(V) ⊗ 𝓜(W)`, by Descent, Proposition 03DX (2)
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`), hence zero; the
affine charts cover every chart, and a sheaf is separated. -/
theorem isZero_of_isQuasicoherentOnSite_of_subsingleton_terminal (X : AlgebraicSpaces B S hS)
    {W : SmallEtale B S hS X.1} (hW : IsTerminal W) (hWa : IsAffineChart B S hS X.1 W)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (h : Subsingleton (M.val.obj (op W))) : IsZero M := by
  have haff : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      Subsingleton (M.val.obj (op V)) := fun V hV => by
    have hb := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM W V hWa hV
      (hW.from V)
    let := chartAlgebra (hF := X.2) (hW.from V)
    let := chartSectionsModule M (hW.from V)
    exact (Equiv.ofBijective _ hb).symm.subsingleton
  refine isZero_of_subsingleton_val_obj B S hS X M (fun V => ⟨fun x y => ?_⟩)
  suffices hz : ∀ z : M.val.obj V, z = 0 by rw [hz x, hz y]
  intro z
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero z
    (generate_isAffineChart_mem_topology B S hS X V.unop) (fun Y g hg => ?_)
  obtain ⟨Y', a, b, hb', rfl⟩ := hg
  have := haff Y' hb'
  have h1 : M.val.presheaf.map b.op z = 0 := @Subsingleton.elim _ this _ _
  have h2 : M.val.presheaf.map (a ≫ b).op z =
      M.val.presheaf.map a.op (M.val.presheaf.map b.op z) :=
    ConcreteCategory.congr_hom (M.val.presheaf.map_comp b.op a.op) z
  show M.val.presheaf.map (a ≫ b).op z = 0
  rw [h2, h1, map_zero]

end AlgebraicGeometry.Space

end
