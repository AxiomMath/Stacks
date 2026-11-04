module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementNonvanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSectionHomReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionAffinePart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison

/-!
# Readings on the presenting chart of the projective completion

Let `X` be an algebraic space and `ℰ` a finite locally free `𝒪_X`-module of rank `r`. A map of
quasi-coherent modules on a represented algebraic space is an isomorphism as soon as its reading
on the scheme is one. On the presenting chart `U` of `X`, the readings of the projection
`ℰ ⊕ 𝒪_X ⟶ ℰ`, of the inclusion `ℰ ⟶ ℰ ⊕ 𝒪_X` and of the summand `𝒪_X` form the split data of
`Stacks.RelativeProj.isIso_pullback_map_hyperplane_of_range_subset` (Stacks 01NS).

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_representedZariski_map`: a map of quasi-coherent modules
  on a represented algebraic space whose reading on the scheme is an isomorphism is one.
* `AlgebraicGeometry.Space.additive_schemeReadingFunctor`: the reading on a scheme is an additive
  functor.
* `AlgebraicGeometry.Space.completionChart_split`,
  `AlgebraicGeometry.Space.completionChartSection_comp_fst`: on the presenting chart, the readings
  of `ℰ ⊕ 𝒪_X ⟶ ℰ`, `ℰ ⟶ ℰ ⊕ 𝒪_X` and of the summand `𝒪_X` form the split data of
  `Stacks.RelativeProj.isIso_pullback_map_hyperplane_of_range_subset`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A map of quasi-coherent modules on a representable algebraic space whose reading on the
scheme is an isomorphism is an isomorphism.** -/
theorem isIso_of_isIso_representedZariski_map {T : BigFppfOver B S hS}
    {M N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N)
    (hf : IsIso ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map f))) :
    IsIso f := by
  let R := (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
    SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  have : IsIso (R.map f) := hf
  obtain ⟨g, hg⟩ := (QuasiCoherentDescent.bijective_representedZariski_map B S hS N M hN).2
    (inv (R.map f))
  have hg' : R.map g = inv (R.map f) := hg
  refine ⟨g, ?_, ?_⟩
  · refine (QuasiCoherentDescent.bijective_representedZariski_map B S hS M M hM).1 ?_
    change R.map (f ≫ g) = R.map (𝟙 M)
    refine (R.map_comp f g).trans ?_
    rw [hg', IsIso.hom_inv_id]
    exact (R.map_id M).symm
  · refine (QuasiCoherentDescent.bijective_representedZariski_map B S hS N N hN).1 ?_
    change R.map (g ≫ f) = R.map (𝟙 N)
    refine (R.map_comp g f).trans ?_
    rw [hg', IsIso.inv_hom_id]
    exact (R.map_id N).symm

variable {X : AlgebraicSpaces B S hS}

/-- The reading on the scheme of `T`, along `ψ : T ⟶ X`, as a functor. -/
abbrev schemeReadingFunctor {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ((BigFppfOver.toScheme B S hS).obj T).Modules :=
  modulePullback B S hS ψ ⋙ (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
    SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property

/-- The reading is an additive functor. -/
instance additive_schemeReadingFunctor {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) : (schemeReadingFunctor ψ).Additive where
  map_add {E E' a b} := by
    have : (modulePushforward B S hS ψ).IsRightAdjoint :=
      ⟨_, ⟨modulePullbackAdjunction B S hS ψ⟩⟩
    have : (modulePushforward B S hS ψ).Additive :=
      Functor.additive_of_preserves_binary_products _
    have h₁ : (modulePullback B S hS ψ).Additive :=
      Adjunction.left_adjoint_additive (modulePullbackAdjunction B S hS ψ)
    have h₂ : (representedSmallEtaleModuleEquivalence B S hS T).inverse.Additive :=
      (representedSmallEtaleModuleEquivalence B S hS T).inverse_additive
    have h₃ : (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).Additive :=
      SmallEtale.additive_restrictModule _ _ _
    have e₁ := Functor.Additive.map_add (self := h₁) (f := a) (g := b)
    have e₂ := Functor.Additive.map_add (self := h₂) (f := (modulePullback B S hS ψ).map a)
      (g := (modulePullback B S hS ψ).map b)
    have e₃ := Functor.Additive.map_add (self := h₃)
      (f := (representedSmallEtaleModuleEquivalence B S hS T).inverse.map
        ((modulePullback B S hS ψ).map a))
      (g := (representedSmallEtaleModuleEquivalence B S hS T).inverse.map
        ((modulePullback B S hS ψ).map b))
    exact ((congrArg (fun t => (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
          ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map t)) e₁).trans
      (congrArg (fun t => (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map t) e₂)).trans e₃

/-! ### The section on the chart of the affine part -/

/-- The reading on a chart is functorial. -/
private theorem chartModuleMap_comp_chartModuleMap {V : SmallEtale B S hS X.1}
    {E E' E'' : Modules.{u, u} B S hS X.1 X.2} (f : E ⟶ E') (g : E' ⟶ E'') :
    chartModuleMap f V ≫ chartModuleMap g V = chartModuleMap (f ≫ g) V :=
  (schemeReadingMap_comp _ _ _).symm

/-- The reading on a chart is additive. -/
private theorem chartModuleMap_add {V : SmallEtale B S hS X.1}
    {E E' : Modules.{u, u} B S hS X.1 X.2} (f g : E ⟶ E') :
    chartModuleMap f V + chartModuleMap g V = chartModuleMap (f + g) V :=
  (schemeReadingMap_add _ _ _).symm

/-- The reading on a chart carries zero to zero. -/
private theorem chartModuleMap_zero {V : SmallEtale B S hS X.1}
    {E E' : Modules.{u, u} B S hS X.1 X.2} : chartModuleMap (0 : E ⟶ E') V = 0 :=
  schemeReadingMap_zero _

/-- The reading on a chart carries the identity to the identity. -/
private theorem chartModuleMap_id {V : SmallEtale B S hS X.1}
    {E : Modules.{u, u} B S hS X.1 X.2} : chartModuleMap (𝟙 E) V = 𝟙 _ :=
  schemeReadingMap_id _

section Completion

variable (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)

/-- The identification of the reading of `𝒪_X` on the presenting chart with the structure sheaf
of its scheme. -/
abbrev completionChartUnitIso :
    schemeReading (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (chartToSpace B S hS X (bundleBaseChart X)) ≅
      Scheme.unitModule (chartScheme (bundleBaseChart X)) :=
  schemeReadingChartIso _ _ ≪≫ restrictToChartSchemeUnitIso B S hS X.1 X.2 _

/-- The summand `𝒪 ⟶ (ℰ ⊕ 𝒪)|_U` on the presenting chart. -/
abbrev completionChartSection :
    Scheme.unitModule (chartScheme (bundleBaseChart X)) ⟶
      chartBundleModule (addUnit X.2 E) (bundleBaseChart X) :=
  (completionChartUnitIso (X := X)).inv ≫ chartModuleMap (addUnitInr X.2 E) (bundleBaseChart X)

/-- The projection `(ℰ ⊕ 𝒪)|_U ⟶ 𝒪` on the presenting chart. -/
abbrev completionChartRetraction :
    chartBundleModule (addUnit X.2 E) (bundleBaseChart X) ⟶
      Scheme.unitModule (chartScheme (bundleBaseChart X)) :=
  chartModuleMap (addUnitSnd X.2 E) (bundleBaseChart X) ≫ (completionChartUnitIso (X := X)).hom

/-- On the presenting chart, the readings of the projection `(ℰ ⊕ 𝒪)|_U ⟶ 𝒪` followed by the
summand `𝒪 ⟶ (ℰ ⊕ 𝒪)|_U`, and of the projection `ℰ ⊕ 𝒪 ⟶ ℰ` followed by the inclusion
`ℰ ⟶ ℰ ⊕ 𝒪`, sum to the identity of `(ℰ ⊕ 𝒪)|_U`. -/
theorem completionChart_split :
    completionChartRetraction E ≫ completionChartSection E +
        chartModuleMap biprod.fst (bundleBaseChart X) ≫
          chartModuleMap biprod.inl (bundleBaseChart X) =
      𝟙 (chartBundleModule (addUnit X.2 E) (bundleBaseChart X)) := by
  simp only [completionChartRetraction, completionChartSection, Category.assoc,
    Iso.hom_inv_id_assoc]
  unfold addUnitSnd addUnitInr
  rw [chartModuleMap_comp_chartModuleMap, chartModuleMap_comp_chartModuleMap,
    chartModuleMap_add, add_comm, biprod.total, chartModuleMap_id]

/-- On the presenting chart, the summand `𝒪 ⟶ (ℰ ⊕ 𝒪)|_U` followed by the reading of the
projection `ℰ ⊕ 𝒪 ⟶ ℰ` is zero. -/
theorem completionChartSection_comp_fst :
    completionChartSection E ≫ chartModuleMap biprod.fst (bundleBaseChart X) = 0 := by
  simp only [completionChartSection, Category.assoc, chartModuleMap_comp_chartModuleMap]
  rw [addUnitInr, biprod.inr_fst, chartModuleMap_zero, comp_zero]

end Completion

end AlgebraicGeometry.Space

end
