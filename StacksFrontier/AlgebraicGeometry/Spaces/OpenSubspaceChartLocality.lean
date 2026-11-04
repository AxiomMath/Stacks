module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCoversTopOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocalHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianAffineChartFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# Properties of modules on an open subspace read on étale charts

Let `U` be an open subspace of an algebraic space `X` and let `cⱼ` be a family of étale charts of
`X` whose images lie in `|U|` and cover it. A morphism of `𝒪_X`-modules restricts to an
isomorphism on `U` as soon as its components at all charts of `X` over some `cⱼ` are
isomorphisms, and an `𝒪_X`-module restricts to zero on `U` as soon as its sections over all
those charts vanish.

## Main results

* `AlgebraicGeometry.Space.liftChart`: the chart `cⱼ` read as a chart of `U`.
* `AlgebraicGeometry.Space.isIso_modulePullback_map_openSubspaceHom_of_forall`.
* `AlgebraicGeometry.Space.isZero_modulePullback_obj_openSubspaceHom_of_forall`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {U : Subfunctor X.1}
  {ι : Type v}

/-- The image of the étale chart `c` in the points of `X`. -/
abbrev chartPointsRange (c : SmallEtale B S hS X.1) : Set (points B S hS X.1) :=
  Set.range (pointsMap B S hS (chartSpace B S hS X c).1 (chartToSpace B S hS X c).hom)

/-- An étale chart whose image lies in an open subspace factors through it. -/
theorem exists_lift_chart (hU : IsOpenSubspace B S hS U) (c : ι → SmallEtale B S hS X.1) (j : ι)
    (hcU : chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    ∃ g : yoneda.obj (c j).1.left ⟶ U.toFunctor, g ≫ U.ι = (c j).1.hom :=
  (factorsThrough_openSubspace_iff_points B S hS X.2 (chartSpace B S hS X (c j)).2 U hU
    (c j).1.hom).2 hcU

variable (hU : IsOpenSubspace B S hS U) {c : ι → SmallEtale B S hS X.1}

/-- The étale chart `cⱼ` of `X`, read as an étale chart of the open subspace `U` through which
it factors. -/
def liftChart (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    (j : ι) : SmallEtale B S hS (openSubspaceSpace B S hS U hU).1 :=
  ⟨CostructuredArrow.mk (exists_lift_chart hU c j (hcU j)).choose,
    isEtaleChart_of_comp_etale B S hS (openSubspaceHom B S hS U hU)
      (isEtale_openSubspaceHom B S hS U hU) _ (by
        change IsEtaleChart B S hS X.1
          (CostructuredArrow.mk ((exists_lift_chart hU c j (hcU j)).choose ≫ U.ι))
        rw [(exists_lift_chart hU c j (hcU j)).choose_spec]
        exact (c j).2)⟩

/-- The chart `cⱼ` read through `U` and carried back to `X` is `cⱼ`. -/
def postcompLiftChartIso
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι)) (j : ι) :
    (smallEtalePostcomp B S hS (openSubspaceHom B S hS U hU)
      (isEtale_openSubspaceHom B S hS U hU)).obj (liftChart hU hcU j) ≅ c j where
  hom := ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) (by
    have h : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj (c j).1.left ⟶ Y),
        yoneda.map (𝟙 (c j).1.left) ≫ f = f := fun f => by simp
    exact (h _).trans (exists_lift_chart hU c j (hcU j)).choose_spec.symm))
  inv := ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) (by
    have h : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj (c j).1.left ⟶ Y),
        yoneda.map (𝟙 (c j).1.left) ≫ f = f := fun f => by simp
    exact (h _).trans (exists_lift_chart hU c j (hcU j)).choose_spec))
  hom_inv_id := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (Category.comp_id _))
  inv_hom_id := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (Category.comp_id _))

/-- The lifted charts cover the small étale site of `U` when the charts cover `|U|`. -/
theorem coversTop_liftChart
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hUc : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆ ⋃ j, chartPointsRange (c j)) :
    (SmallEtale.topology B S hS (openSubspaceSpace B S hS U hU).1).CoversTop
      (liftChart hU hcU) := by
  refine SmallEtale.coversTop_of_iUnion_range_eq_univ B S hS _ _ ?_
  refine Set.eq_univ_of_forall fun w => ?_
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hUc ⟨w, rfl⟩)
  obtain ⟨t, ht⟩ := hj
  have e : (chartToSpace B S hS (openSubspaceSpace B S hS U hU) (liftChart hU hcU j)).hom ≫
      U.ι = (chartToSpace B S hS X (c j)).hom := (exists_lift_chart hU c j (hcU j)).choose_spec
  refine Set.mem_iUnion.2 ⟨j, t, pointsMap_injective_of_mono B S hS U.ι ?_⟩
  rw [← ht, ← e]
  exact (congrFun (pointsMap_comp B S hS _ _ U.ι) t).symm

/-- A morphism of lifted charts, carried back to `X`, gives a morphism to the original chart. -/
private def postcomp_hom_chart
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    {j : ι} {A : SmallEtale B S hS (openSubspaceSpace B S hS U hU).1} (g : A ⟶ liftChart hU hcU j) :
    (smallEtalePostcomp B S hS (openSubspaceHom B S hS U hU)
      (isEtale_openSubspaceHom B S hS U hU)).obj A ⟶ c j :=
  (smallEtalePostcomp B S hS (openSubspaceHom B S hS U hU)
    (isEtale_openSubspaceHom B S hS U hU)).map g ≫ (postcompLiftChartIso hU hcU j).hom

/-- **A morphism of `𝒪_X`-modules is an isomorphism on `U` when it is one over the charts.** If
the charts `cⱼ` lie in `U` and cover it, and the components of `φ` at all charts of `X` over
some `cⱼ` are isomorphisms, then the restriction of `φ` to `U` is an isomorphism. -/
theorem isIso_etaleModulePullback_map_openSubspaceHom_of_forall
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hUc : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆ ⋃ j, chartPointsRange (c j))
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ (j : ι) (T : SmallEtale B S hS X.1), (T ⟶ c j) → IsIso (φ.val.app (op T))) :
    IsIso ((etaleModulePullback B S hS (openSubspaceHom B S hS U hU)
      (isEtale_openSubspaceHom B S hS U hU)).map φ) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop
    (coversTop_liftChart hU hcU hUc) _ fun j T f => by
      have hb := h j _ (postcomp_hom_chart hU hcU f)
      rw [ConcreteCategory.isIso_iff_bijective] at hb ⊢
      exact hb

/-- The restriction to `U` of a morphism of `𝒪_X`-modules is an isomorphism when its components
at all charts of `X` over some `cⱼ` are. -/
theorem isIso_modulePullback_map_openSubspaceHom_of_forall
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hUc : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆ ⋃ j, chartPointsRange (c j))
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : ∀ (j : ι) (T : SmallEtale B S hS X.1), (T ⟶ c j) → IsIso (φ.val.app (op T))) :
    IsIso ((modulePullback B S hS (openSubspaceHom B S hS U hU)).map φ) :=
  (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS
    (openSubspaceHom B S hS U hU) (isEtale_openSubspaceHom B S hS U hU)) φ).2
    (isIso_etaleModulePullback_map_openSubspaceHom_of_forall hU hcU hUc φ h)

/-- **An `𝒪_X`-module restricts to zero on `U` when its sections over the charts vanish.** -/
theorem isZero_modulePullback_obj_openSubspaceHom_of_forall
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hUc : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆ ⋃ j, chartPointsRange (c j))
    (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ (j : ι) (T : SmallEtale B S hS X.1), (T ⟶ c j) → IsZero (M.val.obj (op T))) :
    IsZero ((modulePullback B S hS (openSubspaceHom B S hS U hU)).obj M) := by
  set N := (etaleModulePullback B S hS (openSubspaceHom B S hS U hU)
    (isEtale_openSubspaceHom B S hS U hU)).obj M
  have hN : IsIso (0 : N ⟶ N) :=
    Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop
      (coversTop_liftChart hU hcU hUc) _ fun j T f => by
        have hz' := h j _ (postcomp_hom_chart hU hcU f)
        rw [ModuleCat.isZero_iff_subsingleton] at hz'
        have hz : IsZero (N.val.obj (op T)) := ModuleCat.isZero_iff_subsingleton.2 hz'
        exact hz.isIso hz _
  have hNz : IsZero N := by
    rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : N ⟶ N), Limits.zero_comp]
  exact hNz.of_iso ((modulePullbackIsoEtaleModulePullback B S hS
    (openSubspaceHom B S hS U hU) (isEtale_openSubspaceHom B S hS U hU)).app M)

/-- **The image of a base-changed chart is the preimage of the image of the chart.** -/
theorem chartPointsRange_smallBaseChange {X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS X.1) :
    chartPointsRange ((smallBaseChange B S hS f hf).obj V) =
      pointsMap B S hS X'.1 f.hom ⁻¹' chartPointsRange V := by
  have h := preimage_image_pointsMap_of_isPullback B S hS (hf.isPullback V.1.hom).flip Set.univ
  simp only [Set.image_univ, Set.preimage_univ] at h
  exact h.symm

/-- **The stage form of the iso criterion.** Let `f : X' ⟶ X` be representable and let the
charts `cⱼ` of `X` lie in the open subspace `U` and cover it. A morphism of `𝒪_{X'}`-modules
whose components at all charts of `X'` over some base change `cⱼ ×_X X'` are isomorphisms
restricts to an isomorphism on `f⁻¹(U)`. -/
theorem isIso_modulePullback_map_preimage_of_forall {X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hU' : IsOpenSubspace B S hS (U.preimage f.hom))
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hUc : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆ ⋃ j, chartPointsRange (c j))
    {M N : Modules.{u, u} B S hS X'.1 X'.2} (φ : M ⟶ N)
    (h : ∀ (j : ι) (T : SmallEtale B S hS X'.1), (T ⟶ (smallBaseChange B S hS f hf).obj (c j)) →
      IsIso (φ.val.app (op T))) :
    IsIso ((modulePullback B S hS (openSubspaceHom B S hS (U.preimage f.hom) hU')).map φ) := by
  refine isIso_modulePullback_map_openSubspaceHom_of_forall hU'
    (c := fun j => (smallBaseChange B S hS f hf).obj (c j)) ?_ ?_ φ h
  · intro j
    rw [chartPointsRange_smallBaseChange, range_pointsMap_preimage_ι]
    exact Set.preimage_mono (hcU j)
  · rw [range_pointsMap_preimage_ι]
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hUc hx)
    exact Set.mem_iUnion.2 ⟨j, by rw [chartPointsRange_smallBaseChange]; exact hj⟩

/-- **Finite presentation on `U` read on the affine charts over the `cⱼ`.** A quasi-coherent
`𝒪_X`-module whose sections over every affine chart of `X` over some `cⱼ` are finitely presented
restricts to a module of finite presentation on `U`. -/
theorem isFinitePresentationOnSite_modulePullback_openSubspaceHom_of_forall
    (hcU : ∀ j, chartPointsRange (c j) ⊆ Set.range (pointsMap B S hS U.toFunctor U.ι))
    (hUc : Set.range (pointsMap B S hS U.toFunctor U.ι) ⊆ ⋃ j, chartPointsRange (c j))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (h : ∀ (j : ι) (T : SmallEtale B S hS X.1),
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj T) →
        (T ⟶ c j) → Module.FinitePresentation (chartRing B S hS X.1 X.2 T) (M.val.obj (op T))) :
    ((modulePullback B S hS (openSubspaceHom B S hS U hU)).obj M).IsFinitePresentationOnSite := by
  classical
  set Us := openSubspaceSpace B S hS U hU
  set f := openSubspaceHom B S hS U hU
  set hf := isEtale_openSubspaceHom B S hS U hU
  set P := (modulePullback B S hS f).obj M
  have hPq : P.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f M hM
  have hPc : IsCartesianOnAffineCharts P :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Us.1 Us.2 P hPq
  have hfp : ∀ (A : SmallEtale B S hS Us.1)
      (_ : IsAffine ((SmallEtale.toOver B S hS Us.1 ⋙ BigFppfOver.toScheme B S hS).obj A))
      (j : ι), (A ⟶ liftChart hU hcU j) →
        Module.FinitePresentation (chartRing B S hS Us.1 Us.2 A) (P.val.obj (op A)) := by
    intro A hA j g
    have h₁ := h j ((smallEtalePostcomp B S hS f hf).obj A) (by exact hA)
      (postcomp_hom_chart hU hcU g)
    have h₀ : Module.FinitePresentation (chartRing B S hS Us.1 Us.2 A)
        (((etaleModulePullback B S hS f hf).obj M).val.obj (op A)) := h₁
    let e : (((etaleModulePullback B S hS f hf).obj M).val.obj (op A)) ≃ₗ[
        chartRing B S hS Us.1 Us.2 A] (P.val.obj (op A)) :=
      ((PresheafOfModules.evaluation _ (op A)).mapIso ((SheafOfModules.forget _).mapIso
        ((modulePullbackIsoEtaleModulePullback B S hS f hf).app M).symm)).toLinearEquiv
    exact Module.FinitePresentation.of_equiv e
  refine ⟨fun V => ?_⟩
  have hcov := coversTop_liftChart hU hcU hUc V
  choose I Y a hYaff hY _ using fun (Z : SmallEtale B S hS Us.1) =>
    SmallEtale.exists_affine_etale_ofArrows B S hS Us.1 Z
  let ι' := {q : Σ (A : SmallEtale B S hS Us.1), (A ⟶ V) //
    IsAffine ((SmallEtale.toOver B S hS Us.1 ⋙ BigFppfOver.toScheme B S hS).obj q.1) ∧
      ∃ j, Nonempty (q.1 ⟶ liftChart hU hcU j)}
  refine ⟨ι', fun q => q.1.1, fun q => q.1.2, ?_, fun q => ?_⟩
  · refine (SmallEtale.topology B S hS Us.1).superset_covering ?_
      ((SmallEtale.topology B S hS Us.1).bind_covering hcov
        (fun Z g _ => hY Z))
    rintro W e ⟨Z, g, h', hg, hh, rfl⟩
    obtain ⟨j, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff _ h').1 hg
    obtain ⟨k, t, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).1 hh
    exact ⟨_, t, _, ⟨(⟨⟨Y Z k, a Z k ≫ h'⟩, hYaff Z k, j, ⟨a Z k ≫ b⟩⟩ : ι')⟩,
      (Category.assoc _ _ _).symm⟩
  · obtain ⟨hA, j, ⟨b⟩⟩ := q.2
    have := hfp q.1.1 hA j b
    exact hasFiniteGlobalPresentation_over_of_finitePresentation P hPc hA

end AlgebraicGeometry.Space
