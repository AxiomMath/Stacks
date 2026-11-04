module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingCounterexampleStages
public import StacksFrontier.AlgebraicGeometry.Spaces.UnitSheafChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartDiagramSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreservingAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftedEtalePresentationCharts

/-!
# Stacks 082Q as written is false: a counterexample on algebraic spaces

Stacks 082Q asserts that in Situation 082M, if (a) `f : X ⟶ B` is quasi-compact and
quasi-separated and (b) `F` is of finite presentation, then `Q^{fp}_{F/X/B}` is limit preserving.
This file proves the negation of that statement, at every universe `u`, in the language of the
library: `AlgebraicGeometry.Space.QuotientSituation`,
`AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsFunctor` and
`AlgebraicGeometry.LimitPreserving`.  The corrected statement, which adds that `f` is locally of
finite presentation, is, in the namespace `AlgebraicGeometry.Space.QuotientSituation`,
`finitePresentationQuotientsFunctor_limitPreserving_of_isLocallyOfFinitePresentation`.

The witness, over any big fppf site (every countable ring has its spectrum in it):

* `S = Y = Spec ℚ[t]`, `X = Spec B₀` with `B₀ = ℚ[t][y_a : a ∈ ℚ]/((t - a) y_a)`, `f` the image of
  `ℚ[t] → B₀`, a morphism of affine schemes, hence quasi-compact and quasi-separated, and
  `F = 𝒪_X`, of finite presentation;
* the inverse system `T_g = Spec ℚ[t]_g`, `g ≠ 0` ordered by divisibility, whose limit is
  `T = Spec ℚ(t)` because `Spec` turns the filtered colimit `ℚ(t) = colim ℚ[t]_g` into a limit;
* the identity quotient of `F_T` lies in `Q^{fp}(T)`: `F_T` is of finite presentation, and it is
  flat over `T` because the étale local rings of the spectrum of a field are fields;
* it comes from no stage: `X_{T_g}` is represented by `Spec R_g`, `R_g = ℚ[t]_g ⊗ B₀`, and a
  finitely presented quotient of `F_{T_g}` flat over `T_g` whose pullback to `T` is the identity
  quotient gives, on sections over `Spec R_g`, a nonzero cyclic `R_g`-module of finite
  presentation flat over `ℚ[t]_g`, which does not exist
  (`AlgebraicGeometry.QuotientFunctorCounterexample.false_of_flat_of_finitePresentation`).

## Main results

* `AlgebraicGeometry.Space.QuotientSituation`'s
  `not_forall_finitePresentationQuotientsFunctor_limitPreserving`:
  **Stacks 082Q as written is false.**
* `AlgebraicGeometry.QuotientFunctorCounterexample.bot_mem_finitePresentationQuotients`: the
  identity quotient over `T = Spec ℚ(t)` is a finitely presented quotient flat over `T`.
* `AlgebraicGeometry.QuotientFunctorCounterexample.quotientPullback_ne_bot`: no finitely
  presented quotient at a stage pulls back to it.

## Implementation notes

A stage quotient is read on its sections over the étale chart `Spec R_g ⟶ X_{T_g}`, an
isomorphism onto the base change, through three bridges: flatness over the base gives flatness
of the sections (Stacks 05VV, 01U4;
`AlgebraicGeometry.Space.flat_sections_of_isFlatOver_chartDiagram`), the projection
`𝒪 ≅ F_{T_g} ⟶ Q` is surjective on sections (Stacks 03DW;
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`), and the sections
are finitely presented. If the projection
kills `1`, the quotient is zero, and so is its pullback to `T`, which is then not `F_T ≠ 0`.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

universe u

namespace AlgebraicGeometry.QuotientFunctorCounterexample

open Space

attribute [local instance] countable_polynomial countable_stageRing countable_fibreRing
  countable_fractionRing

variable (B : BigFppfSite.{u})

/-- The base scheme `S = Y = Spec ℚ[t]`. -/
abbrev baseScheme : Scheme.{u} := Spec (uR.{u} (StageRing 1))

/-- The base scheme `Spec ℚ[t]` is in the site. -/
theorem contains_baseScheme : B.Contains baseScheme.{u} :=
  AlgebraicGeometry.Space.contains_spec_of_countable B _

/-- The base `Y = Spec ℚ[t]`, as an object of the big fppf site over itself. -/
abbrev baseObj : BigFppfOver B baseScheme (contains_baseScheme B) :=
  siteObject B baseScheme (contains_baseScheme B) (contains_baseScheme B) (𝟙 _)

/-- The source `X = Spec B₀`, `B₀ = ℚ[t][y_a]/((t - a) y_a)`. -/
abbrev sourceObj : BigFppfOver B baseScheme (contains_baseScheme B) :=
  siteObject B baseScheme (contains_baseScheme B)
    (AlgebraicGeometry.Space.contains_spec_of_countable B _)
    (Spec.map (uHom.{u} (algebraMap (StageRing 1) (FibreRing 1))))

/-- The morphism `f : X ⟶ Y`. -/
abbrev sourceHom : sourceObj B ⟶ baseObj B :=
  Over.homMk (ObjectProperty.homMk (Spec.map (uHom.{u} (algebraMap (StageRing 1) (FibreRing 1)))))
    (by apply ObjectProperty.hom_ext; exact Category.comp_id _)

/-- **The situation of the counterexample**: `f : X = Spec B₀ ⟶ Y = Spec ℚ[t]` with `F = 𝒪_X`. -/
def situation : QuotientSituation B baseScheme (contains_baseScheme B) where
  X := (schemeSpaceFunctor B _ _).obj (sourceObj B)
  Y := (schemeSpaceFunctor B _ _).obj (baseObj B)
  f := (schemeSpaceFunctor B _ _).map (sourceHom B)
  F := SheafOfModules.unit _
  quasicoherent :=
    haveI : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B
        _ _ ((schemeSpaceFunctor B _ _).obj (sourceObj B)).1
          ((schemeSpaceFunctor B _ _).obj (sourceObj B)).2).O)).IsFinitePresentationOnSite :=
      SheafOfModules.isFinitePresentationOnSite_unit
    inferInstance

/-! ### The test schemes -/

/-- The stage `T_g = Spec ℚ[t]_g`, as an object of the site. -/
abbrev stageObj (i : Stage.{u}) : BigFppfOver B baseScheme (contains_baseScheme B) :=
  siteObject B baseScheme (contains_baseScheme B)
    (AlgebraicGeometry.Space.contains_spec_of_countable B _)
    (Spec.map (uHom.{u} (stageMap (one_dvd i.poly))))

/-- The structure morphism `T_g ⟶ Y`. -/
abbrev stageHom (i : Stage.{u}) : stageObj B i ⟶ baseObj B :=
  Over.homMk (ObjectProperty.homMk (Spec.map (uHom.{u} (stageMap (one_dvd i.poly)))))
    (by apply ObjectProperty.hom_ext; exact Category.comp_id _)

/-- The stage `T_g`, as a test scheme over `Y`. -/
abbrev stageTest (i : Stage.{u}) : SchemesOver (situation B).Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B _ _).map (stageHom B i))

/-- The limit `T = Spec ℚ(t)`, as an object of the site. -/
abbrev genericObj : BigFppfOver B baseScheme (contains_baseScheme B) :=
  siteObject B baseScheme (contains_baseScheme B)
    (AlgebraicGeometry.Space.contains_spec_of_countable B _)
    (Spec.map (uHom.{u} (toFraction (one_ne_zero (α := ℚ[X])))))

/-- The structure morphism `T ⟶ Y`. -/
abbrev genericHom : genericObj B ⟶ baseObj B :=
  Over.homMk (ObjectProperty.homMk (Spec.map (uHom.{u} (toFraction (one_ne_zero (α := ℚ[X]))))))
    (by apply ObjectProperty.hom_ext; exact Category.comp_id _)

/-- The limit `T`, as a test scheme over `Y`. -/
abbrev genericTest : SchemesOver (situation B).Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B _ _).map (genericHom B))

/-- The transition maps of the stages commute with their structure morphisms. -/
theorem specMap_stageMap_comp {g h : ℚ[X]} (hgh : g ∣ h) :
    Spec.map (uHom.{u} (stageMap hgh)) ≫ Spec.map (uHom.{u} (stageMap (one_dvd g))) =
      Spec.map (uHom.{u} (stageMap (one_dvd h))) := by
  rw [← Spec.map_comp, uHom_comp, stageMap_trans]

/-- The projections `T ⟶ T_g` commute with the structure morphisms. -/
theorem specMap_toFraction_comp {g : ℚ[X]} (hg : g ≠ 0) :
    Spec.map (uHom.{u} (toFraction hg)) ≫ Spec.map (uHom.{u} (stageMap (one_dvd g))) =
      Spec.map (uHom.{u} (toFraction (one_ne_zero (α := ℚ[X])))) := by
  rw [← Spec.map_comp, uHom_comp, toFraction_comp_stageMap]

/-- The transition morphism `T_h ⟶ T_g` for `g ∣ h`. -/
def stageTransition {i j : Stage.{u}} (hij : j.poly ∣ i.poly) : stageTest B i ⟶ stageTest B j :=
  CostructuredArrow.homMk
    (Over.homMk (ObjectProperty.homMk (Spec.map (uHom.{u} (stageMap hij))))
      (by apply ObjectProperty.hom_ext; exact specMap_stageMap_comp hij))
    (by
      refine ((schemeSpaceFunctor B _ _).map_comp _ _).symm.trans (congrArg _ ?_)
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact specMap_stageMap_comp hij)

/-- **The inverse system `T_g = Spec ℚ[t]_g`, `g ≠ 0`, of test schemes over `Y`.** -/
def stageDiagram : Stage.{u} ⥤ SchemesOver (situation B).Y where
  obj i := stageTest B i
  map f := stageTransition B (leOfHom f)
  map_id i := by
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (uHom.{u} (stageMap _)) = 𝟙 _
    rw [uHom_congr (stageMap_refl i.poly), uHom_id, Spec.map_id]
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change Spec.map (uHom.{u} (stageMap _)) =
      Spec.map (uHom.{u} (stageMap _)) ≫ Spec.map (uHom.{u} (stageMap _))
    rw [← Spec.map_comp, uHom_comp, stageMap_trans]

/-- The projection `T ⟶ T_g`. -/
def stageConeπ (i : Stage.{u}) : genericTest B ⟶ stageTest B i :=
  CostructuredArrow.homMk
    (Over.homMk (ObjectProperty.homMk (Spec.map (uHom.{u} (toFraction i.ne_zero))))
      (by apply ObjectProperty.hom_ext; exact specMap_toFraction_comp i.ne_zero))
    (by
      refine ((schemeSpaceFunctor B _ _).map_comp _ _).symm.trans (congrArg _ ?_)
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact specMap_toFraction_comp i.ne_zero)

/-- **`T = Spec ℚ(t)` with its projections to the stages.** -/
def stageCone : Cone (stageDiagram B) where
  pt := genericTest B
  π :=
    { app i := stageConeπ B i
      naturality i j f := by
        apply CostructuredArrow.hom_ext
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        change 𝟙 _ ≫ Spec.map (uHom.{u} (toFraction j.ne_zero)) =
          Spec.map (uHom.{u} (toFraction i.ne_zero)) ≫ Spec.map (uHom.{u} (stageMap _))
        rw [Category.id_comp, ← Spec.map_comp, uHom_comp, toFraction_comp_stageMap] }

/-- **`Spec ℚ(t)` is the limit of the `Spec ℚ[t]_g`**: `Spec` turns the filtered colimit
`ℚ(t) = colim ℚ[t]_g` into a limit of schemes. -/
def isLimitStageCone : IsLimit ((situation B).testScheme.mapCone (stageCone B)) :=
  isLimitOfPreserves Scheme.Spec
    (isLimitConeOfCoconeLeftOp stageRingDiagram.{u}.rightOp isColimitFractionCocone)

/-! ### The base change to a stage -/

section Fibre

variable (i : Stage.{u})

/-- `Spec R_g`, the base change of `X` to the stage `T_g`, as an object of the site. -/
abbrev fibreObj : BigFppfOver B baseScheme (contains_baseScheme B) :=
  siteObject B baseScheme (contains_baseScheme B)
    (AlgebraicGeometry.Space.contains_spec_of_countable B _)
    (Spec.map (uHom.{u} (algebraMap (StageRing i.poly) (FibreRing i.poly))) ≫
      Spec.map (uHom.{u} (stageMap (one_dvd i.poly))))

/-- The projection `Spec R_g ⟶ X`. -/
abbrev fibreToSource : fibreObj B i ⟶ sourceObj B :=
  Over.homMk (ObjectProperty.homMk (Spec.map (uHom.{u} (fibreMap i.poly)))) (by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, uHom_comp, uHom_comp, fibreMap_comp_algebraMap])

/-- The projection `Spec R_g ⟶ T_g`. -/
abbrev fibreToStage : fibreObj B i ⟶ stageObj B i :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (uHom.{u} (algebraMap (StageRing i.poly) (FibreRing i.poly))))) rfl

/-- **`Spec R_g = X ×_Y T_g`** in the site. -/
theorem isPullback_fibreObj :
    IsPullback (fibreToSource B i) (fibreToStage B i) (sourceHom B) (stageHom B i) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_fibreRing.{u} i.poly)
  have _ : ReflectsLimit (cospan (sourceHom B) (stageHom B i))
      (BigFppfOver.toScheme B baseScheme (contains_baseScheme B)) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B _ _) h

/-- **`Spec R_g = X ×_Y T_g`** among the represented presheaves. -/
theorem isPullback_yoneda_fibreObj :
    IsPullback (yoneda.map (fibreToSource B i)) (yoneda.map (fibreToStage B i))
      (situation B).f.hom (stageTest B i).hom.hom :=
  (isPullback_fibreObj B i).map yoneda

/-- The étale chart `Spec R_g ⟶ X_{T_g}`, an isomorphism. -/
def fibreChart : Space.SmallEtale B _ _ ((situation B).space (stageTest B i)).1 :=
  ⟨CostructuredArrow.mk (isPullback_yoneda_fibreObj B i).isoPullback.hom,
    @isEtaleChart_of_isIso B _ _ (fibreObj B i) _ _ (Iso.isIso_hom _)⟩

/-- Every étale chart of `X_{T_g}` maps to the chart `Spec R_g`. -/
theorem nonempty_hom_fibreChart
    (V : Space.SmallEtale B _ _ ((situation B).space (stageTest B i)).1) :
    Nonempty (V ⟶ fibreChart B i) :=
  ⟨ObjectProperty.homMk (CostructuredArrow.homMk (Yoneda.fullyFaithful.preimage
    (V.obj.hom ≫ (isPullback_yoneda_fibreObj B i).isoPullback.inv)) (by
      refine (congrArg (· ≫ (isPullback_yoneda_fibreObj B i).isoPullback.hom)
        (Yoneda.fullyFaithful.map_preimage _)).trans ?_
      exact (Category.assoc _ _ _).trans ((congrArg (V.obj.hom ≫ ·)
        (isPullback_yoneda_fibreObj B i).isoPullback.inv_hom_id).trans (Category.comp_id _))))⟩

/-- The chart diagram `Spec R_g ⟶ T_g` over `X_{T_g} ⟶ T_g`. -/
abbrev fibreChartDiagram : ChartDiagram B _ _ ((situation B).space (stageTest B i)).1
    ((schemeSpaceFunctor B _ _).obj (stageObj B i)).1
    ((situation B).projection (stageTest B i)).hom where
  U := fibreChart B i
  V := idChart B _ _ (stageObj B i)
  g := fibreToStage B i
  comm := by
    change (isPullback_yoneda_fibreObj B i).isoPullback.hom ≫ pullback.snd _ _ =
      yoneda.map (fibreToStage B i) ≫ 𝟙 _
    rw [Category.comp_id]
    exact (isPullback_yoneda_fibreObj B i).isoPullback_hom_snd

end Fibre

/-! ### The generic point: the identity quotient over `T = Spec ℚ(t)` -/

/-- Every module over a field is flat. -/
theorem flat_of_isField {K M : Type*} [CommRing K] [AddCommGroup M] {inst : Module K M}
    (hK : IsField K) : @Module.Flat K M _ _ inst := by
  let := hK.toField
  infer_instance

/-- The quotient of an object of an abelian category by its zero subobject is the object. -/
def cokernelBotIso {C : Type*} [Category* C] [Abelian C] (M : C) :
    cokernel (⊥ : Subobject M).arrow ≅ M :=
  cokernelIsoOfEq Subobject.bot_arrow ≪≫ cokernelZeroIsoTarget

/-- The zero subobject of an object of an abelian category, named so that its order instance is
found in the abelian category rather than in the ambient category of modules. -/
abbrev zeroSubobject {C : Type*} [Category* C] [Abelian C] (M : C) : Subobject M := ⊥

attribute [local instance] BigFppfSite.hasPullbacks_schemes
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- The identity quotient is the quotient by `⊥`, whose quotient module is `F_T` itself. -/
def quotientModuleBotIso (T : SchemesOver (situation B).Y) :
    (situation B).quotientModule T (zeroSubobject _) ≅ (situation B).baseChangeModule T :=
  cokernelBotIso _

/-- `F_T = (X_T ⟶ X)^*𝒪_X` is of finite presentation. -/
theorem isFinitePresentationOnSite_baseChangeModule (T : SchemesOver (situation B).Y) :
    ((situation B).baseChangeModule T).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_modulePullback B _ _ ((situation B).sourceProjection T)
    (situation B).F SheafOfModules.isFinitePresentationOnSite_unit

/-- **The identity quotient of `F_T` over `T = Spec ℚ(t)` is in `Q^{fp}(T)`**: it is `F_T`, which
is of finite presentation, and every module is flat over the spectrum of a field. -/
theorem bot_mem_finitePresentationQuotients :
    zeroSubobject ((situation B).baseChangeModule (genericTest B)) ∈
      (situation B).finitePresentationQuotients (genericTest B) := by
  have hfp :
      ((situation B).quotientModule (genericTest B) (zeroSubobject _)).IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso (quotientModuleBotIso B _).symm
      (isFinitePresentationOnSite_baseChangeModule B _)
  have := hfp
  refine ⟨⟨inferInstance, ?_⟩, hfp⟩
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint]
  intro xbar
  have hfield := isField_etaleLocalRing_yoneda (genericObj B)
    (fun x => isField_stalk_Spec_field (ULift.{u} (FractionRing ℚ[X])) x)
    (geometricPointMap ((situation B).projection (genericTest B)).hom xbar)
  exact flat_of_isField hfield

/-- The chart of `X_T` given by the represented fibre product `T ×_Y X` of the site. -/
def genericChart : Space.SmallEtale B _ _ ((situation B).space (genericTest B)).1 :=
  ⟨CostructuredArrow.mk (HomSituation.affineFiberIso (sourceHom B) (genericTest B)).hom.hom,
    @isEtaleChart_of_isIso B _ _ _ _ _ (Iso.isIso_hom ((ObjectProperty.ι _).mapIso
      (HomSituation.affineFiberIso (sourceHom B) (genericTest B))))⟩

/-- The generic point `T ⟶ X` of `X = Spec B₀`, `y_a ↦ 0`. -/
abbrev genericToSource : genericObj B ⟶ sourceObj B :=
  Over.homMk (ObjectProperty.homMk (Spec.map (uHom.{u} genericFibre))) (by
    apply ObjectProperty.hom_ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, uHom_comp, show genericFibre.comp (algebraMap (StageRing 1)
      (FibreRing 1)) = toFraction (one_ne_zero (α := ℚ[X])) from
        RingHom.ext genericFibre_algebraMap])

/-- The structure morphism of the test scheme `T`, read in the site. -/
theorem affineTestHom_genericTest :
    HomSituation.affineTestHom (genericTest B) = genericHom B :=
  Yoneda.fullyFaithful.map_injective (HomSituation.yoneda_map_affineTestHom _)

/-- **The functions on `X_T` do not vanish**: `X_T` has the point `T ⟶ X_T` given by the generic
point of `X`. -/
theorem nontrivial_genericChart :
    Nontrivial (chartRing B baseScheme (contains_baseScheme B)
      ((situation B).space (genericTest B)).1
      ((situation B).space (genericTest B)).2 (genericChart B)) := by
  let s : genericObj B ⟶ pullback (HomSituation.affineTestHom (genericTest B)) (sourceHom B) :=
    pullback.lift (𝟙 _) (genericToSource B) (by
      rw [Category.id_comp, affineTestHom_genericTest]
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact congrArg (·.hom) (Over.w (genericToSource B)).symm)
  have x : chartScheme (genericChart B) :=
    (BigFppfOver.toScheme B _ _).map s (Nonempty.some (inferInstance :
      Nonempty (Spec (uR.{u} (FractionRing ℚ[X])))))
  have : Nonempty (⊤ : (chartScheme (genericChart B)).Opens) := ⟨⟨x, trivial⟩⟩
  exact Scheme.component_nontrivial (chartScheme (genericChart B)) ⊤

/-- **`F_T` is not zero.** -/
theorem not_isZero_baseChangeModule_generic :
    ¬ IsZero ((situation B).baseChangeModule (genericTest B)) := by
  intro hz
  have hz' := hz.of_iso (modulePullbackUnitIso B _ _ ((situation B).sourceProjection
    (genericTest B))).symm
  have := nontrivial_genericChart B
  exact one_ne_zero (one_eq_zero_of_isZero_unit (genericChart B) hz')

/-! ### No stage quotient restricts to the identity quotient -/

/-- If the quotient at a stage is zero, its pullback to `T` is not the identity quotient. -/
theorem quotientPullback_ne_bot_of_isZero (i : Stage.{u})
    (K : Subobject ((situation B).baseChangeModule (stageTest B i)))
    (hQ : IsZero ((situation B).quotientModule (stageTest B i) K)) :
    (situation B).quotientPullback (stageConeπ B i) K ≠ zeroSubobject _ := by
  intro hpb
  have := (modulePullbackAdjunction B _ _
    ((situation B).relativeMap (stageConeπ B i))).isLeftAdjoint
  have hz := (Functor.map_isZero (modulePullback B _ _
    ((situation B).relativeMap (stageConeπ B i))) hQ).of_iso
      ((situation B).quotientPullbackCokernelIso (stageConeπ B i) K)
  rw [hpb] at hz
  exact not_isZero_baseChangeModule_generic B (hz.of_iso (quotientModuleBotIso B _).symm)

/-- The ring isomorphism `𝒪(Spec R_g) ≅ R_g`. -/
def fibreChartRingEquiv (i : Stage.{u}) :
    chartRing B baseScheme (contains_baseScheme B) ((situation B).space (stageTest B i)).1
      ((situation B).space (stageTest B i)).2 (fibreChart B i) ≃+*
      FibreRing i.poly :=
  (Scheme.ΓSpecIso (uR.{u} (FibreRing i.poly))).commRingCatIsoToRingEquiv.trans
    ULift.ringEquiv

/-- The ring isomorphism `𝒪(T_g) ≅ ℚ[t]_g`. -/
def stageRingEquiv (i : Stage.{u}) :
    Γ(chartScheme (idChart B _ _ (stageObj B i)), ⊤) ≃+* StageRing i.poly :=
  (Scheme.ΓSpecIso (uR.{u} (StageRing i.poly))).commRingCatIsoToRingEquiv.trans
    ULift.ringEquiv

/-- The ring isomorphisms of the chart and of the stage are compatible with `ℚ[t]_g → R_g`. -/
theorem fibreChartRingEquiv_appTop (i : Stage.{u})
    (c : Γ(chartScheme (idChart B _ _ (stageObj B i)), ⊤)) :
    fibreChartRingEquiv B i
        (((BigFppfOver.toScheme B _ _).map (fibreToStage B i)).appTop.hom c) =
      algebraMap (StageRing i.poly) (FibreRing i.poly) (stageRingEquiv B i c) :=
  congrArg (fun k => (ULift.down (k.hom c) : FibreRing i.poly))
    (Scheme.ΓSpecIso_naturality (uHom.{u} (algebraMap (StageRing i.poly) (FibreRing i.poly))))

/-- **No finitely presented quotient at a stage pulls back to the identity quotient over `T`.** -/
theorem quotientPullback_ne_bot (i : Stage.{u})
    (K : Subobject ((situation B).baseChangeModule (stageTest B i)))
    (hK : K ∈ (situation B).finitePresentationQuotients (stageTest B i)) :
    (situation B).quotientPullback (stageConeπ B i) K ≠ zeroSubobject _ := by
  let D := situation B
  let T := stageTest B i
  let U := fibreChart B i
  have hqc : (D.quotientModule T K).IsQuasicoherentOnSite := hK.1.1
  have hU : IsAffine (chartScheme U) := inferInstanceAs (IsAffine (Spec _))
  have hV : IsAffine (chartScheme (idChart B _ _ (stageObj B i))) :=
    inferInstanceAs (IsAffine (Spec _))
  have hflat := flat_sections_of_isFlatOver_chartDiagram _ _ _ (D.projection T)
    (D.quotientModule T K) hqc hK.1.2 (fibreChartDiagram B i) hU hV
  have hfp := module_finitePresentation_sections_of_isFinitePresentationOnSite
    (D.quotientModule T K) hqc hK.2 U hU
  let e := modulePullbackUnitIso B _ _ (D.sourceProjection T)
  let q := e.inv ≫ D.quotientProjection T K
  have hunit : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B _ _ (D.space T).1 (D.space T).2).O)).IsQuasicoherentOnSite :=
    have : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B _ _ (D.space T).1
          (D.space T).2).O)).IsFinitePresentationOnSite :=
      SheafOfModules.isFinitePresentationOnSite_unit
    inferInstance
  have hsurj := surjective_val_app_of_epi_of_isQuasicoherentOnSite q
    (@epi_comp _ _ _ _ _ e.inv (IsIso.epi_of_iso _) _ (D.epi_quotientProjection T K)) hunit hqc U hU
  by_cases h1 : q.val.app (op U)
      (1 : chartRing B baseScheme (contains_baseScheme B) (D.space T).1 (D.space T).2 U) = 0
  · have hq0 := eq_zero_of_unit_app_one_eq_zero q U (nonempty_hom_fibreChart B i) h1
    have hπ : D.quotientProjection T K = 0 := by
      have : D.quotientProjection T K = e.hom ≫ q := (Iso.hom_inv_id_assoc e _).symm
      rw [this, hq0]
      exact Limits.comp_zero
    exact quotientPullback_ne_bot_of_isZero B i K (IsZero.of_epi_eq_zero _ hπ)
  · exact (false_of_flat_of_finitePresentation i.ne_zero
      (A := Γ(chartScheme (idChart B _ _ (stageObj B i)), ⊤))
      (R := chartRing B baseScheme (contains_baseScheme B) (D.space T).1 (D.space T).2 U)
      ((BigFppfOver.toScheme B _ _).map (fibreToStage B i)).appTop.hom (stageRingEquiv B i)
      (fibreChartRingEquiv B i) (fibreChartRingEquiv_appTop B i) _ hflat hfp
      (q.val.app (op U)).hom hsurj h1).elim

end AlgebraicGeometry.QuotientFunctorCounterexample

namespace AlgebraicGeometry.Space.QuotientSituation

open QuotientFunctorCounterexample

attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **Stacks 082Q as written is false.**  It is not true that in Situation 082M, for every big
fppf site, base scheme and quotient situation `f : X ⟶ Y`, `F` with (a) `f` quasi-compact and
quasi-separated and (b) `F` of finite presentation, the functor `Q^{fp}_{F/X/Y}` is limit
preserving.

The witness is `X = Spec ℚ[t][y_a : a ∈ ℚ]/((t - a) y_a)` over `Y = Spec ℚ[t]` with `F = 𝒪_X`,
along the limit `Spec ℚ(t) = lim Spec ℚ[t]_g`: the identity quotient over `Spec ℚ(t)` comes from
no stage.  The statement holds once `f` is also locally of finite presentation, which is
`finitePresentationQuotientsFunctor_limitPreserving_of_isLocallyOfFinitePresentation`. -/
theorem not_forall_finitePresentationQuotientsFunctor_limitPreserving :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (D : QuotientSituation B S hS),
        IsQuasiCompact B S hS D.f.hom → IsQuasiSeparated B S hS D.f.hom →
        D.F.IsFinitePresentationOnSite →
        LimitPreserving.{u, u + 1, u, u} D.testScheme D.finitePresentationQuotientsFunctor := by
  intro h
  obtain ⟨B, -⟩ := BigFppfSite.exists_contains (Spec (.of (ULift.{u} ℚ)))
  have hqc : IsQuasiCompact B _ _ (situation B).f.hom :=
    isQuasiCompact_of_presheaf_quasiCompact B _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B _ _ @QuasiCompact (sourceHom B)).2
        (inferInstanceAs (QuasiCompact (Spec.map _))))
  have hqs : IsQuasiSeparated B _ _ (situation B).f.hom :=
    isQuasiSeparated_of_isSeparated B _ _
      (isSeparated_yoneda_map_of_isAffine B _ _ (sourceHom B)
        (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))))
  obtain ⟨hcol⟩ := h B _ _ (situation B) hqc hqs SheafOfModules.isFinitePresentationOnSite_unit
    QuotientFunctorCounterexample.Stage.{u} (stageDiagram B) (stageCone B) (isLimitStageCone B)
    (fun _ => inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _)))
  obtain ⟨j, K, hK⟩ := Types.jointly_surjective_of_isColimit hcol
    (⟨zeroSubobject _, bot_mem_finitePresentationQuotients B⟩ :
      (situation B).finitePresentationQuotientsFunctor.obj (op (genericTest B)))
  exact quotientPullback_ne_bot B j.unop K.1 K.2 (congrArg Subtype.val hK)

end AlgebraicGeometry.Space.QuotientSituation
