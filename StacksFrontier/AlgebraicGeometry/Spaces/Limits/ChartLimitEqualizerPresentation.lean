module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEtaleChart

/-!
# The equalizer presentation of Stacks 07SI at the limit

Let `X` be the limit of a limit situation and let `U = lim Uᵢ` be the limit of a chart system of
the chosen stage, with relation system `R = lim Rᵢ`. Then `U` is an étale chart of `X`, `R` is
`U ×_X U`, and the global sections of the structure sheaf of `X` are the global functions on `U`
equalized by the two maps `R ⟶ U` (Stacks 03M8).

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.limitEtaleChart`: the limit of a chart system, as an
  object of the small étale site of the limit algebraic space.
* `AlgebraicGeometry.Space.LimitSituation.limitEtaleChartMap`: the induced map of limit charts, as
  a morphism of that site.
* `AlgebraicGeometry.Space.LimitSituation.limitSectionsEquivUnit`: the group `Γ(X, ℱ)` of
  Stacks 07SI at structure-sheaf coefficients is the ring of global regular functions on the
  limit.
* `AlgebraicGeometry.Space.LimitSituation.limitSectionsEquivEqualizer`: Stacks 03M8 for the
  structure sheaf of the limit.
* `AlgebraicGeometry.Space.LimitSituation.chartLimitEqualizerPresentation`: the equalizer
  presentation of `Γ(X, ℱ)` over the limit of the chart system of the situation.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.toScheme_map_inducedMap` and
  `AlgebraicGeometry.Space.LimitSituation.appTopHomLimit_limitEtaleChartMap`: restriction along
  the induced map of limit charts is the restriction map `AlgebraicGeometry.appTopHomLimit` at the
  limit.
* `AlgebraicGeometry.Space.LimitSituation.isPullback_comparisonFunctor_limitEtaleChartMap`: the
  limit of the relation system is `U ×_X U`.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_naturality_of_unit`: at
  structure-sheaf coefficients, the sections of the limit are the colimit of the sections at the
  stages, given the naturality of the two equalizer presentations.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SG](https://stacks.math.columbia.edu/tag/07SG)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)

/-! ### The limit of a chart system in the small étale site of the limit -/

section Chart

variable {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (L : AffineChartSystem.LimitBridge C)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))

/-- The limit of a chart system, as an object of the small étale site of the limit algebraic
space. -/
noncomputable def limitEtaleChart : SmallEtale B S hS X :=
  ⟨CostructuredArrow.mk (A.limitChartToSpace C L), A.isEtaleChart_limitChartToSpace C L hf₀⟩

/-- The scheme of the limit chart is the vertex of the limiting cone of the reindexed diagram of
schemes. -/
theorem toScheme_limitEtaleChart :
    (BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS X).obj (A.limitEtaleChart C L hf₀))
      = (stagesSchemeCone A C L).pt :=
  rfl

/-- The limit chart is surjective on points as soon as the chart of the chosen stage is. -/
theorem isSurjective_limitEtaleChart (hsurj : IsSurjective B S hS f₀) :
    IsSurjective B S hS (A.limitEtaleChart C L hf₀).1.hom :=
  A.isSurjective_limitChartToSpace C L hsurj

end Chart

/-! ### The induced map of limit charts -/

section Relation

variable {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ A.system.obj (op A.base)}
  {τ υ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (LC : AffineChartSystem.LimitBridge C)
  (E : AffineChartSystem B S hS (op A.base) A.system R₀ g₀)
  (LE : AffineChartSystem.LimitBridge E)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
  (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))

/-- The induced map of limit charts is a morphism over the limit algebraic space. -/
theorem yoneda_map_inducedMap_comp_limitChartToSpace (hτ : τ ≫ f₀ = g₀) :
    yoneda.map (AffineChartSystem.LimitBridge.inducedMap LC LE hτ) ≫ A.limitChartToSpace C LC
      = A.limitChartToSpace E LE := by
  rw [AffineChartSystem.LimitBridge.yoneda_map_inducedMap]
  show AffineChartSystem.LimitBridge.inducedPresheafMap LC LE hτ ≫ LC.toLimit ≫ A.limitIso.hom
      = LE.toLimit ≫ A.limitIso.hom
  rw [← Category.assoc, AffineChartSystem.LimitBridge.inducedPresheafMap_comp_toLimit]

/-- The induced map of limit charts, as a morphism of the small étale site of the limit. -/
noncomputable def limitEtaleChartMap (hτ : τ ≫ f₀ = g₀) :
    A.limitEtaleChart E LE hg₀ ⟶ A.limitEtaleChart C LC hf₀ :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (AffineChartSystem.LimitBridge.inducedMap LC LE hτ)
    (A.yoneda_map_inducedMap_comp_limitChartToSpace C LC E LE hτ))

/-- The morphism of schemes underlying the induced map of limit charts is the comparison map of
the two limiting cones. -/
theorem toScheme_map_inducedMap (hτ : τ ≫ f₀ = g₀) :
    (BigFppfOver.toScheme B S hS).map (AffineChartSystem.LimitBridge.inducedMap LC LE hτ)
      = (isLimit_stagesSchemeCone A C LC).map (stagesSchemeCone A E LE)
          (stagesSchemeHom A C E hτ) :=
  (isLimit_stagesSchemeCone A C LC).hom_ext fun b =>
    (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      ((congrArg (BigFppfOver.toScheme B S hS).map
            (AffineChartSystem.LimitBridge.inducedMap_comp_π LC LE hτ
              ((stagesOverEquivalence A).functor.obj b))).trans
        ((BigFppfOver.toScheme B S hS).map_comp _ _))).trans
      (IsLimit.map_π (stagesSchemeCone A E LE) (isLimit_stagesSchemeCone A C LC)
        (stagesSchemeHom A C E hτ) b).symm

/-- Restriction along the induced map of limit charts is the restriction map at the limit. -/
theorem appTopHomLimit_limitEtaleChartMap (hτ : τ ≫ f₀ = g₀)
    (a : Γ((stagesSchemeCone A C LC).pt, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X).map
            (A.limitEtaleChartMap C LC E LE hf₀ hg₀ hτ))).appTop.hom a
      = appTopHomLimit (stagesSchemeHom A C E hτ) (isLimit_stagesSchemeCone A C LC)
          (stagesSchemeCone A E LE) a :=
  congrArg (fun φ => (Scheme.Hom.appTop φ).hom a) (A.toScheme_map_inducedMap C LC E LE hτ)

/-- The limit of the relation system is the self fibre product of the limit of the chart system,
as a cartesian square of presheaves over the limit algebraic space. -/
theorem isPullback_yoneda_inducedMap_limitChartToSpace (hτ : τ ≫ f₀ = g₀) (hυ : υ ≫ f₀ = g₀)
    (hpb : IsPullback τ υ f₀ f₀) :
    IsPullback (yoneda.map (AffineChartSystem.LimitBridge.inducedMap LC LE hτ))
      (yoneda.map (AffineChartSystem.LimitBridge.inducedMap LC LE hυ))
      (A.limitChartToSpace C LC) (A.limitChartToSpace C LC) :=
  (AffineChartSystem.LimitBridge.isPullback_yoneda_inducedMap LC LE hτ hυ hpb).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) A.limitIso.symm (by simp) (by simp)
    (by simp [limitChartToSpace]) (by simp [limitChartToSpace])

/-- The two induced maps of limit charts exhibit the comparison image of `R = lim Rᵢ` as the fibre
product of the comparison image of `U = lim Uᵢ` with itself over the terminal object of the
spaces-étale site of the limit, that is as `U ×_X U`. -/
theorem isPullback_comparisonFunctor_limitEtaleChartMap (hX : IsAlgebraicSpace B S hS X)
    (hτ : τ ≫ f₀ = g₀) (hυ : υ ≫ f₀ = g₀) (hpb : IsPullback τ υ f₀ f₀) :
    IsPullback
      ((comparisonFunctor B S hS (A.limitSpace hX)).map
        (A.limitEtaleChartMap C LC E LE hf₀ hg₀ hτ))
      ((comparisonFunctor B S hS (A.limitSpace hX)).map
        (A.limitEtaleChartMap C LC E LE hf₀ hg₀ hυ))
      ((SpacesEtale.isTerminal_idObj B S hS (A.limitSpace hX)).from
        ((comparisonFunctor B S hS (A.limitSpace hX)).obj (A.limitEtaleChart C LC hf₀)))
      ((SpacesEtale.isTerminal_idObj B S hS (A.limitSpace hX)).from
        ((comparisonFunctor B S hS (A.limitSpace hX)).obj (A.limitEtaleChart C LC hf₀))) := by
  refine IsPullback.of_map_of_faithful
    (SpacesEtale.toSpaces B S hS (A.limitSpace hX) ⋙ ObjectProperty.ι _) ?_
  have hfrom : (SpacesEtale.toSpaces B S hS (A.limitSpace hX) ⋙ ObjectProperty.ι _).map
        ((SpacesEtale.isTerminal_idObj B S hS (A.limitSpace hX)).from
          ((comparisonFunctor B S hS (A.limitSpace hX)).obj (A.limitEtaleChart C LC hf₀)))
      = A.limitChartToSpace C LC :=
    congrArg (fun k => k.hom) (SpacesEtale.toSpaces_map_from_idObj B S hS
      ((comparisonFunctor B S hS (A.limitSpace hX)).obj (A.limitEtaleChart C LC hf₀)))
  rw [hfrom]
  exact A.isPullback_yoneda_inducedMap_limitChartToSpace C LC E LE hτ hυ hpb

end Relation

/-! ### The group of sections at the limit, at structure-sheaf coefficients -/

/-- Taking the coefficients `ℱ₀` of Stacks 07SI to be the structure sheaf of the chosen stage, the
inverse image `ℱ = f_0^*ℱ₀` to the limit is the structure sheaf of the limit. -/
noncomputable def limitModuleUnitIso (hX : IsAlgebraicSpace B S hS X) :
    SheafOfModules.unit (structureRingSheaf B S hS (A.limitSpace hX)) ≅
      A.limitModule (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX :=
  (modulePullbackUnitIso B S hS (A.projection hX A.base)).symm

/-- The group `Γ(X, ℱ)` of Stacks 07SI at structure-sheaf coefficients is the ring of global
regular functions on the limit. -/
noncomputable def limitSectionsEquivUnit (hX : IsAlgebraicSpace B S hS X) :
    A.limitSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX ≃
      (SheafOfModules.unit (structureRingSheaf B S hS (A.limitSpace hX))).sections :=
  ((SheafOfModules.sectionsFunctor (structureRingSheaf B S hS (A.limitSpace hX))).mapIso
    (A.limitModuleUnitIso hX)).toEquiv.symm

/-- At each étale chart of the limit, the identification of `Γ(X, ℱ)` with `Γ(X, 𝒪_X)` applies the
component there of the inverse of `AlgebraicGeometry.Space.LimitSituation.limitModuleUnitIso`. -/
theorem limitSectionsEquivUnit_val (hX : IsAlgebraicSpace B S hS X)
    (σ : A.limitSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX)
    (W : (SmallEtale B S hS (A.limitSpace hX).obj)ᵒᵖ) :
    (A.limitSectionsEquivUnit hX σ).val W
      = (A.limitModuleUnitIso hX).inv.val.app W (σ.val W) :=
  rfl

/-! ### The equalizer presentation of Stacks 03M8 at the limit -/

section Presentation

variable (hX : IsAlgebraicSpace B S hS X)

/-- Let `X` be the limit of a limit situation, `U` an étale chart of `X` surjective on points and
`R` a relation chart exhibiting `U ×_X U` with its two projections `t, s`. With the coefficients
`ℱ₀` of Stacks 07SI taken to be the structure sheaf of the chosen stage,

`Γ(X, ℱ) ≃ {a : Γ(U, 𝒪) // t^*a = s^*a}`. -/
noncomputable def limitSectionsEquivEqualizer {U R : SmallEtale B S hS X}
    (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS (A.limitSpace hX)).map t)
      ((comparisonFunctor B S hS (A.limitSpace hX)).map s)
      ((SpacesEtale.isTerminal_idObj B S hS (A.limitSpace hX)).from
        ((comparisonFunctor B S hS (A.limitSpace hX)).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS (A.limitSpace hX)).from
        ((comparisonFunctor B S hS (A.limitSpace hX)).obj U))) :
    A.limitSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX ≃
      {a : (Γ((BigFppfOver.toScheme B S hS).obj
                ((SmallEtale.toOver B S hS X).obj U), ⊤) : Type u) //
        ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X).map t)).appTop.hom a
          = ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X).map s)).appTop.hom a} :=
  (A.limitSectionsEquivUnit hX).trans
    (structureSectionsEquivEqualizer B S hS (A.limitSpace hX) hU hR)

/-- The equalizer presentation at the limit carries a section of `Γ(X, ℱ)` to its own member at
the chart `U`, read through the component at `U` of the identification of `ℱ` with the structure
sheaf of the limit. -/
theorem limitSectionsEquivEqualizer_apply_val {U R : SmallEtale B S hS X}
    (hU : IsSurjective B S hS U.1.hom) {t s : R ⟶ U}
    (hR : IsPullback ((comparisonFunctor B S hS (A.limitSpace hX)).map t)
      ((comparisonFunctor B S hS (A.limitSpace hX)).map s)
      ((SpacesEtale.isTerminal_idObj B S hS (A.limitSpace hX)).from
        ((comparisonFunctor B S hS (A.limitSpace hX)).obj U))
      ((SpacesEtale.isTerminal_idObj B S hS (A.limitSpace hX)).from
        ((comparisonFunctor B S hS (A.limitSpace hX)).obj U)))
    (σ : A.limitSections
      (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX) :
    (A.limitSectionsEquivEqualizer hX hU hR σ).1
      = (A.limitModuleUnitIso hX).inv.val.app (op U) (σ.val (op U)) :=
  structureSectionsEquivEqualizer_apply_val B S hS (A.limitSpace hX) hU hR _

end Presentation

/-! ### The equalizer presentation over the limit of a chart system -/

section Generic

variable {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ A.system.obj (op A.base)}
  {τ υ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (LC : AffineChartSystem.LimitBridge C)
  (E : AffineChartSystem B S hS (op A.base) A.system R₀ g₀)
  (LE : AffineChartSystem.LimitBridge E)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
  (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))

/-- With the coefficients `ℱ₀` of Stacks 07SI taken to be the structure sheaf of the chosen stage,
the group `Γ(X, ℱ)` is in bijection with the global functions on the limit chart `U = lim Uᵢ`
equalized by the two maps the limit of the relation system induces:

`Γ(X, ℱ) ≃ {x : Γ(U, 𝒪) // p'^*x = q'^*x}`. -/
noncomputable def limitChartEqualizerPresentation (hX : IsAlgebraicSpace B S hS X)
    (hsurj : IsSurjective B S hS f₀) (hτ : τ ≫ f₀ = g₀) (hυ : υ ≫ f₀ = g₀)
    (hpb : IsPullback τ υ f₀ f₀) :
    A.limitSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX ≃
      {x : (Γ((stagesSchemeCone A C LC).pt, ⊤) : Type u) //
        appTopHomLimit (stagesSchemeHom A C E hτ) (isLimit_stagesSchemeCone A C LC)
              (stagesSchemeCone A E LE) x
          = appTopHomLimit (stagesSchemeHom A C E hυ) (isLimit_stagesSchemeCone A C LC)
              (stagesSchemeCone A E LE) x} :=
  (A.limitSectionsEquivEqualizer hX (A.isSurjective_limitEtaleChart C LC hf₀ hsurj)
        (A.isPullback_comparisonFunctor_limitEtaleChartMap C LC E LE hf₀ hg₀ hX
          hτ hυ hpb)).trans
    (Equiv.subtypeEquivRight fun a => by
      simp only [A.appTopHomLimit_limitEtaleChartMap C LC E LE hf₀ hg₀ hτ a,
        A.appTopHomLimit_limitEtaleChartMap C LC E LE hf₀ hg₀ hυ a]
      exact Iff.rfl)

end Generic

/-! ### The hypothesis `eT` of the consumer, supplied -/

section Consumer

variable {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}

/-- Let `U₀ ⟶ X₀` be an affine étale chart of the chosen stage of a limit situation, surjective on
points, and let `t` and `yoneda s` be the two projections of its relation `R₀ = U₀ ×_{X₀} U₀`.
With the coefficients `ℱ₀` of Stacks 07SI taken to be the structure sheaf of the chosen stage, the
group `Γ(X, ℱ)` is in bijection with the equalizer of the two restriction maps `Γ(U, ⊤) → Γ(R, ⊤)`
at the limit. -/
noncomputable def chartLimitEqualizerPresentation (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀) :
    A.limitSections (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX ≃
      {x : (Γ((A.chartStagesCone U₀ f₀ hI).pt, ⊤) : Type u) //
        A.chartStagesRestrictionLimit (τ := t) (f₀ := f₀) rfl hI x
          = A.chartStagesRestrictionLimit (τ := yoneda.map s) hpb.w.symm hI x} :=
  A.limitChartEqualizerPresentation (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
    (A.chartSystem R₀ (t ≫ f₀)) (A.chartLimitBridge R₀ (t ≫ f₀) hI) hf₀
    (isEtaleChart_comp_of_isPullback hf₀ hpb) hX hsurj rfl hpb.w.symm hpb

/-- At structure-sheaf coefficients, the global sections of the limit are the filtered colimit of
the global sections at the stages, provided the stagewise equalizer presentations are natural in
the stage (`he`) and compatible with the equalizer presentation at the limit (`heT`). -/
theorem isSectionsColimit_of_naturality_of_unit (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (σ : A.stageSections
        (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i),
      (A.chartEqualizerPresentation hf₀ hsurj hpb j
          (A.stageTransition (SheafOfModules.unit
            (structureRingSheaf B S hS (A.stage A.base))) i j h σ)).1
        = ((A.chartStagesDiagram U₀ f₀).map (homOfLE h).op).appTop.hom
            (A.chartEqualizerPresentation hf₀ hsurj hpb i σ).1)
    (heT : ∀ (i : A.Stages) (σ : A.stageSections
        (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) i),
      (A.chartLimitEqualizerPresentation hX hI hf₀ hsurj hpb
          (A.stageProjection (SheafOfModules.unit
            (structureRingSheaf B S hS (A.stage A.base))) hX i σ)).1
        = ((A.chartStagesCone U₀ f₀ hI).π.app (op i)).appTop.hom
            (A.chartEqualizerPresentation hf₀ hsurj hpb i σ).1) :
    A.IsSectionsColimit
      (SheafOfModules.unit (structureRingSheaf B S hS (A.stage A.base))) hX :=
  A.isSectionsColimit_of_limitEqualizerPresentation_of_unit hX hI hf₀ hsurj hpb
    (A.chartLimitEqualizerPresentation hX hI hf₀ hsurj hpb) he heT

end Consumer

end AlgebraicGeometry.Space.LimitSituation

end
