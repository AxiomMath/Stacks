module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAmbientToBase

/-!
# Étale charts of the ambient space of a square-zero extension are thickened charts

Let `i : X ⟶ X'` be the morphism of `X` to the ambient space of a square-zero extension built
from a charted presentation of `X`. For an étale chart `V` of the ambient space factoring étale
through the thickened presenting chart, the thickening of the base change of `V` to `X` is
identified with `V`, independently of the factorization and naturally in `V`.

## Main definitions

* `ChartFactor`: A factorization of an étale chart of the ambient space through the thickened
  presenting chart, étale over it.
* `ChartFactor.thickenHom`: The morphism from the thickened base-changed chart to the chart.

## Main results

* `ChartFactor.isIso_thickenHom`: `ChartFactor.thickenHom` is an isomorphism.
* `ChartFactor.thickenHom_eq`: `ChartFactor.thickenHom` does not depend on the factorization.
* `ChartFactor.thickenHom_naturality`: `ChartFactor.thickenHom` is natural in the chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- **Morphisms of étale schemes over a thickening lift from the reduction** ([Stacks Project,
Tag 039R], fullness): given étale `A ⟶ T` and `B ⟶ T` and a morphism from the base change of `A`
to the reduction into `B` lying over the base change of `B`, there is a morphism `A ⟶ B` over `T`
restricting to it. -/
theorem exists_lift_of_isPullback_etale {T₀ T A B C : Scheme.{u}} (i : T₀ ⟶ T)
    [AlgebraicGeometry.IsClosedImmersion i] (hi : Function.Surjective i.base) (p : A ⟶ T)
    (q : B ⟶ T) [Etale p] [Etale q] (c₁ : C ⟶ A) (c₂ : C ⟶ T₀) (hA : IsPullback c₁ c₂ p i)
    (d : C ⟶ B) (hB : IsPullback d c₂ q i) : ∃ ψ : A ⟶ B, ψ ≫ q = p ∧ c₁ ≫ ψ = d := by
  have : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : T.Etale ⥤ T₀.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ i
  have : F.IsEquivalence :=
    Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion i hi
  let A' : T.Etale := MorphismProperty.Over.mk ⊤ p ‹_›
  let B' : T.Etale := MorphismProperty.Over.mk ⊤ q ‹_›
  let m : F.obj A' ⟶ F.obj B' :=
    MorphismProperty.Over.homMk (hA.isoPullback.inv ≫ hB.isoPullback.hom) (by
      change (hA.isoPullback.inv ≫ hB.isoPullback.hom) ≫ pullback.snd q i = pullback.snd p i
      rw [Category.assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_inv_snd])
  let ψ' : A' ⟶ B' := F.preimage m
  have hm : F.map ψ' = m := F.map_preimage m
  have hfst : (F.map ψ').left ≫ pullback.fst q i = pullback.fst p i ≫ ψ'.left :=
    pullback.lift_fst _ _ _
  refine ⟨ψ'.left, ψ'.w, ?_⟩
  rw [hm] at hfst
  change (hA.isoPullback.inv ≫ hB.isoPullback.hom) ≫ pullback.fst q i =
    pullback.fst p i ≫ ψ'.left at hfst
  have e1 : c₁ = hA.isoPullback.hom ≫ pullback.fst p i := (IsPullback.isoPullback_hom_fst hA).symm
  have e2 : d = hB.isoPullback.hom ≫ pullback.fst q i := (IsPullback.isoPullback_hom_fst hB).symm
  rw [e1, e2]
  refine (Category.assoc _ _ _).trans ((congrArg (hA.isoPullback.hom ≫ ·) hfst.symm).trans ?_)
  exact (congrArg (hA.isoPullback.hom ≫ ·) (Category.assoc _ _ _)).trans
    (Iso.hom_inv_id_assoc _ _)

/-- **Morphisms into a formally unramified scheme agree as soon as they agree on a first-order
thickening of the source.** -/
theorem eq_of_comp_eq_of_isFirstOrderThickening {Z₀ Z T M : Scheme.{u}} (z : Z₀ ⟶ Z)
    (hz : Stacks.Thickenings.IsFirstOrderThickening z) (e : T ⟶ M) (he : FormallyUnramified e)
    {a b : Z ⟶ T} (h₁ : z ≫ a = z ≫ b) (h₂ : a ≫ e = b ≫ e) : a = b := by
  have := hz.1
  exact FormallyUnramified.hom_ext z ⟨2, hz.2⟩ e h₁ h₂

namespace Space

namespace SquareZeroExtension

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme
attribute [local instance] hasSheafify_bigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {E : SquareZeroExtension B S hS f}
  {C : ChartedPresentation B S hS f}
  {hcU : B.Contains (chartThickening B S hS E (presentationChart C.P))}
  {hcR : B.Contains (chartThickening B S hS E (presentationRelationChart C.P))}
  (i : X ⟶ ambient E C hcU hcR)
  (hi : C.P.toSpace ≫ i.hom = yoneda.map (incU E C hcU) ≫ ambQuot E C hcU hcR)

include hi in
/-- `X ⟶ X'` is representable. -/
theorem ambRep : yoneda.relativelyRepresentable i.hom :=
  (isThickeningHom_ambientMap i hi).isClosedImmersion.rep

/-- The base change to `X` of an étale chart of the ambient space. -/
abbrev chartX (V : SmallEtale B S hS (ambient E C hcU hcR).1) : SmallEtale B S hS X.1 :=
  (smallBaseChange B S hS i (ambRep i hi)).obj V

/-- The cartesian projection of the base-changed chart to the chart. -/
abbrev chartXProj (V : SmallEtale B S hS (ambient E C hcU hcR).1) :
    (chartX i hi V).1.left ⟶ V.1.left :=
  (ambRep i hi).snd V.1.hom

/-- A factorization of an étale chart of the ambient space through the thickened presenting
chart. -/
structure ChartFactor (V : SmallEtale B S hS (ambient E C hcU hcR).1) where
  /-- The factoring morphism. -/
  v : V.1.left ⟶ ambU E C hcU
  /-- It factors the structure morphism of the chart. -/
  fac : yoneda.map v ≫ ambQuot E C hcU hcR = V.1.hom
  /-- It is étale. -/
  etale : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map v)

variable {i hi}

/-- The morphism of the base-changed chart to the presenting chart of `X` induced by a
factorization. -/
def ChartFactor.lift {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F : ChartFactor V) :
    (chartX i hi V).1.left ⟶ C.P.U :=
  yoneda.preimage ((isPullback_chart_ambient i hi).lift
    (yoneda.map (chartXProj i hi V ≫ F.v)) ((ambRep i hi).fst V.1.hom) (by
      rw [Functor.map_comp, Category.assoc, F.fac]
      exact ((ambRep i hi).isPullback V.1.hom).w.symm))

/-- The lift followed by the inclusion of the presenting chart is the cartesian projection
followed by the factoring morphism. -/
theorem ChartFactor.lift_incU {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F : ChartFactor V) : F.lift (hi := hi) ≫ incU E C hcU = chartXProj i hi V ≫ F.v := by
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, ChartFactor.lift, Functor.map_preimage]
  exact IsPullback.lift_fst _ _ _ _

/-- The lift lies over the structure morphism of the base-changed chart to `X`. -/
theorem ChartFactor.lift_toSpace {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F : ChartFactor V) : yoneda.map (F.lift (hi := hi)) ≫ C.P.toSpace = (chartX i hi V).1.hom := by
  rw [ChartFactor.lift, Functor.map_preimage]
  exact IsPullback.lift_snd _ _ _ _

/-- The factorization as a morphism of étale charts of `X`. -/
def ChartFactor.hom {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F : ChartFactor V) :
    chartX i hi V ⟶ presentationChart C.P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (F.lift (hi := hi)) (F.lift_toSpace (hi := hi)))

/-- **The base-changed chart is the base change of the chart along the thickening of the
presenting chart.** -/
theorem ChartFactor.isPullback {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F : ChartFactor V) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (chartXProj i hi V))
      ((BigFppfOver.toScheme B S hS).map (F.lift (hi := hi)))
      ((BigFppfOver.toScheme B S hS).map F.v)
      (chartImmersion B S hS E (presentationChart C.P)) := by
  have hY : IsPullback (yoneda.map (chartXProj i hi V)) (yoneda.map (F.lift (hi := hi)))
      (yoneda.map F.v) (yoneda.map (incU E C hcU)) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_chart_ambient i hi)
    · rw [F.lift_toSpace, F.fac]
      exact ((ambRep i hi).isPullback V.1.hom).flip
    · rw [← Functor.map_comp, ← Functor.map_comp, F.lift_incU]
  exact (IsPullback.of_map_of_faithful yoneda hY).map (BigFppfOver.toScheme B S hS)

/-- The thickened base-changed chart admits a morphism to the chart, over the thickened
presenting chart and extending the cartesian projection. -/
theorem exists_thickenHom {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F : ChartFactor V) :
    ∃ ψ : chartThickening B S hS E (chartX i hi V) ⟶ (BigFppfOver.toScheme B S hS).obj V.1.left,
      ψ ≫ (BigFppfOver.toScheme B S hS).map F.v = chartThickeningMap B S hS E (F.hom (hi := hi)) ∧
      chartImmersion B S hS E (chartX i hi V) ≫ ψ =
        (BigFppfOver.toScheme B S hS).map (chartXProj i hi V) := by
  have hFe : _root_.AlgebraicGeometry.Etale (show (BigFppfOver.toScheme B S hS).obj V.1.left ⟶
      chartThickening B S hS E (presentationChart C.P) from
        (BigFppfOver.toScheme B S hS).map F.v) := F.etale
  have := etale_chartThickeningMap B S hS E (F.hom (hi := hi))
  have := (isFirstOrderThickening_chartImmersion B S hS E (presentationChart C.P)).1
  exact exists_lift_of_isPullback_etale (chartImmersion B S hS E (presentationChart C.P))
    (isFirstOrderThickening_chartImmersion B S hS E (presentationChart C.P)).isThickening.2
    (chartThickeningMap B S hS E (F.hom (hi := hi))) ((BigFppfOver.toScheme B S hS).map F.v)
    (chartImmersion B S hS E (chartX i hi V)) (chartSchemeMap (F.hom (hi := hi)))
    (isPullback_chartImmersion_chartThickeningMap B S hS E (F.hom (hi := hi)))
    ((BigFppfOver.toScheme B S hS).map (chartXProj i hi V)) (F.isPullback (hi := hi))

/-- **The thickened base-changed chart maps to the chart**, over the thickened presenting chart
and extending the cartesian projection. -/
def ChartFactor.thickenHom {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F : ChartFactor V) :
    chartThickening B S hS E (chartX i hi V) ⟶ (BigFppfOver.toScheme B S hS).obj V.1.left :=
  (exists_thickenHom F).choose

/-- `ChartFactor.thickenHom` lies over the thickening of `ChartFactor.hom`. -/
theorem ChartFactor.thickenHom_comp {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F : ChartFactor V) :
    F.thickenHom (hi := hi) ≫ (BigFppfOver.toScheme B S hS).map F.v =
      chartThickeningMap B S hS E (F.hom (hi := hi)) :=
  (exists_thickenHom F).choose_spec.1

/-- `ChartFactor.thickenHom` restricts to the cartesian projection on the base-changed chart. -/
theorem ChartFactor.immersion_thickenHom {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F : ChartFactor V) :
    chartImmersion B S hS E (chartX i hi V) ≫ F.thickenHom (hi := hi) =
      (BigFppfOver.toScheme B S hS).map (chartXProj i hi V) :=
  (exists_thickenHom F).choose_spec.2

/-- **The thickened base-changed chart is the chart.** -/
instance ChartFactor.isIso_thickenHom {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F : ChartFactor V) : IsIso (F.thickenHom (hi := hi)) := by
  have hFe : _root_.AlgebraicGeometry.Etale (show (BigFppfOver.toScheme B S hS).obj V.1.left ⟶
      chartThickening B S hS E (presentationChart C.P) from
        (BigFppfOver.toScheme B S hS).map F.v) := F.etale
  have := etale_chartThickeningMap B S hS E (F.hom (hi := hi))
  have := (isFirstOrderThickening_chartImmersion B S hS E (presentationChart C.P)).1
  refine isIso_of_isPullback_of_isPullback_of_surjective_isClosedImmersion
    (chartImmersion B S hS E (presentationChart C.P))
    (isFirstOrderThickening_chartImmersion B S hS E (presentationChart C.P)).isThickening.2
    (chartThickeningMap B S hS E (F.hom (hi := hi))) ((BigFppfOver.toScheme B S hS).map F.v)
    (F.thickenHom (hi := hi)) F.thickenHom_comp
    (chartImmersion B S hS E (chartX i hi V)) (chartSchemeMap (F.hom (hi := hi)))
    (isPullback_chartImmersion_chartThickeningMap B S hS E (F.hom (hi := hi))) ?_
  rw [F.immersion_thickenHom]
  exact F.isPullback (hi := hi)

/-- The morphism of relation schemes attached to two factorizations of a chart. -/
def relLift {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F F' : ChartFactor V) :
    V.1.left ⟶ ambR E C hcR :=
  yoneda.preimage ((ambQuot_isPullback E C hcU hcR).lift (yoneda.map F.v) (yoneda.map F'.v)
    (F.fac.trans F'.fac.symm))

/-- The target of `relLift F F'` is the factoring morphism of `F`. -/
theorem relLift_target {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F F' : ChartFactor V) :
    relLift F F' ≫ ambTarget E C hcU hcR = F.v :=
  yoneda.map_injective (by
    rw [Functor.map_comp, relLift, Functor.map_preimage]
    exact IsPullback.lift_fst _ _ _ _)

/-- The source of `relLift F F'` is the factoring morphism of `F'`. -/
theorem relLift_source {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F F' : ChartFactor V) :
    relLift F F' ≫ ambSource E C hcU hcR = F'.v :=
  yoneda.map_injective (by
    rw [Functor.map_comp, relLift, Functor.map_preimage]
    exact IsPullback.lift_snd _ _ _ _)

/-- The morphism of the base-changed chart to the relation chart attached to two
factorizations. -/
def relChartLift {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F F' : ChartFactor V) :
    (chartX i hi V).1.left ⟶ C.P.R :=
  yoneda.preimage (C.P.isPullback.lift (yoneda.map (F.lift (hi := hi)))
    (yoneda.map (F'.lift (hi := hi))) ((F.lift_toSpace).trans (F'.lift_toSpace).symm))

/-- The target of `relChartLift F F'` is the lift of `F`. -/
theorem relChartLift_target {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F F' : ChartFactor V) :
    relChartLift (hi := hi) F F' ≫ C.P.target = F.lift (hi := hi) :=
  yoneda.map_injective (by
    rw [Functor.map_comp, relChartLift, Functor.map_preimage]
    exact IsPullback.lift_fst _ _ _ _)

/-- The source of `relChartLift F F'` is the lift of `F'`. -/
theorem relChartLift_source {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F F' : ChartFactor V) :
    relChartLift (hi := hi) F F' ≫ C.P.source = F'.lift (hi := hi) :=
  yoneda.map_injective (by
    rw [Functor.map_comp, relChartLift, Functor.map_preimage]
    exact IsPullback.lift_snd _ _ _ _)

/-- The same, as a morphism of étale charts of `X`. -/
def relChartHom {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F F' : ChartFactor V) :
    chartX i hi V ⟶ presentationRelationChart C.P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (relChartLift (hi := hi) F F') (by
    change yoneda.map (relChartLift (hi := hi) F F') ≫ yoneda.map C.P.source ≫ C.P.toSpace = _
    rw [← Category.assoc, ← Functor.map_comp, relChartLift_source, F'.lift_toSpace]))

/-- The target of `relChartHom F F'` is `F.hom`. -/
theorem relChartHom_target {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F F' : ChartFactor V) :
    relChartHom (hi := hi) F F' ≫ presentationRelationTargetHom C.P = F.hom (hi := hi) :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (relChartLift_target F F'))

/-- The source of `relChartHom F F'` is `F'.hom`. -/
theorem relChartHom_source {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F F' : ChartFactor V) :
    relChartHom (hi := hi) F F' ≫ presentationRelationSourceHom C.P = F'.hom (hi := hi) :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (relChartLift_source F F'))

/-- The cartesian projection followed by `relLift F F'` is `relChartLift F F'` followed by the
inclusion of the relation chart. -/
theorem chartXProj_relLift {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F F' : ChartFactor V) :
    chartXProj i hi V ≫ relLift F F' = relChartLift (hi := hi) F F' ≫ incR E C hcR := by
  refine yoneda.map_injective ((ambQuot_isPullback E C hcU hcR).hom_ext ?_ ?_)
  · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, relLift_target,
      incR_comp_ambTarget, ← Category.assoc, relChartLift_target, F.lift_incU]
  · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, relLift_source,
      incR_comp_ambSource, ← Category.assoc, relChartLift_source, F'.lift_incU]

/-- Morphisms from the thickened base-changed chart to a formally unramified scheme agree if they
agree on the base-changed chart and after composition. -/
private theorem thickening_chartX_hom_ext {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    {T M : Scheme.{u}} (e : T ⟶ M) (he : _root_.AlgebraicGeometry.FormallyUnramified e)
    {a b : chartThickening B S hS E (chartX i hi V) ⟶ T}
    (h₁ : chartImmersion B S hS E (chartX i hi V) ≫ a =
      chartImmersion B S hS E (chartX i hi V) ≫ b)
    (h₂ : a ≫ e = b ≫ e) : a = b :=
  eq_of_comp_eq_of_isFirstOrderThickening (chartImmersion B S hS E (chartX i hi V))
    (isFirstOrderThickening_chartImmersion B S hS E (chartX i hi V)) e he h₁ h₂

/-- **The comparison does not depend on the factorization**: for any other factorization, the
comparison of the first lies over the second. -/
theorem ChartFactor.thickenHom_comp_of {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F F' : ChartFactor V) :
    F.thickenHom (hi := hi) ≫ (BigFppfOver.toScheme B S hS).map F'.v =
      chartThickeningMap B S hS E (F'.hom (hi := hi)) := by
  have hT := etale_chartThickeningMap B S hS E (presentationRelationTargetHom C.P)
  have key : F.thickenHom (hi := hi) ≫ (BigFppfOver.toScheme B S hS).map (relLift F F') =
      chartThickeningMap B S hS E (relChartHom (hi := hi) F F') := by
    refine thickening_chartX_hom_ext (chartThickeningMap B S hS E
      (presentationRelationTargetHom C.P)) inferInstance ?_ ?_
    · refine (Category.assoc _ _ _).symm.trans ?_
      rw [F.immersion_thickenHom]
      refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ?_
      refine (congrArg (BigFppfOver.toScheme B S hS).map (chartXProj_relLift F F')).trans ?_
      refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
      exact (chartImmersion_comp_chartThickeningMap B S hS E (relChartHom (hi := hi) F F')).symm
    · refine (Category.assoc _ _ _).trans ?_
      change F.thickenHom (hi := hi) ≫ (BigFppfOver.toScheme B S hS).map (relLift F F') ≫
          (BigFppfOver.toScheme B S hS).map (ambTarget E C hcU hcR) = _
      rw [← Functor.map_comp, relLift_target, F.thickenHom_comp, ← chartThickeningMap_comp,
        relChartHom_target]
  have e1 : (BigFppfOver.toScheme B S hS).map F'.v =
      (BigFppfOver.toScheme B S hS).map (relLift F F') ≫
        (BigFppfOver.toScheme B S hS).map (ambSource E C hcU hcR) := by
    rw [← Functor.map_comp, relLift_source]
  rw [e1, ← Category.assoc, key]
  change chartThickeningMap B S hS E (relChartHom (hi := hi) F F') ≫
    chartThickeningMap B S hS E (presentationRelationSourceHom C.P) = _
  rw [← chartThickeningMap_comp, relChartHom_source]

/-- The factoring morphism on underlying schemes. -/
abbrev ChartFactor.vS {V : SmallEtale B S hS (ambient E C hcU hcR).1} (F : ChartFactor V) :
    (BigFppfOver.toScheme B S hS).obj V.1.left ⟶ chartThickening B S hS E (presentationChart C.P) :=
  (BigFppfOver.toScheme B S hS).map F.v

/-- The factoring morphism on underlying schemes is étale. -/
instance ChartFactor.etale_vS {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F : ChartFactor V) : _root_.AlgebraicGeometry.Etale F.vS := F.etale

/-- **The comparison of a chart with the thickening of its base change does not depend on the
factorization.** -/
theorem ChartFactor.thickenHom_eq {V : SmallEtale B S hS (ambient E C hcU hcR).1}
    (F F' : ChartFactor V) : F.thickenHom (hi := hi) = F'.thickenHom (hi := hi) :=
  thickening_chartX_hom_ext F'.vS inferInstance
    (F.immersion_thickenHom.trans F'.immersion_thickenHom.symm)
    ((F.thickenHom_comp_of F').trans F'.thickenHom_comp.symm)

/-- A factorization restricted along a morphism of charts. -/
def ChartFactor.precomp {V₁ V₂ : SmallEtale B S hS (ambient E C hcU hcR).1} (g : V₁ ⟶ V₂)
    (F : ChartFactor V₂) : ChartFactor V₁ where
  v := g.hom.left ≫ F.v
  fac := by rw [Functor.map_comp, Category.assoc, F.fac]; exact CostructuredArrow.w g.hom
  etale := by
    have := SmallEtale.etale_map B S hS _ g
    rw [Functor.map_comp]
    exact inferInstanceAs (_root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map g) ≫ F.vS))

/-- The lift of a restricted factorization is the base change of the morphism of charts
followed by the lift of the original factorization. -/
theorem ChartFactor.precomp_lift {V₁ V₂ : SmallEtale B S hS (ambient E C hcU hcR).1}
    (g : V₁ ⟶ V₂) (F : ChartFactor V₂) :
    (F.precomp g).lift (hi := hi) =
      ((smallBaseChange B S hS i (ambRep i hi)).map g).hom.left ≫ F.lift (hi := hi) := by
  refine yoneda.map_injective ((isPullback_chart_ambient i hi).hom_ext ?_ ?_)
  · rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg yoneda.map ?_
    rw [ChartFactor.lift_incU, Category.assoc, ChartFactor.lift_incU, ← Category.assoc,
      smallBaseChange_map_snd]
    exact (Category.assoc _ _ _).symm
  · rw [ChartFactor.lift_toSpace, Functor.map_comp, Category.assoc, ChartFactor.lift_toSpace]
    exact (CostructuredArrow.w ((smallBaseChange B S hS i (ambRep i hi)).map g).hom).symm

/-- `ChartFactor.hom` is natural with respect to restriction along a morphism of charts. -/
theorem ChartFactor.map_hom {V₁ V₂ : SmallEtale B S hS (ambient E C hcU hcR).1} (g : V₁ ⟶ V₂)
    (F : ChartFactor V₂) :
    (smallBaseChange B S hS i (ambRep i hi)).map g ≫ F.hom (hi := hi) =
      (F.precomp g).hom (hi := hi) :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (F.precomp_lift g).symm)

/-- **Naturality of the comparison in the chart.** -/
theorem ChartFactor.thickenHom_naturality {V₁ V₂ : SmallEtale B S hS (ambient E C hcU hcR).1}
    (g : V₁ ⟶ V₂) (F : ChartFactor V₂) :
    chartThickeningMap B S hS E ((smallBaseChange B S hS i (ambRep i hi)).map g) ≫
        F.thickenHom (hi := hi) =
      (F.precomp g).thickenHom (hi := hi) ≫ (BigFppfOver.toScheme B S hS).map g.hom.left := by
  refine thickening_chartX_hom_ext F.vS inferInstance ?_ ?_
  · rw [← Category.assoc, chartImmersion_comp_chartThickeningMap, Category.assoc,
      F.immersion_thickenHom, ← Category.assoc, (F.precomp g).immersion_thickenHom]
    refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ?_
    refine Eq.trans ?_ ((BigFppfOver.toScheme B S hS).map_comp _ _)
    exact congrArg (BigFppfOver.toScheme B S hS).map (smallBaseChange_map_snd B S hS i _ g)
  · refine (Category.assoc _ _ _).trans ?_
    refine ((congrArg (_ ≫ ·) F.thickenHom_comp).trans ?_)
    refine ((chartThickeningMap_comp B S hS E _ _).symm.trans ?_)
    rw [F.map_hom g, ← (F.precomp g).thickenHom_comp, Category.assoc]
    refine congrArg (_ ≫ ·) ?_
    exact (BigFppfOver.toScheme B S hS).map_comp _ _

end SquareZeroExtension

end Space

end AlgebraicGeometry

end
