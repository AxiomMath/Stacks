module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UndeformedTargetLiftChart

/-!
# The action of `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` on the lifts into an undeformed target

Let `X ⊂ X'` be a first order thickening of algebraic spaces over a scheme `S`, let `Y` and `B`
be algebraic spaces with `q : Y ⟶ B` and `p : X' ⟶ B`, and let `a : X ⟶ Y` be a morphism. This
is the situation of [Stacks Project, Tag 061D]: the target `Y = Y'` is not deformed. The lifts
of `a` form the sheaf `AlgebraicGeometry.Space.liftsSubfunctor` on the small étale site of
`X'`, whose sections over a chart `U'` are the morphisms `a' : U' ⟶ Y` over `B` with
`a'|_U = a|_U` (Tags 061A, 061D).

This file constructs **the action of the sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` on that
sheaf**: a section `θ` over `U'` moves a lift `a'` over `U'` to the lift `θ · a'` whose
comorphism differs from that of `a'` by the derivation `D = d_{Y/B} ∘ θ` of Equation (0619), the
notation of [Stacks Project, Tag 0CK6]. The acting sheaf is
`AlgebraicGeometry.Space.liftActionSheafChart`, the sheaf
`AlgebraicGeometry.Space.liftActionSheaf` read on the charts of `X'`.

## Main definitions

* `AlgebraicGeometry.Space.liftsTranslate`: the lift `θ · a'`.
* `AlgebraicGeometry.Space.liftsAddAction`: the action of the sections of the acting sheaf over
  `U'` on the lifts over `U'`.

## Main results

* `AlgebraicGeometry.Space.liftsTranslate_chart`: **the characterizing property of `θ · a'`**:
  on every chart `T ⟶ U'` through which `a'` factors through an affine chart `ε : T ⟶ Q` of `Y`
  (carrying an affine chart diagram over `B`), `θ · a'` factors through `Q` by the morphism
  whose map of regular functions is `x ↦ ε^♯ x + ι (θ (d x))`.
* `AlgebraicGeometry.Space.liftsTranslate_zero`, `AlgebraicGeometry.Space.liftsTranslate_add`:
  the action laws.
* `AlgebraicGeometry.Space.liftsTranslate_map`: the action commutes with the restriction maps
  of the two sheaves, so it is an action of the sheaf on the sheaf.

## Implementation notes

The translate is glued. Over a chart `T ⟶ U'` on which `a'` factors through an affine chart `Q`
of `Y` carrying an affine chart diagram over `B` — such charts cover `U'`,
`AlgebraicGeometry.Space.liftChartSieve_mem` — the morphism `T ⟶ Q` with map of regular
functions `ε^♯ + ι ∘ θ ∘ d` is `AlgebraicGeometry.Space.LiftChart.twistHom`; it is a lift
(`AlgebraicGeometry.Space.LiftChart.isChartLift_twistSection`), it does not depend on the chart
of `Y` (`AlgebraicGeometry.Space.twistSection_eq_of_liftChart`) and it is natural in `T`
(`AlgebraicGeometry.Space.LiftChart.map_comp_twistSection`), so these local lifts glue in the
sheaf of lifts. No appeal to Properties of Spaces, Theorem 04KL is made: every morphism
constructed has an affine target.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {X' Y Bs : AlgebraicSpaces C S hS} {Z : ClosedSubspaces C S hS X'.1}
  (hZ : IsFirstOrderThickening C S hS X' Z.1) {q : Y ⟶ Bs}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y} {p : X' ⟶ Bs}

/-- **Two charts of a lift on equal morphisms `T ⟶ U'` give the same twisted section.** -/
theorem twistSection_eq_of_liftChart_of_eq {U' : SmallEtale C S hS X'.1}
    {α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1}
    (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : (liftActionSheaf C S hS Z q a).val.obj
      (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U')))
    (T : SmallEtale C S hS X'.1) (m₁ m₂ : T ⟶ U') (hm : m₁ = m₂)
    (Q₁ : SmallEtale C S hS Y.1)
    (ε₁ : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q₁)
    (w₁ : yoneda.map ε₁ ≫ Q₁.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m₁) ≫ α)
    (hQ₁ : HasAffineChartDiagram C S hS q Q₁)
    (Q₂ : SmallEtale C S hS Y.1)
    (ε₂ : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q₂)
    (w₂ : yoneda.map ε₂ ≫ Q₂.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m₂) ≫ α)
    (hQ₂ : HasAffineChartDiagram C S hS q Q₂) :
    (⟨T, m₁, Q₁, ε₁, w₁⟩ : LiftChart C S hS U' α).twistSection hZ hα θ hQ₁ =
      (⟨T, m₂, Q₂, ε₂, w₂⟩ : LiftChart C S hS U' α).twistSection hZ hα θ hQ₂ := by
  subst hm
  exact twistSection_eq_of_liftChart hZ hα θ T m₁ Q₁ ε₁ w₁ hQ₁ Q₂ ε₂ w₂ hQ₂

/-- The Yoneda bijection for morphisms from a chart of `X'` into `Y`. -/
abbrev chartYoneda (T : SmallEtale C S hS X'.1) :
    (yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj T) ⟶ Y.1) ≃
      ((SmallEtale.toOver C S hS X'.1).op ⋙ Y.1).obj (op T) :=
  yonedaEquiv (C := BigFppfOver C S hS) (X := (SmallEtale.toOver C S hS X'.1).obj T) (F := Y.1)

/-- Membership in the covering sieve of the charts of a lift, unfolded. -/
theorem mem_liftChartSieve {U' : SmallEtale C S hS X'.1}
    {α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1}
    {T : SmallEtale C S hS X'.1} {m : T ⟶ U'} (hm : (liftChartSieve (q := q) α).arrows m) :
    ∃ (Q : SmallEtale C S hS Y.1)
      (ε : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q),
      yoneda.map ε ≫ Q.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ α ∧
        HasAffineChartDiagram C S hS q Q :=
  hm

/-- The sections of the sheaf of lifts over a chart `U'` of `X'`. -/
abbrev ChartLifts (p : X' ⟶ Bs) (q : Y ⟶ Bs)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) (U' : SmallEtale C S hS X'.1) :=
  (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')

/-- The sections of the acting sheaf over a chart `U'` of `X'`. -/
noncomputable abbrev ChartActingSections (q : Y ⟶ Bs)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    (U' : SmallEtale C S hS X'.1) :=
  (liftActionSheaf C S hS Z q a).val.obj
    (op ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).obj U'))

/-- A lift, as a morphism out of its chart. -/
abbrev ChartLifts.hom {U' : SmallEtale C S hS X'.1} (x : ChartLifts p q a U') :
    yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1 :=
  (chartYoneda U').symm x.1

/-- The lifting property of a lift. -/
theorem ChartLifts.isChartLift {U' : SmallEtale C S hS X'.1} (x : ChartLifts p q a U') :
    IsChartLift C S hS p q a.hom U' x.hom :=
  x.2

/-- The chart of a lift chosen on a morphism of the covering sieve of its charts. -/
noncomputable abbrev ChartLifts.chart {U' : SmallEtale C S hS X'.1} (x : ChartLifts p q a U')
    {T : SmallEtale C S hS X'.1} {m : T ⟶ U'} (hm : (liftChartSieve (q := q) x.hom).arrows m) :
    LiftChart C S hS U' x.hom :=
  ⟨T, m, (mem_liftChartSieve hm).choose, (mem_liftChartSieve hm).choose_spec.choose,
    (mem_liftChartSieve hm).choose_spec.choose_spec.1⟩

/-- The chart of `Y` of the chosen chart carries an affine chart diagram over `q`. -/
theorem ChartLifts.hasAffineChartDiagram_chart {U' : SmallEtale C S hS X'.1}
    (x : ChartLifts p q a U')
    {T : SmallEtale C S hS X'.1} {m : T ⟶ U'} (hm : (liftChartSieve (q := q) x.hom).arrows m) :
    HasAffineChartDiagram C S hS q (x.chart hm).Q :=
  (mem_liftChartSieve hm).choose_spec.choose_spec.2

include hZ in
/-- The local translate of a lift over a chart of the covering sieve. -/
noncomputable def liftsLocal {U' : SmallEtale C S hS X'.1} (θ : ChartActingSections q a U')
    (x : ChartLifts p q a U') :
    Presieve.FamilyOfElements (liftsSubfunctor C S hS p q a.hom).toFunctor
      (liftChartSieve (q := q) x.hom).arrows :=
  fun T _ hm ↦ ⟨chartYoneda T ((x.chart hm).twistSection hZ x.isChartLift θ
      (x.hasAffineChartDiagram_chart hm)), by
      change IsChartLift C S hS p q a.hom T ((chartYoneda T).symm (chartYoneda T _))
      rw [Equiv.symm_apply_apply]
      exact (x.chart hm).isChartLift_twistSection hZ x.isChartLift θ _⟩

/-- The value of the local translate, as a morphism out of the chart. -/
theorem liftsLocal_hom {U' : SmallEtale C S hS X'.1} (θ : ChartActingSections q a U')
    (x : ChartLifts p q a U') {T : SmallEtale C S hS X'.1} {m : T ⟶ U'}
    (hm : (liftChartSieve (q := q) x.hom).arrows m) :
    ChartLifts.hom (p := p) (q := q) (a := a) (liftsLocal hZ θ x m hm) =
      (x.chart hm).twistSection hZ x.isChartLift θ (x.hasAffineChartDiagram_chart hm) :=
  Equiv.symm_apply_apply _ _

/-- The restriction maps of the sheaf of lifts, read on morphisms out of the charts. -/
theorem liftsSubfunctor_map_hom {U' T : SmallEtale C S hS X'.1} (g : T ⟶ U')
    (x : ChartLifts p q a U') :
    ChartLifts.hom (p := p) (q := q) (a := a)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map g.op x) =
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map g) ≫ x.hom :=
  (yonedaEquiv_symm_naturality_left ((SmallEtale.toOver C S hS X'.1).map g) Y.1 x.1).symm

include hZ in
/-- **The local translates are compatible.** -/
theorem liftsLocal_compatible {U' : SmallEtale C S hS X'.1} (θ : ChartActingSections q a U')
    (x : ChartLifts p q a U') : (liftsLocal hZ θ x).Compatible := by
  intro T₁ T₂ T'' g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  refine Subtype.ext ((chartYoneda T'').symm.injective ?_)
  refine (liftsSubfunctor_map_hom g₁ _).trans ?_
  refine Eq.trans ?_ (liftsSubfunctor_map_hom g₂ _).symm
  rw [liftsLocal_hom, liftsLocal_hom,
    (x.chart h₁).map_comp_twistSection hZ x.isChartLift θ _ g₁,
    (x.chart h₂).map_comp_twistSection hZ x.isChartLift θ _ g₂]
  exact twistSection_eq_of_liftChart_of_eq hZ x.isChartLift θ T'' _ _ hcomm _ _ _ _ _ _ _ _


/-- The sheaf of lifts, as a sheaf of types in the sense of presieves. -/
theorem presieveIsSheaf_liftsSubfunctor (p : X' ⟶ Bs) (q : Y ⟶ Bs)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :
    Presieve.IsSheaf (SmallEtale.topology C S hS X'.1)
      (liftsSubfunctor C S hS p q a.hom).toFunctor :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_liftsSubfunctor C S hS p q a.hom)

/-- **The translate `θ · a'` of a lift `a'` by a local section `θ` of the acting sheaf**: the
amalgamation of the local translates over the charts of `a'`. -/
noncomputable def liftsTranslate {U' : SmallEtale C S hS X'.1} (θ : ChartActingSections q a U')
    (x : ChartLifts p q a U') : ChartLifts p q a U' :=
  ((presieveIsSheaf_liftsSubfunctor p q a) _ (liftChartSieve_mem q x.hom)).amalgamate
    (liftsLocal hZ θ x) (liftsLocal_compatible hZ θ x)

/-- The translate restricts, on a chart of the covering sieve, to the local translate. -/
theorem liftsTranslate_map_of_mem {U' : SmallEtale C S hS X'.1} (θ : ChartActingSections q a U')
    (x : ChartLifts p q a U') {T : SmallEtale C S hS X'.1} {m : T ⟶ U'}
    (hm : (liftChartSieve (q := q) x.hom).arrows m) :
    (liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op (liftsTranslate hZ θ x) =
      liftsLocal hZ θ x m hm :=
  ((presieveIsSheaf_liftsSubfunctor p q a) _ (liftChartSieve_mem q x.hom)).valid_glue
    (liftsLocal_compatible hZ θ x) m hm

/-- **The characterizing property of the translate `θ · a'`.** On every chart `T ⟶ U'` through
which `a'` factors through an affine chart `ε : T ⟶ Q` of `Y` carrying an affine chart diagram
over `B`, the restriction of `θ · a'` to `T` is the twisted section of the chart: the morphism
`T ⟶ Q ⟶ Y` whose map of regular functions is `x ↦ ε^♯ x + ι_T (θ (d_{Y/B} x))`
(`AlgebraicGeometry.Space.LiftChart.twistScheme_appTop`). -/
theorem liftsTranslate_chart {U' : SmallEtale C S hS X'.1} (θ : ChartActingSections q a U')
    (x : ChartLifts p q a U') (c : LiftChart C S hS U' x.hom)
    (hQ : HasAffineChartDiagram C S hS q c.Q) :
    yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ (liftsTranslate hZ θ x).hom =
      c.twistSection hZ x.isChartLift θ hQ := by
  have hm : (liftChartSieve (q := q) x.hom).arrows c.m := ⟨c.Q, c.ε, c.w, hQ⟩
  refine (liftsSubfunctor_map_hom c.m _).symm.trans ?_
  rw [liftsTranslate_map_of_mem hZ θ x hm, liftsLocal_hom]
  exact twistSection_eq_of_liftChart hZ x.isChartLift θ c.T c.m _ _ _ _ c.Q c.ε c.w hQ

/-- **Two lifts which agree on the charts of a lift are equal.** -/
theorem liftsAt_ext {U' : SmallEtale C S hS X'.1} (x y z : ChartLifts p q a U')
    (h : ∀ c : LiftChart C S hS U' x.hom, HasAffineChartDiagram C S hS q c.Q →
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ y.hom =
        yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ z.hom) : y = z := by
  refine ((presieveIsSheaf_liftsSubfunctor p q a) _ (liftChartSieve_mem q x.hom)).isSeparatedFor.ext
    fun T m hm ↦ ?_
  refine Subtype.ext ((chartYoneda T).symm.injective ?_)
  refine (liftsSubfunctor_map_hom m y).trans (Eq.trans ?_ (liftsSubfunctor_map_hom m z).symm)
  exact h (x.chart hm) (x.hasAffineChartDiagram_chart hm)

/-- **`0 · a' = a'`.** -/
theorem liftsTranslate_zero {U' : SmallEtale C S hS X'.1} (x : ChartLifts p q a U') :
    liftsTranslate hZ 0 x = x :=
  liftsAt_ext x _ _ fun c hQ ↦
    (liftsTranslate_chart hZ 0 x c hQ).trans (c.twistSection_zero hZ x.isChartLift hQ)

/-- The twisted morphism of charts acts on regular functions by the twisted map. -/
private theorem appTop_map_twistHom (hZ : IsFirstOrderThickening C S hS X' Z.1)
    {U' : SmallEtale C S hS X'.1}
    {α : yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1}
    (c : LiftChart C S hS U' α) (hα : IsChartLift C S hS p q a.hom U' α)
    (θ : ChartActingSections q a U') (hQ : HasAffineChartDiagram C S hS q c.Q)
    (f : (structureRingSheaf C S hS Y).obj.obj (op c.Q)) :
    ((BigFppfOver.toScheme C S hS).map (c.twistHom hZ hα θ hQ)).appTop.hom f =
      c.twist hZ hα θ f :=
  haveI : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((SmallEtale.toOver C S hS Y.1).obj c.Q)) := hQ.1
  (congrArg (fun φ ↦ φ.appTop.hom f) (c.toScheme_map_twistHom hZ hα θ hQ)).trans
    (c.twistScheme_appTop hZ hα θ f)

/-- **`(θ₁ + θ₂) · a' = θ₁ · (θ₂ · a')`.** -/
theorem liftsTranslate_add {U' : SmallEtale C S hS X'.1} (θ₁ θ₂ : ChartActingSections q a U')
    (x : ChartLifts p q a U') :
    liftsTranslate hZ (θ₁ + θ₂) x = liftsTranslate hZ θ₁ (liftsTranslate hZ θ₂ x) := by
  refine liftsAt_ext x _ _ fun c hQ ↦ ?_
  set y := liftsTranslate hZ θ₂ x with hy
  have w' : yoneda.map (c.twistHom hZ x.isChartLift θ₂ hQ) ≫ c.Q.1.hom =
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map c.m) ≫ y.hom :=
    (liftsTranslate_chart hZ θ₂ x c hQ).symm
  let c' : LiftChart C S hS U' y.hom :=
    ⟨c.T, c.m, c.Q, c.twistHom hZ x.isChartLift θ₂ hQ, w'⟩
  refine (liftsTranslate_chart hZ (θ₁ + θ₂) x c hQ).trans ?_
  refine Eq.trans ?_ (liftsTranslate_chart hZ θ₁ y c' hQ).symm
  refine (c.twistSection_eq_of_twist_eq hZ x.isChartLift (θ₁ + θ₂) hQ c.m _ w' y.isChartLift θ₁
    hQ fun t ↦ ?_).symm
  have hcond : (SmallEtale.toOver C S hS Z.1.toFunctor).map
        (𝟙 (conormalChartDiagram C S hS Z c.T).U) ≫ (c.diagram x.isChartLift).g =
      (c'.diagram y.isChartLift).g ≫ (SmallEtale.toOver C S hS Y.1).map (𝟙 c.Q) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
    exact (c.snd_comp_twistHom hZ x.isChartLift θ₂ hQ).symm
  have hunit := modulePullbackUnitSection_naturality a (sheafOfDifferentials C S hS q)
    (c.diagram x.isChartLift) (c'.diagram y.isChartLift) _ _ hcond
    ((universalDerivation C S hS q).d t)
  have hid₁ : (sheafOfDifferentials C S hS q).val.map (𝟙 c.Q).op
      ((universalDerivation C S hS q).d t) = (universalDerivation C S hS q).d t :=
    PresheafOfModules.map_id_apply _ _ _
  have hid₂ : ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)).val.map
      (𝟙 (conormalChartDiagram C S hS Z c.T).U).op
        (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q)
          (c.diagram x.isChartLift) ((universalDerivation C S hS q).d t)) =
      modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q)
          (c.diagram x.isChartLift) ((universalDerivation C S hS q).d t) :=
    PresheafOfModules.map_id_apply _ _ _
  have hD : c'.derivation y.isChartLift θ₁ t = c.derivation x.isChartLift θ₁ t :=
    congrArg (liftActionSheafApp C S hS Z q a θ₁
      (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map c.m)))
      (((congrArg (modulePullbackUnitSection C S hS a (sheafOfDifferentials C S hS q)
        (c'.diagram y.isChartLift)) hid₁).symm.trans hunit).trans hid₂)
  have hpb : c'.pullback t = c.twist hZ x.isChartLift θ₂ t :=
    appTop_map_twistHom hZ c x.isChartLift θ₂ hQ t
  refine (c'.twist_apply hZ y.isChartLift θ₁ t).trans ?_
  rw [hpb, hD, c.twist_apply, c.twist_apply]
  have hadd : c.derivation x.isChartLift (θ₁ + θ₂) t =
      c.derivation x.isChartLift θ₁ t + c.derivation x.isChartLift θ₂ t := rfl
  rw [hadd, conormalChartIncl_add, add_assoc, add_comm (conormalChartIncl C S hS Z hZ c.T
    (c.derivation x.isChartLift θ₂ t))]

/-- **The action of the sections of `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` over `U'` on the
lifts of `a` over `U'`**, `θ +ᵥ a' = θ · a'`. -/
@[instance_reducible]
noncomputable def liftsAddAction (U' : SmallEtale C S hS X'.1) :
    AddAction (ChartActingSections q a U') (ChartLifts p q a U') where
  vadd := liftsTranslate hZ
  zero_vadd := liftsTranslate_zero hZ
  add_vadd := liftsTranslate_add hZ

/-- The restriction map of the acting sheaf along a morphism of charts of `X'`. -/
noncomputable abbrev actingMap {U' U'' : SmallEtale C S hS X'.1} (k : U'' ⟶ U')
    (θ : ChartActingSections q a U') : ChartActingSections q a U'' :=
  (liftActionSheaf C S hS Z q a).val.map
    ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map k).op θ

/-- **The action commutes with the restriction maps**: restricting `θ · a'` along `U'' ⟶ U'` is
translating the restriction of `a'` by the restriction of `θ`. So the action is an action of the
sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` on the sheaf of lifts. -/
theorem liftsTranslate_map {U' U'' : SmallEtale C S hS X'.1} (k : U'' ⟶ U')
    (θ : ChartActingSections q a U') (x : ChartLifts p q a U') :
    (liftsSubfunctor C S hS p q a.hom).toFunctor.map k.op (liftsTranslate hZ θ x) =
      liftsTranslate hZ (actingMap k θ)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map k.op x) := by
  let x'' : ChartLifts p q a U'' := (liftsSubfunctor C S hS p q a.hom).toFunctor.map k.op x
  refine liftsAt_ext x'' _ _ fun c'' hQ ↦ ?_
  obtain ⟨T, m'', Q, ε, w''⟩ := c''
  have w : yoneda.map ε ≫ Q.1.hom =
      yoneda.map ((SmallEtale.toOver C S hS X'.1).map (m'' ≫ k)) ≫ x.hom := by
    rw [w'', liftsSubfunctor_map_hom k x, Functor.map_comp, Functor.map_comp, Category.assoc]
  let c : LiftChart C S hS U' x.hom := ⟨T, m'' ≫ k, Q, ε, w⟩
  have hL : yoneda.map ((SmallEtale.toOver C S hS X'.1).map m'') ≫
      ChartLifts.hom (p := p) (q := q) (a := a)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map k.op (liftsTranslate hZ θ x)) =
      c.twistSection hZ x.isChartLift θ hQ := by
    rw [liftsSubfunctor_map_hom k (liftsTranslate hZ θ x), ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp]
    exact liftsTranslate_chart hZ θ x c hQ
  have hR := liftsTranslate_chart hZ (actingMap k θ) x'' ⟨T, m'', Q, ε, w''⟩ hQ
  refine hL.trans (Eq.trans ?_ hR.symm)
  refine (c.twistSection_eq_of_twist_eq hZ x.isChartLift θ hQ m'' ε w'' x''.isChartLift
    (actingMap k θ) hQ fun t ↦ ?_).symm
  have hD : (⟨T, m'', Q, ε, w''⟩ : LiftChart C S hS U'' x''.hom).derivation x''.isChartLift
      (actingMap k θ) t = c.derivation x.isChartLift θ t := by
    refine (liftActionSheafApp_map C S hS Z
      ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map k) θ
      (Over.mk ((smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep).map m''))
      _).trans ?_
    exact liftActionSheafApp_mk_congr C S hS Z θ
      (Functor.map_comp (smallBaseChange C S hS (subspaceInclusion C S hS X' Z) Z.2.2.rep)
        m'' k).symm _
  refine ((⟨T, m'', Q, ε, w''⟩ : LiftChart C S hS U'' x''.hom).twist_apply hZ x''.isChartLift
    (actingMap k θ) t).trans (Eq.trans ?_ (c.twist_apply hZ x.isChartLift θ t).symm)
  exact congrArg (fun z ↦ c.pullback t + conormalChartIncl C S hS Z hZ T z) hD

/-! ### The statement of Stacks 061D -/

section Remark

variable {G : Subfunctor X'.1}

/-- **[Stacks Project, Tag 061D], the action.** Let `X ⊂ X'` be a first order thickening of
algebraic spaces over `S`, let `p : X' ⟶ B` and `q : Y ⟶ B`, and let `a : X ⟶ Y`. The sheaf
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})`, read on the étale charts of `X'`
(`AlgebraicGeometry.Space.liftActionSheafChart`), acts on the sheaf of lifts
`U' ↦ {a' : U' ⟶ Y over B with a'|_U = a|_U}` (`AlgebraicGeometry.Space.liftsSubfunctor`):

* for every chart `U'` the sections of the acting sheaf over `U'` act additively on the lifts
  over `U'` (`AddAction`: `0 · a' = a'` and `(θ₁ + θ₂) · a' = θ₁ · (θ₂ · a')`);
* the action commutes with the restriction maps of the two sheaves along every morphism of
  charts `U'' ⟶ U'`, so it is an action of the sheaf on the sheaf;
* it is the action of [Stacks Project, Tag 0CK6]: on every chart `m : T ⟶ U'` on which `a'`
  factors through an affine chart `ε : T ⟶ Q` of `Y` carrying an affine chart diagram over `B`,
  `θ · a'` factors through `Q` by a morphism `ψ` whose map of regular functions is
  `x ↦ ε^♯ x + ι_T (D x)`, where `D = θ ∘ d_{Y/B}` is the derivation of Equation (0619) read on
  the chart (`AlgebraicGeometry.Space.LiftChart.derivation`) and
  `ι_T : 𝒞_{X/X'}(T_X) ⟶ Γ(T, 𝒪_T)` is the inclusion of the conormal module
  (`AlgebraicGeometry.Space.conormalChartIncl`). That is, the comorphisms of `θ · a'` and `a'`
  differ by the derivation `D`. -/
@[stacks 061D "the action of SheafHom_{O_X}(a^*Omega_{Y/B}, C_{X/X'}) on the sheaf of lifts \
U' ↦ {a' : U' → Y over B with a'|_U = a|_U}: an additive action on the sections over every \
étale chart, commuting with the restriction maps of both sheaves, under which the comorphisms of \
θ · a' and a' differ by the derivation d_{Y/B} ∘ θ"]
theorem exists_liftActionSheafChart_addAction (hG : IsFirstOrderThickening C S hS X' G)
    (p : X' ⟶ Bs) (q : Y ⟶ Bs) (a : IsThickening.space C S hS hG.1 ⟶ Y) :
    ∃ act : ∀ U' : SmallEtale C S hS X'.1,
        AddAction ((liftActionSheafChart C S hS hG.1 q a).val.obj (op U'))
          ((liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')),
      (∀ {U' U'' : SmallEtale C S hS X'.1} (k : U'' ⟶ U')
          (θ : (liftActionSheafChart C S hS hG.1 q a).val.obj (op U'))
          (x : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')),
        (liftsSubfunctor C S hS p q a.hom).toFunctor.map k.op ((act U').vadd θ x) =
          (act U'').vadd ((liftActionSheafChart C S hS hG.1 q a).val.map k.op θ)
            ((liftsSubfunctor C S hS p q a.hom).toFunctor.map k.op x)) ∧
      ∀ (U' : SmallEtale C S hS X'.1)
        (θ : (liftActionSheafChart C S hS hG.1 q a).val.obj (op U'))
        (x : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U'))
        (T : SmallEtale C S hS X'.1) (m : T ⟶ U') (Q : SmallEtale C S hS Y.1)
        (ε : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q)
        (w : yoneda.map ε ≫ Q.1.hom =
          yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫ yonedaEquiv.symm x.1),
        HasAffineChartDiagram C S hS q Q →
        ∃ ψ : (SmallEtale.toOver C S hS X'.1).obj T ⟶ (SmallEtale.toOver C S hS Y.1).obj Q,
          yoneda.map ψ ≫ Q.1.hom = yoneda.map ((SmallEtale.toOver C S hS X'.1).map m) ≫
            yonedaEquiv.symm ((act U').vadd θ x).1 ∧
          ∀ f : (structureRingSheaf C S hS Y).obj.obj (op Q),
            ((BigFppfOver.toScheme C S hS).map ψ).appTop.hom f =
              ((BigFppfOver.toScheme C S hS).map ε).appTop.hom f +
                (show Γ((BigFppfOver.toScheme C S hS).obj
                    ((SmallEtale.toOver C S hS X'.1).obj T), ⊤) from
                  conormalChartIncl C S hS ⟨G, hG.1.1⟩ hG T
                    ((⟨T, m, Q, ε, w⟩ : LiftChart C S hS U' (yonedaEquiv.symm x.1)).derivation
                      (Z := ⟨G, hG.1.1⟩) (p := p) (q := q) (a := a) x.2 θ f)) := by
  refine ⟨fun U' ↦ liftsAddAction (Z := ⟨G, hG.1.1⟩) (q := q) (a := a) (p := p) hG U', ?_, ?_⟩
  · intro U' U'' k θ x
    exact liftsTranslate_map (Z := ⟨G, hG.1.1⟩) (q := q) (a := a) (p := p) hG k θ x
  · intro U' θ x T m Q ε w hQ
    have hx : IsChartLift C S hS p q a.hom U' (yonedaEquiv.symm x.1) := x.2
    let c : LiftChart C S hS U' (yonedaEquiv.symm x.1) := ⟨T, m, Q, ε, w⟩
    refine ⟨c.twistHom (Z := ⟨G, hG.1.1⟩) hG hx θ hQ,
      (liftsTranslate_chart (Z := ⟨G, hG.1.1⟩) (q := q) (a := a) (p := p) hG θ x c hQ).symm,
      fun f ↦ ?_⟩
    exact (appTop_map_twistHom (Z := ⟨G, hG.1.1⟩) (q := q) (a := a) (p := p) hG c hx θ hQ
      f).trans (c.twist_apply hG hx θ f)

end Remark

end AlgebraicGeometry.Space

end
