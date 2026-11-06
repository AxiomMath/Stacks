module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftRestrictionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing the chartwise action on the lifts into an action of sheaves

This file is the glueing step of [Stacks Project, Tag 061C]: the chartwise action of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`, read at a chart of the
ambient space by
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection`, is assembled into an
action of the acting sheaf of groups
`AlgebraicGeometry.Space.liftActionSheafOfGroups` on the sheaf of lifts
`AlgebraicGeometry.Space.liftsSubfunctorULift` at **every** object of the small étale site of
`X'`, not only at those carrying a chart presentation, and the result is packaged as a
`PseudoTorsor`.

What makes the glueing possible without choosing chart presentations is the relation
`AlgebraicGeometry.Space.IsTranslateBy`, "`θ` carries the lift `β` to the lift `γ` over `U'`",
defined by quantifying over *all* chart presentations below `U'` whose presented lift is the
restriction of `β`.  Stability under restriction and uniqueness of `γ` are then immediate — the
latter because chart presentations exist on a covering family of charts,
`AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows` — and they are what
makes every amalgamation in this file automatic: the local translates agree wherever two members
of a covering family are compared because each of them *is* a translate.

## What is conditional, and what is not

The action itself, its two laws and its simple transitivity are **conditional on
`AlgebraicGeometry.Space.IsChartTranslationCompatible`**, whose docstring says what it asserts
and the two chart compatibilities it specialises to: the naturality in the chart
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`,
and a comparison of two chart presentations over one chart.

That predicate is reduced to those two, unconditionally, by
`AlgebraicGeometry.Space.isChartTranslationCompatible_of_natural_of_presentationIndependent`
in the last section, so it is the conjunction of two comparisons, each about a single
identification.

Everything else is unconditional: the two uniqueness statements
(`AlgebraicGeometry.Space.eq_of_isTranslateBy`,
`AlgebraicGeometry.Space.eq_of_isTranslateBy_left`), the locality of the relation
(`AlgebraicGeometry.Space.isTranslateBy_of_sieve` is conditional, but its two sheaf-theoretic
inputs are not), the zero laws, and the freeness statement
`AlgebraicGeometry.Space.translateTransportSection_add_of_eq` which shows the instance of the
compatibility at one presentation and the identity morphism of charts to hold.

## Main definitions

* `AlgebraicGeometry.Space.ChartLiftPresentation.IsEtaleChartSquare`: the two charts of `q` of a
  chart presentation are étale, which is the hypothesis every chart-level statement about the
  action carries.
* `AlgebraicGeometry.Space.IsTranslateBy`: **the relation "`θ` carries the lift `β` to the lift
  `γ` over `U'`"** — the chartwise translation, read at every chart presentation below `U'`.  It
  is this relation, rather than a chosen chart presentation, which glues.
* `AlgebraicGeometry.Space.IsChartTranslationCompatible`: **the compatibility of the chartwise
  actions that the glueing needs**, and its two halves
  `AlgebraicGeometry.Space.IsActionSectionRestrictionNaturalEverywhere` (the ∀-form of the
  naturality in the chart) and
  `AlgebraicGeometry.Space.IsChartActionPresentationIndependent` (**the half that naturality
  does not give**: two chart presentations over one chart, whose chart squares of `q` differ).
* `AlgebraicGeometry.Space.translateGlobalSection`: **the action of a section of the acting sheaf
  on the sheaf of lifts over an arbitrary object of the small étale site of `X'`.**
* `AlgebraicGeometry.Space.liftTorsorAct` and `AlgebraicGeometry.Space.liftPseudoTorsor`: the
  same action in the shape `PseudoTorsor` asks for, and **the pseudo-torsor itself**.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_zero`: the zero
  section of the acting sheaf fixes the presented lift.
* `AlgebraicGeometry.Space.IsTranslateBy.restrict`: the translation relation is stable under
  restriction to a smaller chart, by construction.
* `AlgebraicGeometry.Space.eq_of_isTranslateBy`: **the translate is unique** — two lifts which
  `θ` carries `β` to are equal.  This is the freeness and the sheaf condition of the sheaf of
  lifts, and it carries no hypothesis beyond the first-order thickening.
* `AlgebraicGeometry.Space.eq_of_isTranslateBy_left`: **the translating section is unique** — two
  sections of the acting sheaf which carry `β` to the same lift are equal.
* `AlgebraicGeometry.Space.isTranslateBy_zero`: the zero section carries every lift to itself.
* `AlgebraicGeometry.Space.exists_isTranslateBy` and
  `AlgebraicGeometry.Space.exists_isTranslateBy_left`: **the translate and the translating
  section exist**, by amalgamating the chartwise ones.
* `AlgebraicGeometry.Space.translateGlobalSection_zero`,
  `AlgebraicGeometry.Space.translateGlobalSection_add`,
  `AlgebraicGeometry.Space.translateGlobalSection_map` and
  `AlgebraicGeometry.Space.existsUnique_translateGlobalSection`: **the four laws of the glued
  action** — the identity acts trivially, translating by a sum is translating twice, naturality
  in the chart, and simple transitivity at every object.
* `Stacks.CategoryTheory.eq_of_locally_locally_eq`: a generic engine — two sections of a sheaf of
  types which agree on a covering sieve of each member of a covering sieve are equal.
* `AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartMap_comp_subEtaleChartIso_hom` and
  `AlgebraicGeometry.Space.liftActionSheaf_map_subEtaleChartIso_naturality`: **the comparison of
  the presented chart of the closed subspace with the base-changed chart is natural in the
  chart**, and the restriction maps of the acting sheaf commute with it.  Unconditional, and the
  bookkeeping half of the reduction of the compatibility to its two halves.
* `AlgebraicGeometry.Space.map_translateTransportSection_of_isActionSectionRestrictionNatural`:
  **the chartwise action commutes with restriction to a smaller chart**, granted the naturality
  in the chart, and
  `AlgebraicGeometry.Space.isChartTranslationCompatible_of_natural_of_presentationIndependent`:
  **the reduction of `AlgebraicGeometry.Space.IsChartTranslationCompatible` to its two halves**.

## Why local nonemptiness is not here

`PseudoTorsor.IsTorsor` — that every object of the site is covered by objects over which the
sheaf of lifts has a section — is **not** asserted by [Stacks Project, Tag 061C], which states
simple transitivity only "for any object `U'` over which the sheaf admits a section", and it is
false without a smoothness hypothesis on `q`: for `Bb = Spec k[s]`, `Y = Spec k` with `q` the
origin, `X' = Spec k[ε]/(ε²)` over `Bb` by `s ↦ ε`, `X = Spec k` and `a` the identity of
`Spec k`, a lift over a chart `U'` would be a morphism `U' ⟶ Spec k` over `Bb`, forcing the
image of `s` in `Γ(U', ⊤)` to vanish; it does not on any nonempty étale chart of `X'`, and a
covering family of `X'` has a nonempty member.  A true local-nonemptiness statement needs the
chart square `W ⟶ V` of `q` to be formally smooth, which is the content of
[Stacks Project, Tag 04AM] rather than of the torsor structure.

[Stacks Project, Tag 061C] asserts the pseudo-torsor property unconditionally; what is built
here is conditional on `AlgebraicGeometry.Space.IsChartTranslationCompatible`.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CategoryTheory

open CategoryTheory Opposite

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type w}

/-- **Two sections of a sheaf of types which agree locally on a cover of a cover are equal.**

This is the sheaf condition used twice, packaged once: the equality of two sections is itself a
sieve, so if it holds on a covering sieve of each member of a covering sieve then the
transitivity of the topology makes it hold on a covering sieve, and the sheaf is separated
for that. -/
@[sga "2 XIV 1.8.2.1" "more general"]
theorem eq_of_locally_locally_eq (hF : Presieve.IsSheaf J F) {W : C} {x y : F.obj (op W)}
    {R : Sieve W} (hR : R ∈ J W)
    (h : ∀ ⦃T : C⦄ (n : T ⟶ W), R n → ∃ R' ∈ J T, ∀ ⦃T₀ : C⦄ (k : T₀ ⟶ T), R' k →
      F.map (k ≫ n).op x = F.map (k ≫ n).op y) :
    x = y := by
  have hEcov : (⟨fun _ k => F.map k.op x = F.map k.op y,
      fun {_ _ k} hk g => by
        rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hk]⟩ : Sieve W) ∈ J W := by
    refine J.transitive hR _ ?_
    intro T n hn
    obtain ⟨R', hR', hR'eq⟩ := h n hn
    refine J.superset_covering ?_ hR'
    intro T₀ k hk
    exact hR'eq k hk
  refine (hF _ hEcov).isSeparatedFor.ext ?_
  intro T k hk
  exact hk

/-- Two sections of a presheaf separated for a covering `ofArrows` sieve are equal when their
restrictions along each arrow of the family are. -/
private theorem eq_of_map_ofArrows_eq {X : C} {I : Type*} {W : I → C} {r : ∀ i, W i ⟶ X}
    (hF : Presieve.IsSeparatedFor F (Sieve.ofArrows W r : Presieve X)) {x y : F.obj (op X)}
    (h : ∀ i, F.map (r i).op x = F.map (r i).op y) : x = y :=
  hF.ext fun _ _ hk => by
    obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h i]

/-- A compatible family on the members of a covering `ofArrows` sieve glues to a section
restricting to each member of the family. -/
private theorem exists_map_ofArrows_eq {X : C} {I : Type*} {W : I → C} {r : ∀ i, W i ⟶ X}
    (hF : Presieve.IsSheafFor F (Sieve.ofArrows W r : Presieve X)) (x : ∀ i, F.obj (op (W i)))
    (hx : ∀ ⦃i j : I⦄ ⦃T : C⦄ (gi : T ⟶ W i) (gj : T ⟶ W j), gi ≫ r i = gj ≫ r j →
      F.map gi.op (x i) = F.map gj.op (x j)) :
    ∃ y, ∀ i, F.map (r i).op y = x i := by
  obtain ⟨y, hy, -⟩ := (Presieve.isSheafFor_arrows_iff _ r).1
    ((Presieve.isSheafFor_iff_generate (Presieve.ofArrows W r)).2 hF) x hx
  exact ⟨y, hy⟩

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

/-! ### The étaleness hypothesis of a chart presentation -/

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}

/-- **The two charts of `q` of a chart presentation are étale.**  This is the hypothesis which
every chart-level statement about the action of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` carries, bundled so that a
statement quantifying over chart presentations can name it once.  It is exactly what
[Stacks Project, Tag 04CU] needs, and it is satisfied by every presentation that
`AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows` produces. -/
def IsEtaleChartSquare {U' : SmallEtale C S hS X'.1}
    (P : ChartLiftPresentation C S hS p q a.hom U') : Prop :=
  (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart ∧
    (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart

variable {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')

/-- The identification of the sections of the acting sheaf at the presented chart with the acting
group of the presentation carries the zero section to the zero linear map: it is additive. -/
theorem actionSectionEquiv_zero (hP : P.IsEtaleChartSquare C S hS) :
    actionSectionEquiv C S hS P hP.1 hP.2 0 = 0 :=
  map_zero (actionSectionAddEquiv C S hS P hP.1 hP.2)

/-- The identification of the sections of the transported acting sheaf over the chart of `X'`
with the acting group of a chart presentation there carries the zero section to the zero linear
map. -/
theorem transportActionSectionEquiv_zero (hG : IsThickening C S hS X' Z.1)
    (hP : P.IsEtaleChartSquare C S hS) :
    P.transportActionSectionEquiv C S hS hG hP.1 hP.2 0 = 0 := by
  have h0 : (liftActionSheafTypeSheaf C S hS Z q a).obj.map
        (P.subEtaleChartIso C S hS hG).op.hom
        (0 : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) =
      (0 : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart)) :=
    map_zero ((liftActionSheaf C S hS Z q a).val.presheaf.map
      (P.subEtaleChartIso C S hS hG).op.hom).hom
  exact (congrArg (⇑(actionSectionEquiv C S hS P hP.1 hP.2)) h0).trans
    (P.actionSectionEquiv_zero C S hS hP)

/-- The identification of the sections of the transported acting sheaf over the chart of `X'`
with the acting group of a chart presentation there is **additive**.

The two factors of
`AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv` are additive for
different reasons: the first is a restriction map of the acting sheaf along the comparison of
the two charts of `X`, hence the map underlying a morphism of abelian groups, and the second is
additive by `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv_add`.  The first
factor is handled exactly as in
`AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv_zero`: the
restriction map of the transported sheaf is `map_add` of the morphism of abelian groups on the
acting sheaf's side, which is the spelling the elaborator can unify. -/
theorem transportActionSectionEquiv_add (hG : IsThickening C S hS X' Z.1)
    (hP : P.IsEtaleChartSquare C S hS)
    (θ η : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    P.transportActionSectionEquiv C S hS hG hP.1 hP.2 (θ + η) =
      P.transportActionSectionEquiv C S hS hG hP.1 hP.2 θ +
        P.transportActionSectionEquiv C S hS hG hP.1 hP.2 η := by
  have hadd := map_add ((liftActionSheaf C S hS Z q a).val.presheaf.map
    (P.subEtaleChartIso C S hS hG).op.hom).hom θ η
  exact (congrArg (⇑(actionSectionEquiv C S hS P hP.1 hP.2)) hadd).trans
    (actionSectionEquiv_add C S hS P hP.1 hP.2 _ _)

/-- The derivation attached to the zero section of the acting sheaf is the zero derivation. -/
theorem derivOfActionSection_zero : P.derivOfActionSection 0 = 0 :=
  rfl

/-- **The derivation attached to a section of the acting sheaf at the chart is additive in the
section.**  Both sides are the composite of the section with the pullback of the universal
differential, and the addition of acting sections and of derivations are both pointwise. -/
theorem derivOfActionSection_add (θ η : P.ActionSection) :
    P.derivOfActionSection (θ + η) = P.derivOfActionSection θ + P.derivOfActionSection η :=
  rfl

/-- **The zero section of the acting sheaf fixes the presented lift.**  The translate of the
presented lift by the zero section of the transported acting sheaf is the presented lift. -/
theorem translateTransportSection_zero (hG : IsThickening C S hS X' Z.1)
    (hP : P.IsEtaleChartSquare C S hS) :
    P.translateTransportSection C S hS hG hP.1 hP.2 0 = P.liftSection := by
  rw [translateTransportSection, P.transportActionSectionEquiv_zero C S hS hG hP,
    translateActionSection, P.derivOfActionSection_zero, P.translateSection_zero]

end ChartLiftPresentation

/-! ### Restriction and the sheaf conditions of the two sheaves -/

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}

/-- Restricting a lift along a composite of morphisms of charts is restricting twice. -/
theorem liftsSubfunctor_map_comp_apply (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) {U' V' W' : SmallEtale C S hS X'.1} (m : W' ⟶ V') (n : V' ⟶ U')
    (x : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    (liftsSubfunctor C S hS p q a).toFunctor.map (m ≫ n).op x =
      (liftsSubfunctor C S hS p q a).toFunctor.map m.op
        ((liftsSubfunctor C S hS p q a).toFunctor.map n.op x) := by
  rw [op_comp, Functor.map_comp_apply]

/-- Restricting a section of the transported acting sheaf along a composite of morphisms of
charts is restricting twice. -/
theorem liftActionSheafTransport_map_comp_apply (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' V' W' : SmallEtale C S hS X'.1} (m : W' ⟶ V') (n : V' ⟶ U')
    (x : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    (liftActionSheafTransport C S hS Z hG q a).obj.map (m ≫ n).op x =
      (liftActionSheafTransport C S hS Z hG q a).obj.map m.op
        ((liftActionSheafTransport C S hS Z hG q a).obj.map n.op x) := by
  rw [op_comp, Functor.map_comp_apply]

/-- **The restriction maps of the transported acting sheaf carry the zero section to the zero
section**: by `AlgebraicGeometry.Space.liftActionSheafTransport_map_apply` they are the maps
underlying morphisms of abelian groups. -/
theorem liftActionSheafTransport_map_zero (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U') :
    (liftActionSheafTransport C S hS Z hG q a).obj.map m.op
        (0 : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) =
      (0 : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op V')) := by
  rw [liftActionSheafTransport_map_apply]
  exact map_zero _

/-- **A restriction map of the transported acting sheaf is a restriction map of the acting sheaf
along base change of charts**, in the module spelling and by `rfl`.  This is
`AlgebraicGeometry.Space.liftActionSheafTransport_map_apply` with the target read as a module
rather than as an abelian group, which is the spelling the chart-level identification of the
acting group uses. -/
theorem liftActionSheafTransport_map_eq (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    (liftActionSheafTransport C S hS Z hG q a).obj.map m.op θ =
      (liftActionSheaf C S hS Z q a).val.map
        ((thickeningChartBaseChange C S hS hG).map m).op θ :=
  rfl

/-- The sheaf of lifts is a sheaf for every covering sieve of the small étale site of `X'`, in
the presieve form which amalgamates a compatible family. -/
theorem isSheafFor_liftsSubfunctor (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) {U' : SmallEtale C S hS X'.1} {R : Sieve U'}
    (hR : R ∈ SmallEtale.topology C S hS X'.1 U') :
    Presieve.IsSheafFor (liftsSubfunctor C S hS p q a).toFunctor (R : Presieve U') :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_liftsSubfunctor C S hS p q a) R hR

/-- The sheaf of lifts is separated for every covering sieve of the small étale site of `X'`. -/
theorem isSeparatedFor_liftsSubfunctor (p : X' ⟶ Bb) (q : Y ⟶ Bb) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) {U' : SmallEtale C S hS X'.1} {R : Sieve U'}
    (hR : R ∈ SmallEtale.topology C S hS X'.1 U') :
    Presieve.IsSeparatedFor (liftsSubfunctor C S hS p q a).toFunctor (R : Presieve U') :=
  (isSheafFor_liftsSubfunctor C S hS p q a hR).isSeparatedFor

/-- The transported acting sheaf is a sheaf for every covering sieve of the small étale site of
`X'`. -/
theorem isSheafFor_liftActionSheafTransport (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' : SmallEtale C S hS X'.1} {R : Sieve U'}
    (hR : R ∈ SmallEtale.topology C S hS X'.1 U') :
    Presieve.IsSheafFor (liftActionSheafTransport C S hS Z hG q a).obj (R : Presieve U') :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (liftActionSheafTransport C S hS Z hG q a).property R hR

/-- The transported acting sheaf is separated for every covering sieve of the small étale site of
`X'`. -/
theorem isSeparatedFor_liftActionSheafTransport (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y)
    {U' : SmallEtale C S hS X'.1} {R : Sieve U'}
    (hR : R ∈ SmallEtale.topology C S hS X'.1 U') :
    Presieve.IsSeparatedFor (liftActionSheafTransport C S hS Z hG q a).obj (R : Presieve U') :=
  (isSheafFor_liftActionSheafTransport C S hS Z hG q a hR).isSeparatedFor

/-! ### The translation relation -/

/-- **The relation "the section `θ` of the acting sheaf carries the lift `β` to the lift `γ` over
`U'`".**

It is defined so as to be independent of any choice of chart presentation: `γ` is the translate
of `β` by `θ` when, over *every* smaller chart carrying a chart presentation whose presented lift
is the restriction of `β`, the restriction of `γ` is the chartwise translate
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection` of that presented lift
by the restriction of `θ`.  Two consequences come for free from this shape: the relation is
stable under restriction
(`AlgebraicGeometry.Space.IsTranslateBy.restrict`) and it determines `γ` uniquely
(`AlgebraicGeometry.Space.eq_of_isTranslateBy`), the latter because chart presentations exist on
a covering family. -/
def IsTranslateBy (hG : IsThickening C S hS X' Z.1) {U' : SmallEtale C S hS X'.1}
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U'))
    (β γ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) : Prop :=
  ∀ ⦃V' : SmallEtale C S hS X'.1⦄ (m : V' ⟶ U')
    (Q : ChartLiftPresentation C S hS p q a.hom V')
    (hQ : Q.IsEtaleChartSquare C S hS),
    Q.liftSection = (liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op β →
      (liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op γ =
        Q.translateTransportSection C S hS hG hQ.1 hQ.2
          ((liftActionSheafTransport C S hS Z hG q a).obj.map m.op θ)

/-- **The translation relation is stable under restriction to a smaller chart.**  This holds by
the shape of `AlgebraicGeometry.Space.IsTranslateBy`, which quantifies over all chart
presentations below the chart. -/
theorem IsTranslateBy.restrict {hG : IsThickening C S hS X' Z.1}
    {U' : SmallEtale C S hS X'.1}
    {θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')}
    {β γ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')}
    (h : IsTranslateBy C S hS hG θ β γ) {V' : SmallEtale C S hS X'.1} (n : V' ⟶ U') :
    IsTranslateBy C S hS hG
      ((liftActionSheafTransport C S hS Z hG q a).obj.map n.op θ)
      ((liftsSubfunctor C S hS p q a.hom).toFunctor.map n.op β)
      ((liftsSubfunctor C S hS p q a.hom).toFunctor.map n.op γ) := by
  intro W' m Q hQ hbase
  rw [← liftsSubfunctor_map_comp_apply, ← liftActionSheafTransport_map_comp_apply]
  exact h (m ≫ n) Q hQ (hbase.trans (liftsSubfunctor_map_comp_apply C S hS p q a.hom m n β).symm)

/-- **The translate is unique.**  Two lifts which `θ` carries `β` to are equal: on a covering
family of charts carrying a chart presentation with presented lift the restriction of `β` — which
`AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows` supplies — both
restrict to the chartwise translate, and the sheaf of lifts is separated. -/
theorem eq_of_isTranslateBy (hX : IsFirstOrderThickening C S hS X' Z.1)
    {U' : SmallEtale C S hS X'.1}
    {θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U')}
    {β γ₁ γ₂ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')}
    (h₁ : IsTranslateBy C S hS hX.isThickening θ β γ₁)
    (h₂ : IsTranslateBy C S hS hX.isThickening θ β γ₂) :
    γ₁ = γ₂ := by
  obtain ⟨I, W, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a.hom hX U' β
  refine Stacks.CategoryTheory.eq_of_map_ofArrows_eq
    (isSeparatedFor_liftsSubfunctor C S hS p q a.hom hcov) fun i => ?_
  rw [h₁ (r i) (P i) ⟨hw i, hv i⟩ (hval i), h₂ (r i) (P i) ⟨hw i, hv i⟩ (hval i)]

/-- **The translating section is unique.**  Two sections of the acting sheaf which carry `β` to
the same lift are equal: this is the freeness of the chartwise action
(`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_bijective`) together
with the sheaf condition of the acting sheaf. -/
theorem eq_of_isTranslateBy_left (hX : IsFirstOrderThickening C S hS X' Z.1)
    {U' : SmallEtale C S hS X'.1}
    {θ θ' : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U')}
    {β γ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')}
    (h₁ : IsTranslateBy C S hS hX.isThickening θ β γ)
    (h₂ : IsTranslateBy C S hS hX.isThickening θ' β γ) :
    θ = θ' := by
  obtain ⟨I, W, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a.hom hX U' β
  refine Stacks.CategoryTheory.eq_of_map_ofArrows_eq
    (isSeparatedFor_liftActionSheafTransport C S hS Z hX.isThickening q a hcov) fun i => ?_
  refine ((P i).translateTransportSection_bijective C S hS hX.isThickening (hw i) (hv i)).1 ?_
  rw [← h₁ (r i) (P i) ⟨hw i, hv i⟩ (hval i), ← h₂ (r i) (P i) ⟨hw i, hv i⟩ (hval i)]

/-- **The zero section of the acting sheaf carries every lift to itself.**  Chartwise this is
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_zero`. -/
theorem isTranslateBy_zero (hG : IsThickening C S hS X' Z.1)
    {U' : SmallEtale C S hS X'.1}
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    IsTranslateBy C S hS hG (0 : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U'))
      β β := by
  intro V' m Q hQ hbase
  rw [liftActionSheafTransport_map_zero, Q.translateTransportSection_zero C S hS hG hQ]
  exact hbase.symm

/-- **The chartwise action is free**, read in the form the conclusion of
`AlgebraicGeometry.Space.IsChartTranslationCompatible` has at one presentation and the identity
morphism of charts: two sections of the acting sheaf with the same translate of the presented
lift have the same translate after adding `θ`.  This is the freeness of the chartwise action,
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_bijective`, and it
makes the instance of that predicate at `Q = P`, `m = 𝟙` hold — so what the predicate asserts
is not contradictory. -/
theorem translateTransportSection_add_of_eq {hG : IsThickening C S hS X' Z.1}
    {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')
    (hP : P.IsEtaleChartSquare C S hS)
    (θ η ζ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U'))
    (h : P.translateTransportSection C S hS hG hP.1 hP.2 η =
      P.translateTransportSection C S hS hG hP.1 hP.2 ζ) :
    P.translateTransportSection C S hS hG hP.1 hP.2 (θ + η) =
      P.translateTransportSection C S hS hG hP.1 hP.2 (θ + ζ) := by
  rw [(P.translateTransportSection_bijective C S hS hG hP.1 hP.2).1 h]

/-! ### The compatibility of the chartwise translations of two chart presentations -/

/-- **The chartwise translations of two chart presentations, one below the other, differ by a
translation.**

For `m : V' ⟶ U'`, a chart presentation `P` at `U'` and a chart presentation `Q` at `V'`, the two
chartwise actions
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection` are two simply
transitive actions of the sections of one and the same sheaf on the lifts over `V'` — of `P`
restricted along `m`, and of `Q`.  This says that the comparison of the two is a *translation*:
if `P`'s translate of its presented lift by `η` restricts to `Q`'s translate of its presented
lift by `ζ`, then `P`'s translate by `θ + η` restricts to `Q`'s translate by `θ|_{V'} + ζ`.

Two of its cases are the two compatibilities of the chart-level identification of the acting
group:

* at `m` a morphism of charts and `η = ζ = 0` — so that `P` and `Q` present the same lift over
  `V'` — it is the naturality in the chart of
  `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`, which for a presentation
  obtained by restricting `P` is
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`
  (whose decomposition into four comparisons is in that declaration's docstring);
* at `m = 𝟙` it is the independence of the chartwise action of the chart presentation: two chart
  presentations over one chart which present the same lift act in the same way.  What the
  comparison needs is the chart squares of `q` through which the two factor, which is the same
  family of four comparisons as the first case but along a morphism of chart squares of `q`
  rather than along a morphism of charts of `X'`.

At `Q = P` and `m = 𝟙` it holds trivially, and chart presentations exist on a covering family of
charts (`AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows`), so what it
asserts is not empty. -/
def IsChartTranslationCompatible (p : X' ⟶ Bb) (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) : Prop :=
  ∀ ⦃U' V' : SmallEtale C S hS X'.1⦄ (m : V' ⟶ U')
    (P : ChartLiftPresentation C S hS p q a.hom U')
    (hP : P.IsEtaleChartSquare C S hS)
    (Q : ChartLiftPresentation C S hS p q a.hom V')
    (hQ : Q.IsEtaleChartSquare C S hS)
    (θ η : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U'))
    (ζ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op V')),
    (liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op
        (P.translateTransportSection C S hS hG hP.1 hP.2 η) =
      Q.translateTransportSection C S hS hG hQ.1 hQ.2 ζ →
    (liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op
        (P.translateTransportSection C S hS hG hP.1 hP.2 (θ + η)) =
      Q.translateTransportSection C S hS hG hQ.1 hQ.2
        ((liftActionSheafTransport C S hS Z hG q a).obj.map m.op θ + ζ)

/-- **The chartwise translate is a translate in the sense of
`AlgebraicGeometry.Space.IsTranslateBy`**, granted the compatibility of the chartwise
translations: the translate of the presented lift of a chart presentation by `θ` is what `θ`
carries that presented lift to. -/
theorem isTranslateBy_translateTransportSection {hG : IsThickening C S hS X' Z.1}
    (hH : IsChartTranslationCompatible C S hS p Z hG q a)
    {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')
    (hP : P.IsEtaleChartSquare C S hS)
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    IsTranslateBy C S hS hG θ P.liftSection
      (P.translateTransportSection C S hS hG hP.1 hP.2 θ) := by
  intro V' m Q hQ hbase
  have hbase' : (liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op
        (P.translateTransportSection C S hS hG hP.1 hP.2 0) =
      Q.translateTransportSection C S hS hG hQ.1 hQ.2 0 := by
    rw [P.translateTransportSection_zero C S hS hG hP,
      Q.translateTransportSection_zero C S hS hG hQ]
    exact hbase.symm
  have h := hH m P hP Q hQ θ 0 0 hbase'
  simp only [add_zero] at h
  exact h

/-- **The translation relation is local on the chart.**  If, on a covering sieve of `U'`, the
restriction of `θ` carries the restriction of `β` to the restriction of `γ`, then `θ` carries `β`
to `γ` over `U'`.

The two sheaf conditions do the work: a chart carrying a chart presentation with presented lift
the restriction of `β` is covered by charts over which the relation is assumed, so the two
candidate translates agree there by
`AlgebraicGeometry.Space.isTranslateBy_translateTransportSection`, and
`Stacks.CategoryTheory.eq_of_locally_locally_eq` assembles that into an equality over the
chart. -/
theorem isTranslateBy_of_sieve (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    {θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U')}
    {β γ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')}
    {R : Sieve U'} (hR : R ∈ SmallEtale.topology C S hS X'.1 U')
    (h : ∀ ⦃V' : SmallEtale C S hS X'.1⦄ (f : V' ⟶ U'), R f →
      IsTranslateBy C S hS hX.isThickening
        ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map f.op θ)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map f.op β)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map f.op γ)) :
    IsTranslateBy C S hS hX.isThickening θ β γ := by
  intro W' m Q hQ hbase
  set tr := Q.translateTransportSection C S hS hX.isThickening hQ.1 hQ.2
    ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op θ) with htr
  have hQtr := isTranslateBy_translateTransportSection C S hS hH Q hQ
    ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op θ)
  rw [hbase, ← htr] at hQtr
  refine Stacks.CategoryTheory.eq_of_locally_locally_eq
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_liftsSubfunctor C S hS p q a.hom))
    ((SmallEtale.topology C S hS X'.1).pullback_stable m hR) ?_
  intro T n hn
  obtain ⟨I, W, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a.hom hX T
      ((liftsSubfunctor C S hS p q a.hom).toFunctor.map (n ≫ m).op β)
  have key : ∀ i, (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i ≫ n).op
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op γ) =
      (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i ≫ n).op tr := by
    intro i
    have hbaseP : (P i).liftSection =
        (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i ≫ n).op
          ((liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op β) := by
      rw [← liftsSubfunctor_map_comp_apply, Category.assoc, liftsSubfunctor_map_comp_apply]
      exact hval i
    have e2 := hQtr (r i ≫ n) (P i) ⟨hw i, hv i⟩ hbaseP
    have e1 := h (n ≫ m) hn (r i) (P i) ⟨hw i, hv i⟩ (hval i)
    rw [e2, ← liftsSubfunctor_map_comp_apply, Category.assoc,
      liftsSubfunctor_map_comp_apply, e1]
    refine congrArg _ ?_
    rw [← liftActionSheafTransport_map_comp_apply, ← liftActionSheafTransport_map_comp_apply,
      Category.assoc]
  refine ⟨Sieve.ofArrows W r, hcov, ?_⟩
  intro T₀ k hk
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  rw [Category.assoc, liftsSubfunctor_map_comp_apply C S hS p q a.hom g (r i ≫ n),
    liftsSubfunctor_map_comp_apply C S hS p q a.hom g (r i ≫ n), key i]

/-! ### Existence of the translate and of the translating section -/

/-- **The translate exists.**  Every section of the acting sheaf carries every lift over `U'` to
a lift over `U'`, granted the compatibility of the chartwise translations.

On a covering family of charts carrying a chart presentation with presented lift the restriction
of `β` the translate is the chartwise one; those local translates agree wherever two members of
the family are compared, because each of them is a translate in the sense of
`AlgebraicGeometry.Space.IsTranslateBy` and the translate is unique; and the sheaf of lifts
amalgamates them. -/
theorem exists_isTranslateBy (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    (θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    ∃ γ, IsTranslateBy C S hS hX.isThickening θ β γ := by
  obtain ⟨I, W, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a.hom hX U' β
  have claim : ∀ ⦃V' : SmallEtale C S hS X'.1⦄ (f : V' ⟶ U') (i : I) (g : V' ⟶ W i),
      g ≫ r i = f →
      IsTranslateBy C S hS hX.isThickening
        ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map f.op θ)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map f.op β)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map g.op
          ((P i).translateTransportSection C S hS hX.isThickening (hw i) (hv i)
            ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map (r i).op θ))) := by
    intro V' f i g hg
    have hb := isTranslateBy_translateTransportSection C S hS hH (P i) ⟨hw i, hv i⟩
      ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map (r i).op θ)
    rw [hval i] at hb
    have hres := hb.restrict C S hS g
    rwa [← liftActionSheafTransport_map_comp_apply, ← liftsSubfunctor_map_comp_apply, hg] at hres
  obtain ⟨γ, hγ⟩ := Stacks.CategoryTheory.exists_map_ofArrows_eq
    (isSheafFor_liftsSubfunctor C S hS p q a.hom hcov)
    (fun i => (P i).translateTransportSection C S hS hX.isThickening (hw i) (hv i)
      ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map (r i).op θ))
    (by
      intro i j T gi gj hsq
      exact eq_of_isTranslateBy C S hS hX (claim (gi ≫ r i) i gi rfl)
        (claim (gi ≫ r i) j gj hsq.symm))
  refine ⟨γ, isTranslateBy_of_sieve C S hS hX hH hcov ?_⟩
  intro V' f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  rw [liftsSubfunctor_map_comp_apply C S hS p q a.hom g (r i) γ, hγ i]
  exact claim (g ≫ r i) i g rfl

/-- **The translating section exists.**  For any two lifts `β` and `γ` over `U'` there is a
section of the acting sheaf carrying `β` to `γ`, granted the compatibility of the chartwise
translations.

Chartwise this is the transitivity of the chartwise action,
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_bijective`; the local
sections agree wherever two members of the covering family are compared, because the translating
section is unique, and the acting sheaf amalgamates them. -/
theorem exists_isTranslateBy_left (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    (β γ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    ∃ θ, IsTranslateBy C S hS hX.isThickening θ β γ := by
  obtain ⟨I, W, r, P, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a.hom hX U' β
  have hsurj : ∀ i, ∃ θ', (P i).translateTransportSection C S hS hX.isThickening (hw i) (hv i)
      θ' = (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i).op γ := fun i =>
    ((P i).translateTransportSection_bijective C S hS hX.isThickening (hw i) (hv i)).2 _
  choose θ' hθ' using hsurj
  have claim : ∀ ⦃V' : SmallEtale C S hS X'.1⦄ (f : V' ⟶ U') (i : I) (g : V' ⟶ W i),
      g ≫ r i = f →
      IsTranslateBy C S hS hX.isThickening
        ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map g.op (θ' i))
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map f.op β)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map f.op γ) := by
    intro V' f i g hg
    have hb := isTranslateBy_translateTransportSection C S hS hH (P i) ⟨hw i, hv i⟩ (θ' i)
    rw [hval i, hθ' i] at hb
    have hres := hb.restrict C S hS g
    rwa [← liftsSubfunctor_map_comp_apply, ← liftsSubfunctor_map_comp_apply, hg] at hres
  obtain ⟨θ, hθ⟩ := Stacks.CategoryTheory.exists_map_ofArrows_eq
    (isSheafFor_liftActionSheafTransport C S hS Z hX.isThickening q a hcov)
    θ' (by
      intro i j T gi gj hsq
      exact eq_of_isTranslateBy_left C S hS hX (claim (gi ≫ r i) i gi rfl)
        (claim (gi ≫ r i) j gj hsq.symm))
  refine ⟨θ, isTranslateBy_of_sieve C S hS hX hH hcov ?_⟩
  intro V' f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  rw [liftActionSheafTransport_map_comp_apply C S hS Z hX.isThickening q a g (r i) θ, hθ i]
  exact claim (g ≫ r i) i g rfl

/-! ### The sum of two translations -/

/-- **Translating by a sum is translating twice**, granted the compatibility of the chartwise
translations: if `η` carries `β` to `γ` and `θ` carries `γ` to `δ`, then `θ + η` carries `β` to
`δ`.

Chartwise this is the action law
`AlgebraicGeometry.Space.ChartLiftPresentation.translateHom_add`, in the form in which the
compatibility of the chartwise translations states it: over a chart presentation `Q` whose
presented lift is the restriction of `γ`, the translate of `β` by `θ + η` and the translate of
`γ` by `θ` are the same, and chart presentations with that presented lift exist on a covering
family. -/
theorem IsTranslateBy.add (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    {θ η : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U')}
    {β γ δ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')}
    (h₁ : IsTranslateBy C S hS hX.isThickening η β γ)
    (h₂ : IsTranslateBy C S hS hX.isThickening θ γ δ) :
    IsTranslateBy C S hS hX.isThickening (θ + η) β δ := by
  intro V' m P hP hbase
  have hγ := h₁ m P hP hbase
  obtain ⟨I, W, r, Q, hval, hw, hv, hcov⟩ :=
    exists_chartLiftPresentation_liftSection_ofArrows C S hS p q a.hom hX V'
      ((liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op γ)
  have key : ∀ i, (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i).op
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op δ) =
      (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i).op
        (P.translateTransportSection C S hS hX.isThickening hP.1 hP.2
          ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op (θ + η))) := by
    intro i
    have hQi : (Q i).IsEtaleChartSquare C S hS := ⟨hw i, hv i⟩
    have hbQ : (Q i).liftSection =
        (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i ≫ m).op γ := by
      rw [liftsSubfunctor_map_comp_apply]
      exact hval i
    have e2 := h₂ (r i ≫ m) (Q i) hQi hbQ
    have hhyp : (liftsSubfunctor C S hS p q a.hom).toFunctor.map (r i).op
          (P.translateTransportSection C S hS hX.isThickening hP.1 hP.2
            ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op η)) =
        (Q i).translateTransportSection C S hS hX.isThickening hQi.1 hQi.2 0 := by
      rw [(Q i).translateTransportSection_zero C S hS hX.isThickening hQi, hval i, hγ]
    have e3 := hH (r i) P hP (Q i) hQi
      ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op θ)
      ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op η) 0 hhyp
    rw [← liftsSubfunctor_map_comp_apply, e2, liftActionSheafTransport_map_add, e3, add_zero,
      ← liftActionSheafTransport_map_comp_apply]
  exact Stacks.CategoryTheory.eq_of_map_ofArrows_eq
    (isSeparatedFor_liftsSubfunctor C S hS p q a.hom hcov) key

/-! ### The global action on the sheaf of lifts -/

/-- **The action of a section of the acting sheaf on the sheaf of lifts, at an arbitrary object
of the small étale site of `X'`**, granted the compatibility of the chartwise translations: the
unique lift that `θ` carries `β` to.

Over a chart carrying a chart presentation with presented lift `β` it is the chartwise translate
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection`
(`AlgebraicGeometry.Space.eq_translateGlobalSection` at that presentation), but no such
presentation exists over an arbitrary chart, which is why the action is obtained by glueing. -/
noncomputable def translateGlobalSection (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    (θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U') :=
  (exists_isTranslateBy C S hS hX hH θ β).choose

/-- `AlgebraicGeometry.Space.translateGlobalSection` is what `θ` carries `β` to. -/
theorem isTranslateBy_translateGlobalSection (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    (θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    IsTranslateBy C S hS hX.isThickening θ β (translateGlobalSection C S hS hX hH θ β) :=
  (exists_isTranslateBy C S hS hX hH θ β).choose_spec

/-- **The global action is the only translate**: any lift that `θ` carries `β` to is
`AlgebraicGeometry.Space.translateGlobalSection`.  In particular it is the chartwise translate
over a chart presentation with presented lift `β`. -/
theorem eq_translateGlobalSection (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    {θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U')}
    {β γ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')}
    (h : IsTranslateBy C S hS hX.isThickening θ β γ) :
    γ = translateGlobalSection C S hS hX hH θ β :=
  eq_of_isTranslateBy C S hS hX h (isTranslateBy_translateGlobalSection C S hS hX hH θ β)

/-- **The zero section acts trivially.** -/
theorem translateGlobalSection_zero (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    translateGlobalSection C S hS hX hH
        (0 : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U')) β = β :=
  (eq_translateGlobalSection C S hS hX hH
    (isTranslateBy_zero C S hS hX.isThickening β)).symm

/-- **The action law**: translating by a sum is translating twice. -/
theorem translateGlobalSection_add (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    (θ η : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    translateGlobalSection C S hS hX hH (θ + η) β =
      translateGlobalSection C S hS hX hH θ (translateGlobalSection C S hS hX hH η β) :=
  (eq_translateGlobalSection C S hS hX hH
    ((isTranslateBy_translateGlobalSection C S hS hX hH η β).add C S hS hX hH
      (isTranslateBy_translateGlobalSection C S hS hX hH θ
        (translateGlobalSection C S hS hX hH η β)))).symm

/-- **The action is natural in the chart**: it commutes with the restriction maps of the two
sheaves.  This is the restriction-stability of the translation relation,
`AlgebraicGeometry.Space.IsTranslateBy.restrict`, together with the uniqueness of the
translate. -/
theorem translateGlobalSection_map (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    (liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op
        (translateGlobalSection C S hS hX hH θ β) =
      translateGlobalSection C S hS hX hH
        ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op θ)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op β) :=
  eq_translateGlobalSection C S hS hX hH
    ((isTranslateBy_translateGlobalSection C S hS hX hH θ β).restrict C S hS m)

/-- **The action is simply transitive at every object of the small étale site of `X'`**: for any
two lifts over `U'` there is a unique section of the acting sheaf carrying the first to the
second.  This is [Stacks Project, Tag 061C] with the covering family of chart presentations
eliminated. -/
theorem existsUnique_translateGlobalSection (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' : SmallEtale C S hS X'.1}
    (β γ : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')) :
    ∃! θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'),
      translateGlobalSection C S hS hX hH θ β = γ := by
  obtain ⟨θ, hθ⟩ := exists_isTranslateBy_left C S hS hX hH β γ
  refine ⟨θ, (eq_translateGlobalSection C S hS hX hH hθ).symm, fun θ' hθ' => ?_⟩
  refine eq_of_isTranslateBy_left C S hS hX ?_ hθ
  rw [← hθ']
  exact isTranslateBy_translateGlobalSection C S hS hX hH θ' β

/-! ### The pseudo-torsor -/

/-- **The action of the acting sheaf of groups on the sheaf of lifts**, as the `act` field of
`PseudoTorsor` asks for it: on the universe lift of the sheaf of lifts, which is where the two
sheaves have sections in one universe.  It is
`AlgebraicGeometry.Space.translateGlobalSection` read through that universe lift. -/
noncomputable def liftTorsorAct (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    (U' : SmallEtale C S hS X'.1)
    (θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U')) :
    (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U') :=
  ULift.up (translateGlobalSection C S hS hX hH θ β.down)

/-- `AlgebraicGeometry.Space.liftTorsorAct` is the universe lift of
`AlgebraicGeometry.Space.translateGlobalSection`, by `rfl`. -/
theorem liftTorsorAct_eq (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    (U' : SmallEtale C S hS X'.1)
    (θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U')) :
    liftTorsorAct C S hS hX hH U' θ β =
      ULift.up (translateGlobalSection C S hS hX hH θ β.down) :=
  rfl

/-- **The identity section acts trivially**, which is the `one_act` field of `PseudoTorsor`: the
unit of the group law of `AlgebraicGeometry.Space.liftActionSheafOfGroups` is the zero section of
the acting sheaf (`AlgebraicGeometry.Space.liftActionSheafTransport_one_eq_zero`). -/
theorem liftTorsorAct_one (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    (U' : SmallEtale C S hS X'.1)
    (β : (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U')) :
    liftTorsorAct C S hS hX hH U' 1 β = β := by
  rw [liftTorsorAct_eq, liftActionSheafTransport_one_eq_zero,
    translateGlobalSection_zero C S hS hX hH β.down]
  rfl

/-- **The action is compatible with multiplication in the acting sheaf of groups**, which is the
`mul_act` field of `PseudoTorsor`: the group law is the addition of the acting sheaf's sections
(`AlgebraicGeometry.Space.liftActionSheafTransport_mul_eq_add`) and
`AlgebraicGeometry.Space.translateGlobalSection_add` is the action law for that addition. -/
theorem liftTorsorAct_mul (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    (U' : SmallEtale C S hS X'.1)
    (θ η : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U')) :
    liftTorsorAct C S hS hX hH U' (θ * η) β =
      liftTorsorAct C S hS hX hH U' θ (liftTorsorAct C S hS hX hH U' η β) := by
  rw [liftTorsorAct_eq, liftTorsorAct_eq, liftTorsorAct_eq,
    liftActionSheafTransport_mul_eq_add]
  exact congrArg ULift.up (translateGlobalSection_add C S hS hX hH θ η β.down)

/-- **The action is natural with respect to the restriction maps**, which is the `naturality`
field of `PseudoTorsor`.  The restriction maps of the universe lift of the sheaf of lifts are
those of the sheaf of lifts (`AlgebraicGeometry.Space.liftsSubfunctorULift_map_up`), so this is
`AlgebraicGeometry.Space.translateGlobalSection_map`. -/
theorem liftTorsorAct_map (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    {U' V' : SmallEtale C S hS X'.1} (m : V' ⟶ U')
    (θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'))
    (β : (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U')) :
    (liftsSubfunctorULift C S hS p q a.hom).obj.map m.op
        (liftTorsorAct C S hS hX hH U' θ β) =
      liftTorsorAct C S hS hX hH V'
        ((liftActionSheafTransport C S hS Z hX.isThickening q a).obj.map m.op θ)
        ((liftsSubfunctorULift C S hS p q a.hom).obj.map m.op β) := by
  rw [liftTorsorAct_eq, liftsSubfunctorULift_map_up, liftTorsorAct_eq]
  exact congrArg ULift.up (translateGlobalSection_map C S hS hX hH m θ β.down)

/-- **The action is simply transitive on every set of sections**, which is the
`simplyTransitive` field of `PseudoTorsor` — and it holds at every object, with no nonemptiness
hypothesis, since the two sections are given.  This is
`AlgebraicGeometry.Space.existsUnique_translateGlobalSection`. -/
theorem existsUnique_liftTorsorAct (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a)
    (U' : SmallEtale C S hS X'.1)
    (s t : (liftsSubfunctorULift C S hS p q a.hom).obj.obj (op U')) :
    ∃! θ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U'),
      liftTorsorAct C S hS hX hH U' θ s = t := by
  obtain ⟨θ, hθ, huniq⟩ := existsUnique_translateGlobalSection C S hS hX hH s.down t.down
  refine ⟨θ, ?_, fun θ' hθ' => huniq θ' (congrArg ULift.down hθ')⟩
  show liftTorsorAct C S hS hX hH U' θ s = t
  rw [liftTorsorAct_eq, hθ]
  rfl

/-- **[Stacks Project, Tag 061C] for a first-order thickening: the sheaf of lifts is a pseudo
torsor under the acting sheaf of [Stacks Project, Tag 061D]**, granted
`AlgebraicGeometry.Space.IsChartTranslationCompatible`.

Every field is one of the declarations above applied verbatim: the two sheaves are
`AlgebraicGeometry.Space.liftsSubfunctorULift` and
`AlgebraicGeometry.Space.liftActionSheafOfGroups`, which put [Stacks Project, Tag 061D]'s two
sheaves on one site at one universe, and the action and its three laws are
`AlgebraicGeometry.Space.liftTorsorAct`, `AlgebraicGeometry.Space.liftTorsorAct_one`,
`AlgebraicGeometry.Space.liftTorsorAct_mul` and `AlgebraicGeometry.Space.liftTorsorAct_map`,
with `AlgebraicGeometry.Space.existsUnique_liftTorsorAct` for the simple transitivity.

What the hypothesis `hH` asserts, together with the two compatibilities of the chart-level
identification of the acting group that it specialises to, is in the docstring of
`AlgebraicGeometry.Space.IsChartTranslationCompatible`.  Everything else here is unconditional:
in particular the uniqueness of the translate and of the translating section
(`AlgebraicGeometry.Space.eq_of_isTranslateBy` and
`AlgebraicGeometry.Space.eq_of_isTranslateBy_left`), the locality of the translation relation
and the zero law carry nothing beyond the first-order thickening. -/
noncomputable def liftPseudoTorsor (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a) :
    PseudoTorsor (liftActionSheafOfGroups C S hS Z hX.isThickening q a) where
  presheaf := (liftsSubfunctorULift C S hS p q a.hom).obj
  isSheaf := (liftsSubfunctorULift C S hS p q a.hom).property
  act U θ β := liftTorsorAct C S hS hX hH U.unop θ β
  one_act U s := liftTorsorAct_one C S hS hX hH U.unop s
  mul_act U θ η s := liftTorsorAct_mul C S hS hX hH U.unop θ η s
  naturality f θ s := liftTorsorAct_map C S hS hX hH f.unop θ s
  simplyTransitive U _ s t := existsUnique_liftTorsorAct C S hS hX hH U.unop s t

/-! ### The presented chart against the base-changed chart, naturally in the chart -/

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')

/-- The morphism of presheaves underlying
`AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso` is the comparison of the two
pullbacks that it is built from. -/
theorem yoneda_map_subEtaleChartIso_hom (hG : IsThickening C S hS X' Z.1) :
    yoneda.map ((P.subEtaleChartIso C S hS hG).hom.hom.left) =
      (P.isPullback.flip.isoIsPullback _ _
        ((isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.isPullback U'.1.hom)).hom :=
  yoneda.map_preimage _

/-- The chart morphism of `AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`: the
comparison of the presented chart with the base-changed chart commutes with the two chart
morphisms into the closed subspace. -/
theorem subEtaleChartIso_hom_comp_fst (hG : IsThickening C S hS X' Z.1) :
    yoneda.map ((P.subEtaleChartIso C S hS hG).hom.hom.left) ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.fst U'.1.hom =
      P.subChart := by
  rw [P.yoneda_map_subEtaleChartIso_hom C S hS hG]
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The ambient morphism of `AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`:
the comparison of the presented chart with the base-changed chart commutes with the two
inclusions into the ambient chart. -/
theorem subEtaleChartIso_hom_comp_snd (hG : IsThickening C S hS X' Z.1) :
    (P.subEtaleChartIso C S hS hG).hom.hom.left ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.snd U'.1.hom =
      P.incl :=
  yoneda.map_injective ((yoneda.map_comp _ _).trans (by
    rw [P.yoneda_map_subEtaleChartIso_hom C S hS hG]
    exact IsPullback.isoIsPullback_hom_snd _ _ _ _))

/-- **The comparison of the presented chart with the base-changed chart is natural in the
chart.**  For a restriction datum `R` of `P` along `m : V' ⟶ U'`, the square formed by the two
comparisons of `AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`, the morphism of
presented charts
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subEtaleChartMap` and the base change
of `m` commutes.

Everything in sight is a morphism into the base change of `U'`, which is a fibre product, so the
square is checked on its two projections: on the chart morphism into the closed subspace by
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap_comp_subChart` and the triangle
of a morphism of charts, and on the inclusion into the ambient chart by
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap_comp_incl` and
`AlgebraicGeometry.Space.smallBaseChange_map_snd`. -/
theorem subEtaleChartMap_comp_subEtaleChartIso_hom (hG : IsThickening C S hS X' Z.1)
    {V' : SmallEtale C S hS X'.1} (R : P.Restriction V') :
    R.subEtaleChartMap (Z := Z) (a := a) ≫ (P.subEtaleChartIso C S hS hG).hom =
      (R.presentation.subEtaleChartIso C S hS hG).hom ≫
        (thickeningChartBaseChange C S hS hG).map R.chartMap := by
  have hw : yoneda.map (((thickeningChartBaseChange C S hS hG).map R.chartMap).hom.left) ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.fst U'.1.hom =
      (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.fst V'.1.hom :=
    CostructuredArrow.w _
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
  refine (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.hom_ext ?_ ?_
  · show yoneda.map (R.subMap ≫ (P.subEtaleChartIso C S hS hG).hom.hom.left) ≫ _ =
      yoneda.map ((R.presentation.subEtaleChartIso C S hS hG).hom.hom.left ≫
        ((thickeningChartBaseChange C S hS hG).map R.chartMap).hom.left) ≫ _
    rw [Functor.map_comp, Functor.map_comp]
    have e1 : (yoneda.map R.subMap ≫
          yoneda.map ((P.subEtaleChartIso C S hS hG).hom.hom.left)) ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.fst U'.1.hom =
      R.subChart :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => yoneda.map R.subMap ≫ z)
          (P.subEtaleChartIso_hom_comp_fst C S hS hG)).trans R.subMap_comp_subChart)
    have e2 : (yoneda.map ((R.presentation.subEtaleChartIso C S hS hG).hom.hom.left) ≫
          yoneda.map (((thickeningChartBaseChange C S hS hG).map R.chartMap).hom.left)) ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.fst U'.1.hom =
      R.subChart :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z =>
            yoneda.map ((R.presentation.subEtaleChartIso C S hS hG).hom.hom.left) ≫ z) hw).trans
          (R.presentation.subEtaleChartIso_hom_comp_fst C S hS hG))
    exact e1.trans e2.symm
  · show (R.subMap ≫ (P.subEtaleChartIso C S hS hG).hom.hom.left) ≫ _ =
      ((R.presentation.subEtaleChartIso C S hS hG).hom.hom.left ≫
        ((thickeningChartBaseChange C S hS hG).map R.chartMap).hom.left) ≫ _
    have f1 : (R.subMap ≫ (P.subEtaleChartIso C S hS hG).hom.hom.left) ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.snd U'.1.hom =
      R.incl ≫ R.ambientMap :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => R.subMap ≫ z) (P.subEtaleChartIso_hom_comp_snd C S hS hG)).trans
          R.subMap_comp_incl)
    have f2 : ((R.presentation.subEtaleChartIso C S hS hG).hom.hom.left ≫
          ((thickeningChartBaseChange C S hS hG).map R.chartMap).hom.left) ≫
        (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep.snd U'.1.hom =
      R.incl ≫ R.ambientMap :=
      (Category.assoc _ _ _).trans
        (((congrArg (fun z => (R.presentation.subEtaleChartIso C S hS hG).hom.hom.left ≫ z)
              (smallBaseChange_map_snd C S hS (IsThickening.inclusion C S hS hG)
                (isClosedImmersion_inclusion_of_isThickening C S hS hG).rep R.chartMap)).trans
            (Category.assoc _ _ _).symm).trans
          (congrArg (fun z => z ≫ R.chartMap.hom.left)
            (R.presentation.subEtaleChartIso_hom_comp_snd C S hS hG)))
    exact f1.trans f2.symm

/-- The chartwise translation is the chartwise action at the acting section the transported
identification attaches to a section of the transported acting sheaf, by `rfl`.  It is named
because `rw` cannot unfold a definition and every statement below has to be brought to this
spelling syntactically. -/
theorem translateTransportSection_eq (hG : IsThickening C S hS X' Z.1)
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    P.translateTransportSection C S hS hG hw hv θ =
      P.translateActionSection (P.transportActionSectionEquiv C S hS hG hw hv θ) :=
  rfl

/-- The transported identification of the acting group is the identification at the presented
chart composed with the restriction map of the acting sheaf along the comparison
`AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`, by `rfl`. -/
theorem transportActionSectionEquiv_eq
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (hG : IsThickening C S hS X' Z.1)
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    P.transportActionSectionEquiv C S hS hG hw hv θ =
      actionSectionEquiv C S hS P hw hv
        ((liftActionSheaf C S hS Z q a).val.map
          (P.subEtaleChartIso C S hS hG).hom.op θ) :=
  rfl

end ChartLiftPresentation

/-! ### Reducing the compatibility to the two chart compatibilities -/

/-- **The naturality in the chart of the identification of the acting group, at every chart
presentation and every restriction datum.**  This is the ∀-form of the predicate
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`;
the ∀ adds nothing to it, since that predicate carries no
hypothesis beyond the presentation, its restriction datum and the étaleness of the two charts of
`q`. -/
def IsActionSectionRestrictionNaturalEverywhere (p : X' ⟶ Bb)
    (Z : ClosedSubspaces C S hS X'.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) : Prop :=
  ∀ ⦃U' V' : SmallEtale C S hS X'.1⦄ (P : ChartLiftPresentation C S hS p q a.hom U')
    (hP : P.IsEtaleChartSquare C S hS) (R : P.Restriction V'),
    R.IsActionSectionRestrictionNatural (Z := Z) (a := a) hP.1 hP.2

/-- **The chartwise action does not depend on the chart presentation.**  Two chart presentations
over one and the same chart `V'` whose translates of their presented lifts by `η` and `ζ` agree
translate by `θ + η` and `θ + ζ` to the same lift.

This is `AlgebraicGeometry.Space.IsChartTranslationCompatible` at `m = 𝟙`, and it is the half of
that compatibility which the naturality in the chart does **not** give: a covering family of
chart presentations has a *different* affine chart square of `q` at each member
(`AlgebraicGeometry.Space.exists_affine_chartSquare_hom_ofArrows` produces the squares `W i ⟶ V i`
indexed by the member), while
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` keeps the chart square of `q` fixed —
its `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.presentation` has the `tgt`, `bse`,
`tgtChart`, `bseChart`, `chartHom` and `chartSq` of the presentation it restricts.  So on an
overlap of two members the two restricted presentations differ in the chart square of `q`.

What such a comparison needs is the same family of four comparisons as the naturality in the
chart — [Stacks Project, Tag 04M0] with Equation [Stacks Project, Tag 03LW], the source square of
[Stacks Project, Tag 04CU] after [Stacks Project, Tag 04CS], and the target square of
[Stacks Project, Tag 03LU], [Stacks Project, Tag 04CO] and [Stacks Project, Tag 04G2] (1) — but
along a morphism of chart squares of `q` rather than along a morphism of charts of `X'`. -/
def IsChartActionPresentationIndependent (p : X' ⟶ Bb) (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) : Prop :=
  ∀ ⦃V' : SmallEtale C S hS X'.1⦄
    (P₁ : ChartLiftPresentation C S hS p q a.hom V') (hP₁ : P₁.IsEtaleChartSquare C S hS)
    (P₂ : ChartLiftPresentation C S hS p q a.hom V') (hP₂ : P₂.IsEtaleChartSquare C S hS)
    (θ η ζ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op V')),
    P₁.translateTransportSection C S hS hG hP₁.1 hP₁.2 η =
        P₂.translateTransportSection C S hS hG hP₂.1 hP₂.2 ζ →
      P₁.translateTransportSection C S hS hG hP₁.1 hP₁.2 (θ + η) =
        P₂.translateTransportSection C S hS hG hP₂.1 hP₂.2 (θ + ζ)

/-- The naturality square of
`AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartMap_comp_subEtaleChartIso_hom`, read
in the opposite category, which is where a restriction map of the acting sheaf is indexed. -/
theorem subEtaleChartIso_hom_op_naturality (hG : IsThickening C S hS X' Z.1)
    {U' V' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')
    (R : P.Restriction V') :
    (P.subEtaleChartIso C S hS hG).hom.op ≫ (R.subEtaleChartMap (Z := Z) (a := a)).op =
      ((thickeningChartBaseChange C S hS hG).map R.chartMap).op ≫
        (R.presentation.subEtaleChartIso C S hS hG).hom.op :=
  op_comp.symm.trans ((congrArg Quiver.Hom.op
    (P.subEtaleChartMap_comp_subEtaleChartIso_hom C S hS hG R)).trans op_comp)

/-- **The restriction maps of the acting sheaf commute with the comparison of the presented chart
with the base-changed chart.**  This is
`AlgebraicGeometry.Space.subEtaleChartIso_hom_op_naturality` read on sections, which is
functoriality of the acting sheaf and nothing else. -/
theorem liftActionSheaf_map_subEtaleChartIso_naturality (hG : IsThickening C S hS X' Z.1)
    {U' V' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')
    (R : P.Restriction V')
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    (liftActionSheaf C S hS Z q a).val.map (R.subEtaleChartMap (Z := Z) (a := a)).op
        ((liftActionSheaf C S hS Z q a).val.map (P.subEtaleChartIso C S hS hG).hom.op θ) =
      (liftActionSheaf C S hS Z q a).val.map (R.presentation.subEtaleChartIso C S hS hG).hom.op
        ((liftActionSheafTransport C S hS Z hG q a).obj.map R.chartMap.op θ) :=
  (((liftActionSheaf C S hS Z q a).val.map_comp_apply
        (P.subEtaleChartIso C S hS hG).hom.op
        (R.subEtaleChartMap (Z := Z) (a := a)).op θ).symm.trans
      ((liftActionSheaf C S hS Z q a).val.congr_map_apply
        (subEtaleChartIso_hom_op_naturality C S hS hG P R) θ)).trans
    ((liftActionSheaf C S hS Z q a).val.map_comp_apply
      ((thickeningChartBaseChange C S hS hG).map R.chartMap).op
      (R.presentation.subEtaleChartIso C S hS hG).hom.op θ)

/-! ### Reducing the compatibility to those two

`AlgebraicGeometry.Space.IsChartTranslationCompatible` **is** implied by
`AlgebraicGeometry.Space.IsActionSectionRestrictionNaturalEverywhere` together with
`AlgebraicGeometry.Space.IsChartActionPresentationIndependent`, and that implication is proved
here.  A restriction datum along the morphism of charts exists because the smaller chart carries
a chart presentation and is therefore affine
(`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.exists_of_isFirstOrderThickening`);
the naturality carries the restriction of `P`'s translate to the translate of the restricted
presentation, through
`ChartLiftPresentation.Restriction.map_translateActionSection_actionSectionEquiv` and the chart
comparison
`AlgebraicGeometry.Space.liftActionSheaf_map_subEtaleChartIso_naturality` proved above; and the
independence then compares the restricted presentation with the given one over the smaller
chart.

The acting section is never written out: the three `rfl` bridges
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_eq`,
`AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv_eq` and
`AlgebraicGeometry.Space.liftActionSheafTransport_map_eq` put both sides in the acting sheaf's
own spelling, the chart comparison is rewritten backwards so that both sides read the section at
the presented chart, and `map_translateActionSection_actionSectionEquiv` closes the goal at that
section.  Rewriting the goal into the naturality predicate's own spelling instead is too
expensive to elaborate.
-/

/-- **The chartwise action commutes with restriction to a smaller chart**, granted the naturality
in the chart of the identification of the acting group: restricting the translate of the presented
lift of `P` by a section `θ` of the transported acting sheaf gives the translate, by the
restriction of `θ`, of the lift presented by the restricted presentation.

This is
`ChartLiftPresentation.Restriction.map_translateActionSection_actionSectionEquiv` of
`AlgebraicGeometry.Space`
read at the transported acting sheaf, which is the sheaf the glueing acts by: both sides are
indexed by charts of `X'` rather than by the charts of `X` the presentations present. -/
theorem map_translateTransportSection_of_isActionSectionRestrictionNatural
    {hG : IsThickening C S hS X' Z.1} {U' V' : SmallEtale C S hS X'.1}
    (P : ChartLiftPresentation C S hS p q a.hom U') (hP : P.IsEtaleChartSquare C S hS)
    (R : P.Restriction V')
    (hnat : R.IsActionSectionRestrictionNatural (Z := Z) (a := a) hP.1 hP.2)
    (θ : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')) :
    (liftsSubfunctor C S hS p q a.hom).toFunctor.map R.chartMap.op
        (P.translateTransportSection C S hS hG hP.1 hP.2 θ) =
      R.presentation.translateTransportSection C S hS hG hP.1 hP.2
        ((liftActionSheafTransport C S hS Z hG q a).obj.map R.chartMap.op θ) := by
  rw [ChartLiftPresentation.translateTransportSection_eq,
    ChartLiftPresentation.translateTransportSection_eq,
    ChartLiftPresentation.transportActionSectionEquiv_eq,
    ChartLiftPresentation.transportActionSectionEquiv_eq,
    ← liftActionSheaf_map_subEtaleChartIso_naturality C S hS hG P R θ]
  exact R.map_translateActionSection_actionSectionEquiv hP.1 hP.2 hnat _

/-- **The compatibility of the chartwise translations follows from the naturality in the chart of
the identification of the acting group together with the independence of the chartwise action of
the chart presentation.**  So `AlgebraicGeometry.Space.IsChartTranslationCompatible`, the
hypothesis of the glueing, is a conjunction of two statements each about a single comparison.

Given a morphism `m : V' ⟶ U'` of charts, a presentation `P` at `U'` and a presentation `Q` at
`V'`, the smaller chart is affine because `Q` presents it, so `P` restricts along `m`; the
naturality identifies the restriction of each of `P`'s translates with a translate of the
restricted presentation, by
`AlgebraicGeometry.Space.map_translateTransportSection_of_isActionSectionRestrictionNatural`; and
the independence then compares the restricted presentation with `Q` over `V'`, both presentations
now living over one chart. Additivity of the restriction maps of the acting sheaf,
`AlgebraicGeometry.Space.liftActionSheafTransport_map_add`, matches the two spellings of the
translating section. -/
theorem isChartTranslationCompatible_of_natural_of_presentationIndependent
    (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hnat : IsActionSectionRestrictionNaturalEverywhere C S hS p Z q a)
    (hindep : IsChartActionPresentationIndependent C S hS p Z hX.isThickening q a) :
    IsChartTranslationCompatible C S hS p Z hX.isThickening q a := by
  intro U' V' m P hP Q hQ θ η ζ h
  obtain ⟨R, hR⟩ :=
    ChartLiftPresentation.Restriction.exists_of_isFirstOrderThickening P hX m
      Q.isAffineAmbient
  subst hR
  have key := fun (σ : (liftActionSheafTransport C S hS Z hX.isThickening q a).obj.obj (op U')) =>
    map_translateTransportSection_of_isActionSectionRestrictionNatural C S hS P hP R
      (hnat P hP R) σ
  rw [key η] at h
  rw [key (θ + η), liftActionSheafTransport_map_add]
  exact hindep R.presentation hP Q hQ _ _ ζ h

end AlgebraicGeometry.Space

end
