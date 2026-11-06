module

public import StacksFrontier.Algebra.TranslationDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing

/-!
# A chart-free difference of lifts gives the compatibility of the chartwise translations

Let `X ⊆ X'` be a closed subspace of an algebraic space over a scheme `S` contained in a big
fppf site `C`, let `q : Y ⟶ Bb` be a morphism of algebraic spaces and let `a : X ⟶ Y` be a
morphism over `Bb`.  The chartwise action of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` translates the lift
presented by a chart presentation `P` at a chart `U'` of `X'` by a section of the acting sheaf
over `U'`, and the glueing of those chartwise actions into an action of sheaves at every object
of the small étale site of `X'`, which
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing` carries out, is conditional
on the one predicate
`AlgebraicGeometry.Space.IsChartTranslationCompatible`: the chartwise translations of two chart
presentations, one below the other, differ by a translation.

This file discharges that predicate from a **difference of two lifts which refers to no chart
presentation**.  Such a difference is a family of maps

`D U' : lifts over U' → lifts over U' → sections of the acting sheaf over U'`,

and what is asked of it is exactly two things: that it recover the acting section from a pair of
translates of one chart presentation
(`AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate`), and that it commute with the
restriction maps of the two sheaves
(`AlgebraicGeometry.Space.IsLiftDifferenceRestrictionNatural`).  Neither mentions two chart
presentations, so a difference defined without reference to a chart — as
`AlgebraicGeometry.Space.liftPairGlobalSection` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairActionSection` is — has a chance of
satisfying both, and `AlgebraicGeometry.Space.isChartTranslationCompatible_of_liftDifference`
turns that into the predicate.

## Main definitions

* `AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate`: the difference recovers the acting
  section from a pair of translates of one chart presentation.
* `AlgebraicGeometry.Space.IsLiftDifferenceRestrictionNatural`: the difference commutes with the
  restriction maps of the sheaf of lifts and of the transported acting sheaf.

## Main results

* `AlgebraicGeometry.Space.isChartTranslationCompatible_of_liftDifference`: **a chart-free
  difference with those two properties discharges
  `AlgebraicGeometry.Space.IsChartTranslationCompatible`**, and with it
  `AlgebraicGeometry.Space.isChartActionPresentationIndependent_of_liftDifference`, the half of
  its reduction which was open for want of any comparison of two chart presentations over one
  chart.
* `AlgebraicGeometry.Space.exists_liftDifference_of_isChartTranslationCompatible`: the
  **converse**, so the two hypotheses are equivalent to the predicate they discharge — they are
  neither a weakening of it nor empty.
* `AlgebraicGeometry.Space.isLiftDifferenceOfTranslate_of_chartSubtraction`: the translate
  property **at an arbitrary base point** from a chartwise subtraction, and
  `AlgebraicGeometry.Space.chartSubtraction_of_isLiftDifferenceOfTranslate` its converse, so
  that reformulation is again neither a weakening nor empty.

**This bypasses the reduction** of that predicate to
`AlgebraicGeometry.Space.IsActionSectionRestrictionNaturalEverywhere` together with
`AlgebraicGeometry.Space.IsChartActionPresentationIndependent`, which is what
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing` had reduced it to and
which that file records as itself unproved, its last step being a heartbeat wall.  Neither of
those two predicates is used or needed here: the predicate the glueing consumes — the `hH` of
`AlgebraicGeometry.Space.isTranslateBy_translateTransportSection` and of everything after it —
is proved directly.

## Implementation notes

**The whole proof is `Stacks.eq_translate_add_of_difference`**, which is stated in
`StacksFrontier.Algebra.TranslationDifference` with every datum a variable and no geometry at all:
two abelian groups, four maps, two differences, three equations.  Nothing of the lifting problem
enters its proof, and the three declarations here are its instantiations.  That placement is
deliberate — the elaboration walls recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing` are all conversions between
two elaborations of a statement about a *concrete* chart presentation, and a generic lemma
applied to variables never asks the kernel for one.

**What is asked of the difference is its value at a pair of translates of an arbitrary acting
section, not at the presented lift and one translate.**  The reading "the difference of the
presented lift and its translate by `θ` is `θ`" is the case `η = 0` of
`AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate`, by
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_zero`.  The case
`η = 0` on its own does not suffice, and the reason is in the predicate being discharged: it
compares a translate over `U'` restricted to `V'` with a translate over `V'`, and those are
translates of two *different* lifts — the restriction of `P`'s presented lift and `Q`'s — so a
hypothesis about the presented lift alone never reaches the second one.  Granted that a chart
presentation can be moved along the action to present any of its own translates, the general
case follows from the case `η = 0`; that is a property of the family of chart presentations and
is not assumed here.

**That passage is not the only route to the general case, and the other one is cheaper.**  Moving
the base point is not free: re-basing a presentation replaces its
`AlgebraicGeometry.Space.ChartLiftPresentation.liftHom`, and
`AlgebraicGeometry.Space.ChartLiftPresentation.redHomScheme` carries that field, so the type
`AlgebraicGeometry.Space.ChartLiftPresentation.Deriv` of the re-based presentation is only
equal to the original's after a rewrite.  A difference whose chart value is a **subtraction** of
acting sections needs none of it: a subtraction is base-point-free, and
`AlgebraicGeometry.Space.isLiftDifferenceOfTranslate_of_chartSubtraction` gets the arbitrary `η`
from `Stacks.eq_of_difference_translate` and the additivity of the chart identification alone.
That is the shape a difference of two structure maps has, by
`AlgebraicGeometry.Space.ChartLiftPresentation.liftDiffDerivation_translate_translate`.

**No additivity of the restriction maps is used**, and neither is the freeness of the chartwise
action: of `AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_bijective`
only the surjectivity is taken.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 061C] asserts the pseudo-torsor
property unconditionally and what is proved here is an implication between two hypotheses of it;
the tag stays where
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing` has it.

## References

* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}
variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}

/-! ### What is asked of a chart-free difference -/

/-- **A candidate difference of two lifts**: a family of maps attaching to two sections of the
sheaf of lifts over a chart `U'` of `X'` a section of the transported acting sheaf over `U'`.

This is only the shape; the two properties which make such a family a difference are
`AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate` and
`AlgebraicGeometry.Space.IsLiftDifferenceRestrictionNatural`. -/
abbrev LiftDifferenceFamily (p : X' ⟶ Bb) (Z : ClosedSubspaces C S hS X'.1)
    (hG : IsThickening C S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y) :=
  ∀ U' : SmallEtale C S hS X'.1,
    (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U') →
      (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U') →
        (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')

/-- **The difference recovers the acting section from a pair of translates of one chart
presentation.**  For a chart presentation `P` at `U'` whose two charts of `q` are étale, the
difference of `P`'s translate of its presented lift by `η` and `P`'s translate by `θ + η` is
`θ`.

The case `η = 0` says that the difference of the presented lift and its translate by `θ` is
`θ`, by `AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_zero`; the
general case is what the compatibility of two chart presentations needs, and the module
documentation says why. -/
def IsLiftDifferenceOfTranslate {hG : IsThickening C S hS X' Z.1}
    (D : LiftDifferenceFamily C S hS p Z hG q a) : Prop :=
  ∀ ⦃U' : SmallEtale C S hS X'.1⦄ (P : ChartLiftPresentation C S hS p q a.hom U')
    (hP : P.IsEtaleChartSquare C S hS)
    (θ η : (liftActionSheafTransport C S hS Z hG q a).obj.obj (op U')),
    D U' (P.translateTransportSection C S hS hG hP.1 hP.2 η)
        (P.translateTransportSection C S hS hG hP.1 hP.2 (θ + η)) = θ

/-- **The difference commutes with restriction.**  Restricting two lifts over `U'` to a chart
`V'` below it and taking their difference there is restricting their difference over `U'`.

This is the naturality in the chart of a difference which is defined chart by chart; for a
difference defined with no reference to a chart at all it is the statement that the definition
commutes with étale localization of `X'`. -/
def IsLiftDifferenceRestrictionNatural {hG : IsThickening C S hS X' Z.1}
    (D : LiftDifferenceFamily C S hS p Z hG q a) : Prop :=
  ∀ ⦃U' V' : SmallEtale C S hS X'.1⦄ (m : V' ⟶ U')
    (x y : (liftsSubfunctor C S hS p q a.hom).toFunctor.obj (op U')),
    D V' ((liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op x)
        ((liftsSubfunctor C S hS p q a.hom).toFunctor.map m.op y) =
      (liftActionSheafTransport C S hS Z hG q a).obj.map m.op (D U' x y)

/-! ### The translate property from a chartwise subtraction -/

/-- **A difference computed chartwise by subtraction of acting sections satisfies
`AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate`** — at an *arbitrary* base point, and with
no re-basing of the chart presentation.

What is asked for here is the value of the difference at a pair of translates of one
presentation, read through the chart identification
`AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv`: it is the
subtraction of the two acting sections.  That is exactly what a difference of two lifts computed
from the difference of their structure maps gives, because
`AlgebraicGeometry.Space.ChartLiftPresentation.liftDiffDerivation_translate_translate` says the
difference of the structure maps of two translates of one presentation is the difference of the
two translating derivations, and
`AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection_bijective` turns a
derivation back into an acting section.

The whole proof is `Stacks.eq_of_difference_translate`, whose two inputs are the additivity and
the injectivity of the chart identification
(`AlgebraicGeometry.Space.ChartLiftPresentation.transportActionSectionEquiv_add`).  Nothing
about the family of chart presentations is used, and that is the point: **the base point is
arbitrary at no cost**, because a subtraction is base-point-free.  The closure of the family of
chart presentations under moving the base point along the action — the property the module
documentation describes as what a passage from the case `η = 0` would need, and which is not
free, since re-basing a presentation changes
`AlgebraicGeometry.Space.ChartLiftPresentation.redHomScheme` and with it the type
`AlgebraicGeometry.Space.ChartLiftPresentation.Deriv` — is **not** required on this route. -/
theorem isLiftDifferenceOfTranslate_of_chartSubtraction {hG : IsThickening C S hS X' Z.1}
    (D : LiftDifferenceFamily C S hS p Z hG q a)
    (hD : ∀ ⦃U' : SmallEtale C S hS X'.1⦄ (P : ChartLiftPresentation C S hS p q a.hom U')
      (hP : P.IsEtaleChartSquare C S hS) (σ₁ σ₂ : P.ActionSection),
      P.transportActionSectionEquiv C S hS hG hP.1 hP.2
          (D U' (P.translateActionSection σ₁) (P.translateActionSection σ₂)) = σ₂ - σ₁) :
    IsLiftDifferenceOfTranslate C S hS D := by
  intro U' P hP θ η
  exact Stacks.eq_of_difference_translate (P.transportActionSectionEquiv_add C S hS hG hP)
    (hD P hP) (P.transportActionSectionEquiv C S hS hG hP.1 hP.2).injective θ η

/-- **Conversely, the translate property gives the chartwise subtraction.**  So the hypothesis of
`AlgebraicGeometry.Space.isLiftDifferenceOfTranslate_of_chartSubtraction` is **equivalent** to
the predicate it discharges: it is a reformulation of
`AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate` into the shape that a difference of two
structure maps produces, and neither a weakening of it nor empty.

Every pair of acting sections is a pair `(η, θ + η)` — take `η` to be the first and `θ` the
difference — so the two statements say the same thing, once the chart identification is known to
be additive. -/
theorem chartSubtraction_of_isLiftDifferenceOfTranslate {hG : IsThickening C S hS X' Z.1}
    {D : LiftDifferenceFamily C S hS p Z hG q a} (hD : IsLiftDifferenceOfTranslate C S hS D)
    ⦃U' : SmallEtale C S hS X'.1⦄ (P : ChartLiftPresentation C S hS p q a.hom U')
    (hP : P.IsEtaleChartSquare C S hS) (σ₁ σ₂ : P.ActionSection) :
    P.transportActionSectionEquiv C S hS hG hP.1 hP.2
        (D U' (P.translateActionSection σ₁) (P.translateActionSection σ₂)) = σ₂ - σ₁ := by
  set E := P.transportActionSectionEquiv C S hS hG hP.1 hP.2 with hE
  have key : ∀ σ, P.translateTransportSection C S hS hG hP.1 hP.2 (E.symm σ) =
      P.translateActionSection σ := fun σ =>
    congrArg P.translateActionSection (E.apply_symm_apply σ)
  have h := hD P hP (E.symm σ₂ - E.symm σ₁) (E.symm σ₁)
  rw [sub_add_cancel, key, key] at h
  rw [h]
  refine (map_sub (AddEquiv.mk' E (P.transportActionSectionEquiv_add C S hS hG hP)) _ _).trans ?_
  exact congrArg₂ (· - ·) (E.apply_symm_apply _) (E.apply_symm_apply _)

/-! ### The compatibility -/

/-- **A chart-free difference of two lifts discharges the compatibility of the chartwise
translations.**  Granted a family of differences which recovers the acting section from a pair
of translates of one chart presentation and which commutes with restriction,
`AlgebraicGeometry.Space.IsChartTranslationCompatible` holds — so the glueing of the chartwise
action into an action of sheaves of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftTorsorGlueing` is unconditional on that
difference alone.

Neither hypothesis mentions two chart presentations, which is what a difference referring to no
chart can satisfy; the predicate discharged does, and that is the whole point.

The proof is `Stacks.eq_translate_add_of_difference` at the two presentations, with the
surjectivity half of
`AlgebraicGeometry.Space.ChartLiftPresentation.translateTransportSection_bijective` for the
presentation over the smaller chart. -/
theorem isChartTranslationCompatible_of_liftDifference {hG : IsThickening C S hS X' Z.1}
    {D : LiftDifferenceFamily C S hS p Z hG q a}
    (hD : IsLiftDifferenceOfTranslate C S hS D)
    (hDnat : IsLiftDifferenceRestrictionNatural C S hS D) :
    IsChartTranslationCompatible C S hS p Z hG q a := by
  intro _ _ m P hP Q hQ θ η ζ h
  exact Stacks.eq_translate_add_of_difference (hD P hP) (hD Q hQ) (hDnat m)
    (Q.translateTransportSection_bijective C S hS hG hQ.1 hQ.2).2 h

/-- **The independence of the chartwise action of the chart presentation** follows, being
`AlgebraicGeometry.Space.IsChartTranslationCompatible` read at one chart and the identity
morphism of charts: the restriction maps of the two sheaves along the identity are the
identity, by functoriality. -/
theorem isChartActionPresentationIndependent_of_liftDifference
    {hG : IsThickening C S hS X' Z.1}
    {D : LiftDifferenceFamily C S hS p Z hG q a}
    (hD : IsLiftDifferenceOfTranslate C S hS D)
    (hDnat : IsLiftDifferenceRestrictionNatural C S hS D) :
    IsChartActionPresentationIndependent C S hS p Z hG q a := by
  intro _ P₁ hP₁ P₂ hP₂ θ η ζ h
  exact Stacks.eq_translate_add_of_difference (resA := id) (resL := id)
    (t₁ := P₁.translateTransportSection C S hS hG hP₁.1 hP₁.2)
    (t₂ := P₂.translateTransportSection C S hS hG hP₂.1 hP₂.2)
    (hD P₁ hP₁) (hD P₂ hP₂) (fun _ _ => rfl)
    (P₂.translateTransportSection_bijective C S hS hG hP₂.1 hP₂.2).2 h

/-! ### The converse: the two hypotheses are exactly the compatibility -/

/-- **Conversely, the compatibility produces such a difference.**  Granted
`AlgebraicGeometry.Space.IsChartTranslationCompatible`, the glued action of
`AlgebraicGeometry.Space.translateGlobalSection` is simply transitive at every chart, and the
section carrying one lift to another is a chart-free difference with both properties.

So the two hypotheses of
`AlgebraicGeometry.Space.isChartTranslationCompatible_of_liftDifference` are **equivalent** to
the predicate they discharge: they are not a weakening of it, and they are not empty.  The
difference is read off the action rather than constructed, which is why this direction needs no
geometry: `AlgebraicGeometry.Space.existsUnique_translateGlobalSection` gives the section,
`AlgebraicGeometry.Space.translateGlobalSection_add` gives the first property and
`AlgebraicGeometry.Space.translateGlobalSection_map` the second. -/
theorem exists_liftDifference_of_isChartTranslationCompatible
    (hX : IsFirstOrderThickening C S hS X' Z.1)
    (hH : IsChartTranslationCompatible C S hS p Z hX.isThickening q a) :
    ∃ D : LiftDifferenceFamily C S hS p Z hX.isThickening q a,
      IsLiftDifferenceOfTranslate C S hS D ∧ IsLiftDifferenceRestrictionNatural C S hS D := by
  classical
  refine ⟨fun _ x y => (existsUnique_translateGlobalSection C S hS hX hH x y).choose, ?_, ?_⟩
  · intro U' P hP θ η
    refine ((existsUnique_translateGlobalSection C S hS hX hH _ _).choose_spec.2 θ ?_).symm
    exact ((congrArg (translateGlobalSection C S hS hX hH θ)
          (eq_translateGlobalSection C S hS hX hH
            (isTranslateBy_translateTransportSection C S hS hH P hP η))).trans
        (translateGlobalSection_add C S hS hX hH θ η P.liftSection).symm).trans
      (eq_translateGlobalSection C S hS hX hH
        (isTranslateBy_translateTransportSection C S hS hH P hP (θ + η))).symm
  · intro U' V' m x y
    refine ((existsUnique_translateGlobalSection C S hS hX hH _ _).choose_spec.2 _ ?_).symm
    exact (translateGlobalSection_map C S hS hX hH m
          (existsUnique_translateGlobalSection C S hS hX hH x y).choose x).symm.trans
      (congrArg _ (existsUnique_translateGlobalSection C S hS hX hH x y).choose_spec.1)

end AlgebraicGeometry.Space

end
