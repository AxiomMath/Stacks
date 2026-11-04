module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Formal étaleness is an étale-chart condition

A morphism of algebraic spaces over a scheme is formally étale exactly when the morphism of
schemes underlying every commuting square of étale scheme charts is formally étale, and
exactly when that holds for one such square whose two chart maps are surjective. Two
consequences are drawn: a flat unramified morphism of algebraic spaces is formally étale, and a
morphism of algebraic spaces is étale exactly when it is locally of finite presentation and
formally étale.

## Main results

* `AlgebraicGeometry.Space.formallyEtale_iff_etaleCharts`: **Stacks 04GD**, the equivalence of
  (1) and (2).
* `AlgebraicGeometry.Space.formallyEtale_iff_surjectiveEtaleChart`: **Stacks 04GD**, the
  equivalence of (1) and (3).
* `AlgebraicGeometry.Space.formallyEtale_of_isUnramified_of_isFlat`: **Stacks 0615**.
* `AlgebraicGeometry.Space.isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale`:
  **Stacks 0616**.

## Implementation notes

The chart condition is `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Tag 03MJ at the
scheme-level predicate `AlgebraicGeometry.FormallyEtale` of Tag 02HG, which is how every other
chart criterion in this library is phrased — étaleness itself by Tag 03XT, local finite
presentation by Tag 03XP, flatness by Tag 03ML, unramifiedness by Tag 03ZH, and formal
unramifiedness by Tag 04G8. Stating Tag 04GD this way is what makes Tags 0615 and 0616
immediate: all five conditions become conditions on one and the same square of charts, so the
scheme-level implications of Tags 04FF and 02HM can be quantified over the charts.

For a single square of charts, passing between the chart condition and the predicate on the
morphism of algebraic spaces is the content of
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmooth/EtaleCharts.lean`. The equivalence is then
assembled exactly as for formal unramifiedness in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmooth/UnramifiedChartCriterion.lean`: one
direction composes the chart of the source with the morphism and cancels the chart of the
target using Tags 04AL, 049T and 04G5, and the other descends along a surjective étale chart
by Tag 04CY, for which the source and target must be sheaves for the étale topology on the
slice — which an algebraic space is.

## References

* [Stacks Project, Tag 02HG](https://stacks.math.columbia.edu/tag/02HG)
* [Stacks Project, Tag 02HM](https://stacks.math.columbia.edu/tag/02HM)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04FF](https://stacks.math.columbia.edu/tag/04FF)
* [Stacks Project, Tag 04G5](https://stacks.math.columbia.edu/tag/04G5)
* [Stacks Project, Tag 04GD](https://stacks.math.columbia.edu/tag/04GD)
* [Stacks Project, Tag 0615](https://stacks.math.columbia.edu/tag/0615)
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04GD, (1) implies (2).** In a commuting square of étale scheme charts of a
formally étale morphism of presheaves, the morphism of schemes between the charts is formally
étale.

The composite of the chart of the source with the morphism is formally étale by Tag 049T,
since the chart is formally étale by Tag 04AL; it equals the composite of the chart morphism
with the chart of the target, and Tag 04G5 cancels the latter, which is formally unramified. -/
theorem holdsOnEveryEtaleChart_formallyEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : FormallyEtale f) :
    HoldsOnEveryEtaleChart B S hS
      (@_root_.AlgebraicGeometry.FormallyEtale.{u} : MorphismProperty Scheme.{u}) f := by
  intro U V a b ψ ha hb hdiag
  have hbF := formallyEtale_of_etale B S hS b hb
  refine schemeFormallyEtale_of_formallyEtale_yonedaMap B S hS ψ ?_
  refine formallyEtale_of_comp_of_formallyUnramified (yoneda.map ψ) b
    (fun T T' hT hT' i hi x y hxy _ _ hz₁ hz₂ =>
      (hbF T T' hT hT' i hi x y hxy).unique hz₁ hz₂) ?_
  rw [hdiag]
  exact formallyEtale_comp (formallyEtale_of_etale B S hS a ha) hf

/-- **Stacks 04GD, (3) implies (1).** Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`, let `a : yoneda.obj U ⟶ X` be a surjective étale chart, let `b : yoneda.obj V ⟶ Y` be an
étale chart and let `ψ : U ⟶ V` make the square commute. If the morphism of schemes underlying
`ψ` is formally étale, then `f` is formally étale. -/
theorem formallyEtale_of_surjectiveEtaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
      Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
      Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b)
    (haSurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hdiag : a ≫ f = yoneda.map ψ ≫ b)
    (hψ : _root_.AlgebraicGeometry.FormallyEtale
      ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallyEtale f := by
  have hcomp : FormallyEtale (a ≫ f) :=
    hdiag ▸ formallyEtale_comp
      (formallyEtale_yonedaMap_of_schemeFormallyEtale B S hS ψ hψ)
      (formallyEtale_of_etale B S hS b hb)
  exact formallyEtale_of_comp
    { B := B, S := S, hS := hS, F := yoneda.obj U, G := X, H := Y, a := a, b := f
      representable_a := ha.1, surjective_a := haSurj, etale_a := ha }
    (isSheaf_etaleTopology_over_of_isAlgebraicSpace B S hS hX)
    (isSheaf_etaleTopology_over_of_isAlgebraicSpace B S hS hY) hcomp

/-- **Stacks 04GD, the equivalence of (1) and (2).** A morphism of algebraic spaces over `S` is
formally étale exactly when the morphism of schemes underlying every commuting square of étale
scheme charts is formally étale. -/
@[stacks 04GD "condition (2)"]
theorem formallyEtale_iff_etaleCharts
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallyEtale f ↔
      HoldsOnEveryEtaleChart B S hS
        (@_root_.AlgebraicGeometry.FormallyEtale.{u} : MorphismProperty Scheme.{u}) f := by
  refine ⟨holdsOnEveryEtaleChart_formallyEtale B S hS f, fun hall ↦ ?_⟩
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact formallyEtale_of_surjectiveEtaleChart B S hS hX hY f a b ψ haEtale hbEtale haSurj
    hdiag (hall U V a b ψ haEtale hbEtale hdiag.symm)

/-- **Stacks 04GD, the equivalence of (1) and (3).** A morphism of algebraic spaces over `S` is
formally étale exactly when there is one commuting square of étale scheme charts, both chart
maps surjective, whose underlying morphism of schemes is formally étale. -/
@[stacks 04GD "condition (3)"]
theorem formallyEtale_iff_surjectiveEtaleChart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallyEtale f ↔
      ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        yoneda.map ψ ≫ b = a ≫ f ∧
        _root_.AlgebraicGeometry.FormallyEtale
          ((BigFppfOver.toScheme B S hS).map ψ) := by
  refine ⟨fun hf ↦ ?_, fun ⟨U, V, a, b, ψ, ha, hb, haSurj, _, hdiag, hψ⟩ ↦
    formallyEtale_of_surjectiveEtaleChart B S hS hX hY f a b ψ ha hb haSurj hdiag.symm hψ⟩
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, hbSurj, hdiag.symm,
    (formallyEtale_iff_etaleCharts B S hS hX hY f).mp hf U V a b ψ haEtale hbEtale hdiag.symm⟩

/-- **Stacks 0615.** A flat unramified morphism of algebraic spaces over `S` is formally étale.

Unramifiedness and flatness are conditions on the étale charts of the morphism, and on each
chart Tag 04FF makes the morphism of schemes formally étale; Tag 04GD assembles those into
formal étaleness of the morphism of algebraic spaces. -/
@[stacks 0615]
theorem formallyEtale_of_isUnramified_of_isFlat
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hu : IsUnramified B S hS f) (hflat : IsFlat B S hS f) :
    FormallyEtale f := by
  refine (formallyEtale_iff_etaleCharts B S hS hX hY f).mpr fun U V a b ψ ha hb hdiag => ?_
  have := hu U V a b ψ ha hb hdiag
  have := hflat U V a b ψ ha hb hdiag
  exact _root_.AlgebraicGeometry.formallyEtale_of_unramified_flat _

/-- **Stacks 0616.** A morphism of algebraic spaces over `S` is étale if and only if it is
locally of finite presentation and formally étale.

All three conditions are conditions on the same squares of étale scheme charts — étaleness by
Tag 03XT, local finite presentation by Tag 03XP and formal étaleness by Tag 04GD — so the
statement is the scheme-level equivalence of Tag 02HM quantified over the charts, together
with the distribution of a universal quantifier over a conjunction. -/
@[stacks 0616, ega "IV 17.6.1" "a) <=> d)"]
theorem isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsEtale B S hS f ↔ (IsLocallyOfFinitePresentation B S hS f ∧ FormallyEtale f) := by
  rw [isEtale_iff_holdsOnEveryEtaleChart B S hS hX hY f,
    formallyEtale_iff_etaleCharts B S hS hX hY f]
  refine ⟨fun hf => ⟨fun U V a b ψ ha hb hdiag =>
      ((_root_.AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_formallyEtale
        ((BigFppfOver.toScheme B S hS).map ψ)).mp (hf U V a b ψ ha hb hdiag)).1,
    fun U V a b ψ ha hb hdiag =>
      ((_root_.AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_formallyEtale
        ((BigFppfOver.toScheme B S hS).map ψ)).mp (hf U V a b ψ ha hb hdiag)).2⟩,
    fun ⟨hlfp, hfe⟩ U V a b ψ ha hb hdiag =>
      (_root_.AlgebraicGeometry.etale_iff_locallyOfFinitePresentation_and_formallyEtale
        ((BigFppfOver.toScheme B S hS).map ψ)).mpr
        ⟨hlfp U V a b ψ ha hb hdiag, hfe U V a b ψ ha hb hdiag⟩⟩

end AlgebraicGeometry.Space

end
