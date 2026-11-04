module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType

/-!
# Cancelling local finite presentation against local finite type (Stacks 05WT)

If a composite `X ⟶ Y ⟶ Z` of morphisms of algebraic spaces is locally of finite presentation
and the second factor is locally of finite type, then the first factor is locally of finite
presentation. This is **Stacks 05WT**, and it is the only cancellation statement of the
every-étale-chart machinery of **Stacks 03MJ** that compares *two different* properties of
scheme morphisms: the companion
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp` (**Stacks 0462**) cancels one property
against itself, so it instantiates the single-property
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp`, and this one cannot.

The argument is the one-property argument with the second property carried along. A surjective
étale atlas of the final target is lifted along the second morphism by **Stacks 02X1**, and the
surjective étale chart of the intermediate space so obtained is lifted again along the first
morphism. The two morphisms of the site so produced compose to the morphism of a chart square of
the composite, so `P` holds of that composite of scheme morphisms; the second of them is the
morphism of a chart square of the second factor, so `Q` holds of it; cancelling at the level of
schemes leaves `P` on a surjective étale chart square of the first morphism, which is
**Stacks 03MJ** condition (2).

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_of`: the two-property cancellation of
  the every-étale-chart condition.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp`: **Stacks 05WT**.

## Implementation notes

The cancellation hypothesis is stated as an implication between properties of morphisms of
schemes rather than through `CategoryTheory.MorphismProperty` instance classes, so that the
instance-argument form of the scheme-level statement
`AlgebraicGeometry.locallyOfFinitePresentation_of_comp` (**Stacks 02FV**, part (1)) discharges
it by application.

Of the imports, `Spaces.FinitePresentation` and `Spaces.FiniteType` are **necessary** — without
either the statement does not elaborate (`Function expected at`) — while
`Descent.EtaleLocal.FinitePresentationLocalAtSource`, `Morphisms.FinitePresentation.Basic` and
`Spaces.EtaleChartLocality` supply names used in the proof. `Spaces.EtaleCharts` is not imported:
`exists_surjective_etale_presentation_lift` is reachable through `Spaces.EtaleChartLocality`, and
the statement is the same without it.

Stacks 05WT is a result of Chapter 67 (Morphisms of Spaces), and its registration
`@[stacks 05WT]` is placed here. It is also consumed here by
name: the statement of Stacks 06Q6 for 1-morphisms of algebraic stacks needs exactly this
proposition for the top horizontal morphisms of its smooth diagrams.

## References

* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 05WT](https://stacks.math.columbia.edu/tag/05WT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two properties of morphisms of schemes, the first étale local on the source and target, with
the first cancelling against the second: if the first holds on every étale chart of a composite
of morphisms of algebraic spaces over `S` and the second holds on every étale chart of the
second factor, then the first holds on every étale chart of the first factor.

A surjective étale atlas of the final target is lifted along the second morphism, and the
surjective étale chart of the intermediate space so obtained is lifted again along the first
morphism. The resulting two morphisms of the site compose to the morphism of a chart square of
the composite, so `P` holds of that composite of scheme morphisms; the second is the morphism of
a chart square of the second factor, so `Q` holds of it; cancelling leaves `P` on a surjective
étale chart square of the first morphism. -/
theorem holdsOnEveryEtaleChart_of_comp_of
    (P Q : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hcancel : ∀ {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z), P (u ≫ v) → Q v → P u)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hfg : HoldsOnEveryEtaleChart B S hS P (f ≫ g))
    (hg : HoldsOnEveryEtaleChart B S hS Q g) :
    HoldsOnEveryEtaleChart B S hS P f := by
  obtain ⟨W, c, hcSurj, hcEtale⟩ := hH.exists_atlas
  obtain ⟨V, b, k, hbk, hbSurj, hbEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hG hH g W c hcSurj hcEtale
  obtain ⟨U, a, h, hah, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurj hbEtale
  have hsq : yoneda.map (h ≫ k) ≫ c = a ≫ f ≫ g := by
    rw [Functor.map_comp, Category.assoc, ← hbk, ← Category.assoc, ← hah, Category.assoc]
  have hcomp : P ((BigFppfOver.toScheme B S hS).map (h ≫ k)) :=
    hfg U W a c (h ≫ k) haEtale hcEtale hsq
  have hQk : Q ((BigFppfOver.toScheme B S hS).map k) :=
    hg V W b c k hbEtale hcEtale hbk.symm
  have hPh : P ((BigFppfOver.toScheme B S hS).map h) :=
    hcancel _ ((BigFppfOver.toScheme B S hS).map k)
      (by simpa only [Functor.map_comp] using hcomp) hQk
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hF hG f).mpr
    ⟨U, V, a, b, h, haEtale, hbEtale, haSurj, hah.symm, hPh⟩

/-- **Stacks 05WT.** If a composite of morphisms of algebraic spaces over `S` is locally of
finite presentation and its second factor is locally of finite type, then its first factor is
locally of finite presentation.

Being locally of finite presentation is étale local on the source and target by **Stacks 04R3**
and cancels against being locally of finite type at the level of schemes by **Stacks 02FV**,
part (1), so this is the two-property cancellation of the chart condition at those two
properties. -/
@[stacks 05WT]
theorem isLocallyOfFinitePresentation_of_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hfg : IsLocallyOfFinitePresentation B S hS (f ≫ g))
    (hg : IsLocallyOfFiniteType B S hS g) :
    IsLocallyOfFinitePresentation B S hS f :=
  holdsOnEveryEtaleChart_of_comp_of B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    (fun u v huv hv => @locallyOfFinitePresentation_of_comp _ _ _ u v huv hv)
    hF hG hH f g hfg hg

end AlgebraicGeometry.Space

end
