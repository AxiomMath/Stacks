module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLinearMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalTopSections

/-!
# The sections of the acting sheaf at a chart are the acting group of the chart presentation

Let `X ⊆ X'` be a closed subspace of an algebraic space over a scheme `S` contained in a big
fppf site `B`, let `q : Y ⟶ Bb` be a morphism of algebraic spaces and let `a : X ⟶ Y` be a
morphism over `Bb`.  The sheaf acting on the lifts of `a` over the étale charts of `X'` is
`AlgebraicGeometry.Space.liftActionSheaf`, the internal Hom
`SheafHom_{𝒪_X}(a^*Ω_{Y/Bb}, 𝒞_{X/X'})` of [Stacks Project, Tag 061D], and the action is
constructed over an étale scheme chart in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`, where the acting object is
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` — a `Γ(U, ⊤)`-linear map
`Γ(a^*Ω_{W/V}, ⊤) ⟶ RingHom.ker i^♯` of Zariski data on the chart.

This file identifies the two: for a chart presentation `P` of the lifting problem, the sections
of the acting sheaf over the étale chart of `X` that `P` presents **are** `P.ActionSection`.

## The two descriptions, and what matches them

A section of `liftActionSheaf` over an étale chart is, by the definition of an internal Hom, a
morphism of the restrictions of `a^*Ω_{Y/Bb}` and `𝒞_{X/X'}` to the **slice** of the small étale
site at that chart.  The geometric comparisons available are instead about the **inverse image**
to the small étale site of the chart space.  What matches them is the slice form of
[Stacks Project, Tag 04M0] together with Equation [Stacks Project, Tag 03LW], packaged as
`AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv`: once the two inverse
images are presented as the modules `Mᵃ` of [Stacks Project, Tag 03DU] (4) of quasi-coherent
Zariski modules on an affine chart scheme, a chart-level section is exactly a linear map of their
global sections.  The two presentations are

* the source, `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso`, the composite
  of [Stacks Project, Tag 04CU] and [Stacks Project, Tag 04CS] in the spelling a chart
  presentation produces;
* the target, `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso`,
  [Stacks Project, Tag 04CO] followed by [Stacks Project, Tag 04G2] (1);

and the one remaining identification of global sections is
`Stacks.Thickenings.conormalTopSectionsLinearEquivKer`, that the global sections of the Zariski
conormal sheaf of the chart thickening are `RingHom.ker i^♯`.

## Main definitions

* `AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChart`: the étale chart of `X` that the
  presentation presents — the object `P.sub` with its chart morphism.
* `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.chartTargetIso`: the two inverse images at that
  chart, as associated modules of the Zariski cotangent sheaf of the chart square and of the
  Zariski conormal sheaf of the chart thickening.
* `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionAddEquiv`: **the sections of the
  acting sheaf of [Stacks Project, Tag 061D] over the presented chart are
  `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, as abelian groups**, and
  `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv` is the underlying bijection,
  with `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv_add` its additivity.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.chartSq'` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.subChart_comp`: the chart square of `q` and the
  factorization of the presented chart through it, read as morphisms of algebraic spaces.  The
  second is the pointwise lift clause of `AlgebraicGeometry.Space.IsChartLift` applied at the
  presenting square, which is the only place the lifting condition is used.

## Implementation notes

The two étale charts of `q` enter as hypotheses, in the `MorphismProperty.presheaf` form the
freeness and transitivity statements of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` use, and are converted to
`AlgebraicGeometry.Space.IsEtale` by
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`, both charts having representable
source.  Étaleness of the charts of `q` is what [Stacks Project, Tag 04CU] needs; it is not
needed by the action itself, which is why
`AlgebraicGeometry.Space.ChartLiftPresentation` does not carry it.

No affineness beyond the presentation's own is used: the chart scheme of the presented chart of
`X` is `AlgebraicGeometry.Space.ChartLiftPresentation.subScheme`, affine by
`AlgebraicGeometry.Space.ChartLiftPresentation.isAffineSub`, and the ambient chart is affine by
the presentation's `isAffineAmbient` field, which is what makes the map on global functions of
the chart thickening surjective.

The quasi-coherence of the two Zariski modules is unconditional:
[Stacks Project, Tag 01BG] at the sheaf of differentials for the source, and
`Stacks.Conormal.conormalSheaf_isQuasicoherent` — the quasi-coherence half of
[Stacks Project, Tag 01R2] — for the target.

## What this does not do

**It does not describe the value of the identification, and that is a genuine obstruction
rather than an omission.**  The last factor of
`AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv` is
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`, whose inverse direction
is an `Equiv.ofBijective` of `β ↦ βᵃ` — a `Function.surjInv`, hence choice — so the composite
cannot describe its own values and must be used through the characterising equations of its two
factors (`β ↦ βᵃ` and `Stacks.AlgebraicGeometry.ModuleLimits.appTopₗ`) instead.

What the identification *does* carry is its **additivity**: it is built as an isomorphism of
abelian groups, `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionAddEquiv`, from the
additivity of the general identification
(`AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv_add`) and the fact that
the remaining factor is a linear equivalence.  The two have to be assembled in one declaration:
the conversion identifying the two elaborations of that last factor — one at the ring of the
chart, one at the ring of `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` — does not
fit the heartbeat budget of a declaration that also elaborates the first factor, which is why
`actionSectionEquiv` is *defined* as the underlying bijection of the additive equivalence rather
than built a second time.

The outer `LinearEquiv.arrowCongr` *can* be peeled: the statement that the linear map attached to a section is the chart-level
reading of that section followed by
`Stacks.Thickenings.conormalTopSectionsLinearEquivKer` is
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv_apply`, in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSectionValue`.  What looks like
a `whnf` wall comes down to three things, none of them mathematics: the `rfl` has to be
done between the *isomorphisms of abelian groups* and never at an applied value; the passage from
the isomorphism to the value has to be a generic lemma at plain variables; and the `Module`
structure of the conormal data over the ring spelled `Γ(chartScheme A, ⊤)` has to be supplied by
hand, instance resolution not finding it because the second factor spells the same ring
`Γ(U, ⊤)`.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 061D]'s acting sheaf is registered on
`AlgebraicGeometry.Space.liftActionSheaf` and its action on the lifts in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`; what is proved here is
that the group acting there is the acting sheaf's sections, which is the identification step (II)
of [Stacks Project, Tag 04AM] needs and not a new assertion of either tag.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1}
  (P : ChartLiftPresentation C S hS p q a.hom U')

/-- **The étale chart of the subspace that a chart presentation presents.**  The object `P.sub`
of the big fppf site, with the chart morphism `P.subChart`, is an étale chart of `X`: it is the
base change of the étale chart `U'` of `X'` along the inclusion of `X`, which is what the
cartesian square `P.isPullback` says. -/
abbrev subEtaleChart : SmallEtale C S hS Z.1.toFunctor :=
  presentedSubspaceChart C S hS Z U' P.incl P.subChart P.isPullback

/-- The chart square of `q` carried by the presentation, read as a commuting square of morphisms
of algebraic spaces. -/
theorem chartSq' :
    (ObjectProperty.homMk P.tgtChart : schemeSpace P.tgt ⟶ Y) ≫ q =
      schemeSpaceMap P.chartHom ≫ (ObjectProperty.homMk P.bseChart : schemeSpace P.bse ⟶ Bb) :=
  ObjectProperty.hom_ext _ P.chartSq.symm

/-- **The presented chart of `X`, followed by `a`, factors through the chart square of `q`.**
The factorization is the reduction of the presented lift to the closed subscheme of the chart
followed by the chart of `Y`.  This is the pointwise clause of
`AlgebraicGeometry.Space.IsChartLift` applied to the presenting square: a test object mapping
into the chart and landing in `X` factors through `P.sub`, and there the presented lift agrees
with `a`. -/
theorem subChart_comp :
    chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) P.subEtaleChart ≫ a =
      schemeSpaceMap (P.incl ≫ P.liftHom) ≫
        (ObjectProperty.homMk P.tgtChart : schemeSpace P.tgt ⟶ Y) := by
  apply ObjectProperty.hom_ext
  show P.subChart ≫ a.hom = yoneda.map (P.incl ≫ P.liftHom) ≫ P.tgtChart
  rw [Functor.map_comp, Category.assoc]
  exact (P.isLift.2 P.sub P.incl P.subChart P.isPullback.w).symm

/-- **The source comparison at the presented chart.**  The inverse image of `a^*Ω_{Y/Bb}` to the
small étale site of the chart space is the associated module of the Zariski cotangent sheaf
`AlgebraicGeometry.Space.ChartLiftPresentation.chartCotangent` of the chart square.

This is `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` at the presentation;
the two étale charts of `q` are where [Stacks Project, Tag 04CU] is used. -/
def chartSourceIso
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (modulePullback C S hS (chartToSpace C S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) P.subEtaleChart)).obj
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)) ≅
      (representedAssociatedModule C S hS P.sub (schemeSpace P.sub).property).obj
        P.chartCotangent :=
  chartDifferentialsAssociatedCotangentIso C S hS q a
    (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
    ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
    ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
    P.chartSq' P.subEtaleChart (P.incl ≫ P.liftHom) P.subChart_comp

/-- **The target comparison at the presented chart.**  The inverse image of `𝒞_{X/X'}` to the
small étale site of the chart space is the associated module of the Zariski conormal sheaf of the
chart thickening.

This is `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso` at the
presentation. -/
def chartTargetIso :
    letI := P.isFirstOrderThickening.1
    (modulePullback C S hS (chartToSpace C S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) P.subEtaleChart)).obj
        (conormalModule C S hS X' Z) ≅
      (representedAssociatedModule C S hS P.sub (schemeSpace P.sub).property).obj
        (Stacks.Thickenings.conormalModules P.inclScheme) :=
  letI := P.isFirstOrderThickening.1
  conormalModulePresentedChartAssociatedIso C S hS Z U' P.incl P.isFirstOrderThickening.1
    P.subChart P.isPullback

/-- **The sections of the acting sheaf of [Stacks Project, Tag 061D] over the presented chart are
the acting group of the chart presentation, as abelian groups.**  Granted that the two charts of
`q` are étale — which is what [Stacks Project, Tag 04CU] needs and what the action itself does
not — a section of `SheafHom_{𝒪_X}(a^*Ω_{Y/Bb}, 𝒞_{X/X'})` over the étale chart of `X` presented
by `P` is exactly a `Γ(U, ⊤)`-linear map `Γ(a^*Ω_{W/V}, ⊤) ⟶ RingHom.ker i^♯`, that is an element
of `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, and the bijection is additive.

This is the identification of the slice description of a chart-level section with the Zariski
one, `AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv`, fed the two
geometric comparisons at the presentation and composed with the identification of the global
sections of the Zariski conormal sheaf with the conormal data of the chart thickening.  Both
factors are additive — the first by
`AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv_add`, the second because
it is a linear equivalence — so the composite is built here as an isomorphism of abelian groups
rather than as a bare bijection. -/
def actionSectionAddEquiv
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart) ≃+ P.ActionSection :=
  letI := P.isAffineAmbient
  letI : IsAffine (chartScheme P.subEtaleChart) := P.isAffineSub
  haveI := P.isFirstOrderThickening.1
  haveI : AlgebraicGeometry.IsImmersion P.inclScheme := inferInstance
  haveI : (P.chartCotangent).IsQuasicoherent :=
    Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf' _ _
  haveI : (Stacks.Thickenings.conormalModules P.inclScheme).IsQuasicoherent :=
    Stacks.Conormal.conormalSheaf_isQuasicoherent P.inclScheme
  letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  (AddEquiv.mk' (smallEtaleInternalHomChartAssociatedLinearEquiv C S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
        (conormalModule C S hS X' Z) P.subEtaleChart P.chartCotangent
        (Stacks.Thickenings.conormalModules P.inclScheme)
        (chartSourceIso C S hS P hw hv) (chartTargetIso C S hS P))
      (smallEtaleInternalHomChartAssociatedLinearEquiv_add C S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
        (conormalModule C S hS X' Z) P.subEtaleChart P.chartCotangent
        (Stacks.Thickenings.conormalModules P.inclScheme)
        (chartSourceIso C S hS P hw hv) (chartTargetIso C S hS P))).trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl _ _)
      (Stacks.Thickenings.conormalTopSectionsLinearEquivKer P.inclScheme
        P.isFirstOrderThickening.2)).toAddEquiv

/-- **The sections of the acting sheaf of [Stacks Project, Tag 061D] over the presented chart are
the acting group of the chart presentation.**  This is the underlying bijection of
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionAddEquiv`.

It is *defined* as that bijection rather than built again from the two factors: the conversion
which identifies the two elaborations of the second factor — one at the ring
`Γ(chartScheme A, ⊤)` of the chart and one at the ring `Γ(U, ⊤)` of
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` — does not fit the heartbeat budget
of a declaration which also has to elaborate the first factor, so the two have to be one term and
not two. -/
def actionSectionEquiv
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart) ≃ P.ActionSection :=
  (actionSectionAddEquiv C S hS P hw hv).toEquiv

/-- **The identification of the acting sheaf's chart sections with the acting group is
additive.** -/
theorem actionSectionEquiv_add
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (g₁ g₂ : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart)) :
    actionSectionEquiv C S hS P hw hv (g₁ + g₂) =
      actionSectionEquiv C S hS P hw hv g₁ + actionSectionEquiv C S hS P hw hv g₂ :=
  map_add (actionSectionAddEquiv C S hS P hw hv) g₁ g₂

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
