module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The differentials of a smooth morphism of algebraic spaces are finite locally free

Let `S` be a scheme and let `f : X ⟶ Y` be a smooth morphism of algebraic spaces over `S`.
Stacks 0CK5 asserts that the sheaf of differentials `Ω_{X/Y}` of Stacks 04CT is finite locally
free on the small étale site of `X`.

The source's proof is two steps: the statement is étale local on `X` and on `Y` by Stacks 04CU,
and so follows from the case of schemes, Stacks 02G1.  This file performs that reduction.
Smoothness of `f` is `AlgebraicGeometry.Space.IsSmooth`, the every-chart condition of
Stacks 03ZC(1), so it hands over smoothness of the scheme morphism `ψ : U ⟶ V` of any commuting
square of étale charts; Stacks 02G1 makes `Ω_{U/V}` finite locally free in the local-generators
form of Stacks 01C6(2);
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree` turns that into the
covering-family form of Stacks 03DL(2), which is the form in which this development states
finite local freeness of a module on the small étale site of an algebraic space; and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_etaleModulePullback_iff`, the clause of
Stacks 03DN along an étale morphism of algebraic spaces, descends the property from a surjective
étale chart of `X` to `X`.

One input of the source's proof is not available in this development and is carried as a
hypothesis:

* The comparison of Stacks 04CS between the differentials of a morphism of *schemes* on its
  small Zariski site and on its small étale site.  Stacks 04CS is proved in the scheme's own
  spelling —
  `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedRelativeDifferentialsDerivation`
  and `AlgebraicGeometry.SmallEtale.isIso_differentialsComparison_of_universal` of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsCorepresentable.lean`
  — but the transport of that identification onto the spaces-level sheaf of differentials of a
  morphism of represented algebraic spaces is not available: the two statements name different
  relative structures, vanishing on functions pulled back from opens of the target against
  derivations relative to the inverse image `ψ⁻¹𝒪` on the small étale site.  That transport is
  what is carried here, as `hsite`.

Stacks 04CU itself — the identification `Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V}` on a commuting square of
étale charts, with the *spaces*-level `Ω_{U/V}` on the right — was carried here too, as a second
hypothesis.  It is not any more: the tree proves it unconditionally, as
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, and that is what the proof
below uses.

## Main definitions

* `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeSiteComparison` is the one hypothesis, the
  transport of finite local freeness across the two sites of a morphism of schemes of the site.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials`: **Stacks 0CK5**,
  granted that comparison.

## Implementation notes

The hypothesis is not a statement about the finite local freeness of `Ω_{X/Y}`, so it is not
implied by the conclusion.  It is quantified over *every* morphism `ψ` of the big fppf site,
with no reference to `f`: it is the site comparison for an arbitrary morphism of schemes, and the
conclusion, a statement about one module on the small étale site of `X`, implies nothing about
the differentials of an unrelated `ψ`.  Smoothness of `f` is what makes it applicable, through
Stacks 02G1, and removing it leaves the proof with no way to produce its antecedent.

It is carried as an implication rather than as an identification because its two sides live on
different sites — the small Zariski site of the scheme `U` and the small étale site of `U` read
as an algebraic space — so no isomorphism of the two modules can be written down without the
associated-module functor of Stacks 03DU.  **It is not a restatement of
`AlgebraicGeometry.Space.SchemeDifferentialsComparison`**, the canonical form of Stacks 04CS
this tree carries, which is exactly that isomorphism: an identification of two modules is not a
transport of a property of them, and deducing this hypothesis from that identification needs
Stacks 03DX (2) for the associated-module functor, of which the tree has the free case alone,
`AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free'`.  The two statements
are therefore kept apart.

The chart square is produced the way the second half of the proof of Stacks 04G9 produces one:
an atlas of the target, lifted along `f` by Stacks 02X1,
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`.  Its chart of the source is
surjective on points, which is what the étale-locality step needs, and the pullback of modules
along it is étale restriction by Stacks' Equation 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`.

## References

* [Stacks Project, Tag 0CK5](https://stacks.math.columbia.edu/tag/0CK5)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1), the case of schemes.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  differentials of a morphism of schemes on its small Zariski and small étale sites.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces.
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL) and
  [Tag 01C6](https://stacks.math.columbia.edu/tag/01C6), the two forms of finite local freeness.
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN), the locality of finite
  local freeness on a covering family.
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1), the lift of a
  surjective étale chart along a morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identification of Stacks 04CU for `f : X ⟶ Y`: in every commuting square of étale
charts `a` of the source and `b` of the target, the restriction of `Ω_{X/Y}` to the chart `a` —
the pullback of `𝒪_X`-modules along `a`, by the abuse of notation of Stacks' Equation 03LW — is
the sheaf of differentials of the square's chart morphism, read as a morphism of algebraic
spaces.

This was carried as a hypothesis of Stacks 0CK5 and is **not** carried any more: it is proved
outright, just below, as
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleChartComparison`, from
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`.  Its right-hand side is the
spaces-level sheaf of differentials of the chart morphism, which is what that identification
produces; the scheme-level comparison, Stacks 04CS, is a different statement and is the
hypothesis that remains. -/
abbrev SheafOfDifferentialsEtaleChartComparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    Prop :=
  ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1) (ψ : U ⟶ V),
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b →
    yoneda.map ψ ≫ b = a ≫ f.hom →
    Nonempty ((modulePullback B S hS
          (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj
        (sheafOfDifferentials B S hS f) ≅
      sheafOfDifferentials B S hS (schemeSpaceMap ψ))

/-- **Stacks 04CU over a commuting square of étale charts, with no hypothesis.**  The
identification `AlgebraicGeometry.Space.SheafOfDifferentialsEtaleChartComparison` holds: it is
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` at the square, read through
`AlgebraicGeometry.Space.isEtale_of_presheaf_etale` to turn étaleness of the two chart maps as
morphisms of presheaves into étaleness as morphisms of algebraic spaces. -/
theorem sheafOfDifferentialsEtaleChartComparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    SheafOfDifferentialsEtaleChartComparison B S hS f := by
  intro U V a b ψ ha hb hdiag
  exact ⟨sheafOfDifferentialsEtaleLocalizationIso B S hS f
    (ObjectProperty.homMk a : schemeSpace U ⟶ X) (schemeSpaceMap ψ)
    (ObjectProperty.homMk b : schemeSpace V ⟶ Y) (isEtale_of_presheaf_etale B S hS ha)
    (isEtale_of_presheaf_etale B S hS hb) (ObjectProperty.hom_ext _ hdiag.symm)⟩

/-- The comparison of Stacks 04CS, in the form in which finite local freeness consumes it: for
every morphism `ψ` of the big fppf site of `S`, finite local freeness of the sheaf of relative
differentials of the scheme morphism `ψ` on the small Zariski site gives finite local freeness
of the sheaf of differentials of `ψ` read as a morphism of algebraic spaces, on the small étale
site.

Both sides are Stacks 03DL(2); only the site changes.  Nothing in this development compares the
two, so this is the one input of Stacks 0CK5 that it does not prove.  The statement mentions no
particular morphism of algebraic spaces.

It is **not** a restatement of `AlgebraicGeometry.Space.SchemeDifferentialsComparison`, the
canonical form of Stacks 04CS carried by this tree; the implementation notes of this module say
why the two are kept apart. -/
abbrev SheafOfDifferentialsSchemeSiteComparison : Prop :=
  ∀ (U V : BigFppfOver B S hS) (ψ : U ⟶ V),
    SheafOfModules.IsFiniteLocallyFreeOnSite
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)) →
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (sheafOfDifferentials B S hS (schemeSpaceMap ψ))

/-- **Stacks 0CK5.** The sheaf of differentials `Ω_{X/Y}` of a smooth morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` is finite locally free on the small étale site of `X`,
granted the comparison `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeSiteComparison`.

An atlas of the target lifts along `f`, by Stacks 02X1, to a commuting square of étale charts
whose chart of the source is surjective on points.  Smoothness of `f` is the every-chart
condition of Stacks 03ZC(1), so the square's scheme morphism `ψ` is smooth; Stacks 02G1 makes
`Ω_{U/V}` finite locally free in the local-generators form of Stacks 01C6(2), and
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree` rewrites that in the
covering-family form of Stacks 03DL(2).  The hypothesis carries it to the small étale site,
Stacks 04CU — `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleChartComparison`, which is proved
and no longer assumed — to the restriction of `Ω_{X/Y}` to the chart, and the clause of
Stacks 03DN along an étale morphism of algebraic spaces descends it from that surjective chart
to `X`. -/
@[stacks 0CK5 "granted as `hsite` the comparison of 04CS transporting finite local freeness of
  the differentials of a morphism of schemes of the site from its small Zariski site to its small
  étale site.  The identification Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V} of 04CU over a commuting square of
  étale charts is not granted: it is proved here"]
theorem isFiniteLocallyFreeOnSite_sheafOfDifferentials {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsSmooth B S hS f.hom)
    (hsite : SheafOfDifferentialsSchemeSiteComparison B S hS) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (sheafOfDifferentials B S hS f) := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.2.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V b hbSurj hbEtale
  have hcEt : IsEtale B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X).hom :=
    isEtale_of_presheaf_etale B S hS haEtale
  have hcSurj : IsSurjective B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X).hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U a).1 haSurj
  have hψ : Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
    hf U V a b ψ haEtale hbEtale hdiag.symm
  have hscheme : SheafOfModules.IsFiniteLocallyFreeOnSite
      (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)) :=
    Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree _
      (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials _)
  obtain ⟨e⟩ :=
    sheafOfDifferentialsEtaleChartComparison B S hS f U V a b ψ haEtale hbEtale hdiag.symm
  refine (isFiniteLocallyFreeOnSite_etaleModulePullback_iff B S hS
    (ObjectProperty.homMk a : schemeSpace U ⟶ X) hcEt hcSurj _).mpr ?_
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X) hcEt).app _)
    (SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e.symm (hsite U V ψ hscheme))

end AlgebraicGeometry.Space

end
