module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport

/-!
# Formal unramifiedness of a morphism of algebraic spaces and the vanishing of `Ω_{X/Y}`

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`. Stacks
04G9 asserts that `f` is formally unramified exactly when its sheaf of differentials
`Ω_{X/Y}` of Stacks 04CT is a zero object.

The source's proof combines three statements. Stacks 04G8 reduces formal unramifiedness of `f`
to formal unramifiedness of the scheme morphism `ψ : U ⟶ V` in one commuting square of étale
scheme charts whose two chart maps are surjective; Stacks 02H9 rewrites that as the vanishing
of the sheaf of relative differentials of `ψ`; and Stacks 04CU identifies the restriction of
`Ω_{X/Y}` to the small étale site of `U` with `Ω_{U/V}`, which turns the vanishing of the
latter into the vanishing of the restriction of `Ω_{X/Y}` to a surjective étale chart, and so
into the vanishing of `Ω_{X/Y}` itself.

All four steps are available here and are used:

* Stacks 04G8 is `AlgebraicGeometry.Space.formallyUnramified_iff_surjectiveEtaleChart`;
* Stacks 02H9 is
  `AlgebraicGeometry.Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials`;
* the last step — a sheaf of modules on `X` vanishes as soon as its restriction to a
  surjective étale chart does — is proved below as
  `AlgebraicGeometry.Space.isZero_of_isZero_modulePullback_chart`, from the faithfulness of
  that restriction, `AlgebraicGeometry.Space.faithful_modulePullback`.
* Stacks 04CU is `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, which
  produces the identification `Ω_{X/Y}|_{U_étale} ≅ Ω_{ψ}` of the restriction with the
  *spaces*-level sheaf of differentials of `ψ`; Stacks 04CS, in the form
  `AlgebraicGeometry.Space.sheafOfDifferentialsRepresentedIso`, identifies the latter with the
  small-étale module associated to the scheme-level `Ω_{U/V}` that Stacks 02H9 speaks about,
  and `AlgebraicGeometry.Space.isZero_representedAssociatedModule_iff` turns the vanishing of
  the associated module back into the vanishing of `Ω_{U/V}`.

Stacks 04CU is available too, and is used, not assumed:
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` produces the identification
`Ω_{X/Y}|_{U_étale} ≅ Ω_{U/V}` on any commuting square of étale charts, unconditionally.  Its
right-hand side is the *spaces*-level sheaf of differentials of `ψ` read as a morphism of
represented algebraic spaces, which Stacks 04CU's final sentence identifies, through
Stacks 04CS, with the scheme-level `Ω_{U/V}` that Stacks 02H9 speaks about.  This development
has the invertibility clause of Stacks 04CS, at zero objects
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeVanishing`: for every morphism `ψ` of
schemes of the big fppf site, the spaces-level sheaf of differentials of `ψ` vanishes exactly
when the scheme-level sheaf of relative differentials of `ψ` does.  So nothing is carried.  The
chart-square form `AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison` in which both
directions of the equivalence use that comparison is *derived* from it below, by Stacks 04CU.

**Its `mpr` half is no longer a hypothesis.**
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeVanishing.lean` proves the
vanishing shadow of Stacks 04CS in the direction that needs no surjectivity of the comparison
map, and hence proves the `mpr` half of the chart comparison outright as
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_mpr`.  That is the only half the
forward implication of Stacks 04G9 consumes, so the forward implication is available with no
hypothesis at all, as
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified` in that module.
The `mp` half, which the converse implication consumes, is still open: the comparison map
`AlgebraicGeometry.SmallEtale.differentialsComparison` lands *in* the small-étale
differentials, so a zero target says nothing about its source without surjectivity.

**So the comparison below is no longer an independent assumption.**  Its open half is isolated as
`AlgebraicGeometry.Space.SheafOfDifferentialsChartComparisonMp`, and
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_of_mp` derives the whole equivalence
from that half; anything that needs the equivalence should assume the half.  No consumer of this
library assumes either any more: the two that assumed the equivalence, in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceUnramifiedPair.lean`, spent it only on the
forward implication of Stacks 04G9 and now call that unconditionally.

The comparison of Stacks 04CS that this shadows is itself carried in one canonical statement,
`AlgebraicGeometry.Space.SchemeDifferentialsComparison`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparison.lean`).  The chart
comparison below is *not* a restatement of it and does not follow from it: an isomorphism
`Ω^{spaces}_ψ ≅ (Ω_{U/V})^a` carries a vanishing of the left side to a vanishing of the right,
and only Stacks 08H8's faithfulness assertion for the associated-module functor of
Stacks 03DU (4) would return from there to `Ω_{U/V}` — and that assertion is in this tree only
for the pullback of the abstract morphism of ringed topoi,
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback`, which is not that
functor.

## Main definitions

* `AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison`: the chart-square form in which
  the proof of Stacks 04G9 consumes the comparison of Stacks 04CS.  That comparison,
  `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeVanishing`, is stated in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparison.lean` and proved in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`.

## Main results

* `AlgebraicGeometry.Space.isZero_of_isZero_modulePullback_chart`: a sheaf of modules on an
  algebraic space is a zero object as soon as its restriction along a surjective étale scheme
  chart is.
* `AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_of_schemeVanishing` and
  `AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison`: the chart-square comparison
  follows from the comparison for morphisms of schemes, by Stacks 04CU, and that comparison is
  proved.
* `AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials`:
  **Stacks 04G9**, granted the vanishing comparison for morphisms of schemes.

## References

* [Stacks Project, Tag 04G9](https://stacks.math.columbia.edu/tag/04G9)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8), the reduction of
  formal unramifiedness to a surjective étale chart square.
* [Stacks Project, Tag 02H9](https://stacks.math.columbia.edu/tag/02H9), the equivalence for
  a morphism of schemes.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the identification
  `Ω_{X/Y}|_{U_étale} = Ω_{U/V}`.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  differentials of a morphism of schemes on its small Zariski and small étale sites.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the pullback of
  modules along a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sheaf of `𝒪_X`-modules on an algebraic space `X` over `S` is a zero object as soon as
its restriction along a surjective étale scheme chart is one.

The restriction along such a chart is faithful by
`AlgebraicGeometry.Space.faithful_modulePullback`. The vanishing of the restriction identifies
any two morphisms out of it, so the restrictions of the identity and of the zero morphism of
the module agree, and faithfulness returns that to the module itself, where a vanishing
identity is the vanishing of the module. -/
theorem isZero_of_isZero_modulePullback_chart {X : AlgebraicSpaces B S hS}
    (U : BigFppfOver B S hS) (i : schemeSpace U ⟶ X) (hi : IsEtale B S hS i.hom)
    (hs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (hM : IsZero ((modulePullback B S hS i).obj M)) : IsZero M := by
  have := faithful_modulePullback B S hS U i hi hs
  exact (IsZero.iff_id_eq_zero M).mpr ((modulePullback B S hS i).map_injective (hM.eq_of_src _ _))

/-- The chart comparison for the sheaf of differentials of a morphism `f : X ⟶ Y` of algebraic
spaces over `S`: in every commuting square of étale scheme charts whose chart map of the source
is surjective, the restriction of `Ω_{X/Y}` to that chart is a zero object exactly when the
sheaf of relative differentials of the scheme morphism `ψ : U ⟶ V` of the square is.

This is the third step of the proof of Stacks 04G9 in the form in which that proof uses it:
the identification `Ω_{X/Y}|_{U_étale} = Ω_{U/V}` of Stacks 04CU, read through the comparison
of Stacks 04CS between the small Zariski and the small étale differentials of a morphism of
schemes.

Only its `mp` half is still an assumption.  The `mpr` half is proved outright as
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_mpr`, and this whole equivalence
follows from the `mp` half alone by
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_of_mp`, both in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeVanishing.lean`; that half is
`AlgebraicGeometry.Space.SheafOfDifferentialsChartComparisonMp` and is what a new consumer should
assume. -/
abbrev SheafOfDifferentialsChartComparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1) (ψ : U ⟶ V),
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b →
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    yoneda.map ψ ≫ b = a ≫ f.hom →
    (IsZero ((modulePullback B S hS
          (ObjectProperty.homMk a : schemeSpace U ⟶ X)).obj
        (sheafOfDifferentials B S hS f)) ↔
      IsZero (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)))

/-- **The chart-square comparison follows from the comparison for morphisms of schemes.**  On a
commuting square of étale charts, Stacks 04CU identifies the restriction of `Ω_{X/Y}` to the
chart with the sheaf of differentials of the square's scheme morphism read as a morphism of
represented algebraic spaces — `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`,
proved unconditionally — so the two vanish together, and the hypothesis turns the vanishing of
the latter into the vanishing of the scheme-level `Ω_{U/V}`.

The surjectivity of the chart is not used: the identification of Stacks 04CU holds on every
commuting square of étale charts. -/
theorem sheafOfDifferentialsChartComparison_of_schemeVanishing
    (hscheme : SheafOfDifferentialsSchemeVanishing B S hS) {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) : SheafOfDifferentialsChartComparison B S hS f := by
  intro U V a b ψ ha hb _ hcomm
  have hsq : (ObjectProperty.homMk a : schemeSpace U ⟶ X) ≫ f =
      schemeSpaceMap ψ ≫ (ObjectProperty.homMk b : schemeSpace V ⟶ Y) :=
    ObjectProperty.hom_ext _ hcomm.symm
  have e := sheafOfDifferentialsEtaleLocalizationIso B S hS f
    (ObjectProperty.homMk a : schemeSpace U ⟶ X) (schemeSpaceMap ψ)
    (ObjectProperty.homMk b : schemeSpace V ⟶ Y) (isEtale_of_presheaf_etale B S hS ha)
    (isEtale_of_presheaf_etale B S hS hb) hsq
  exact e.isZero_iff.trans (hscheme U V ψ)

/-- **The chart-square comparison of Stacks 04CU, proved.**  The vanishing comparison for the
morphisms of schemes of the site is
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeVanishing`, Stacks 04CS read at zero
objects. -/
theorem sheafOfDifferentialsChartComparison {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    SheafOfDifferentialsChartComparison B S hS f :=
  sheafOfDifferentialsChartComparison_of_schemeVanishing B S hS
    (sheafOfDifferentialsSchemeVanishing B S hS) f

/-- **Stacks 04G9**, granted the chart-square comparison.  A morphism `f : X ⟶ Y` of algebraic
spaces over `S` is formally unramified exactly when its sheaf of differentials `Ω_{X/Y}` is a
zero object.

Both directions pass through one commuting square of étale scheme charts with both chart maps
surjective. Formal unramifiedness of `f` is formal unramifiedness of the scheme morphism of
such a square by Stacks 04G8, and that is the vanishing of the sheaf of relative differentials
of the square's scheme morphism by Stacks 02H9; the chart-square comparison turns the latter
into the vanishing of the restriction of `Ω_{X/Y}` to the chart, and
`AlgebraicGeometry.Space.isZero_of_isZero_modulePullback_chart` into the vanishing of
`Ω_{X/Y}`. Conversely the restriction of a zero object is a zero object. In the direction that
starts from the vanishing a square has to be produced, and an atlas of the target together
with `AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift` produces one.

The tag is registered on
`AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials`, which is this
statement with the chart-square comparison replaced by the comparison for morphisms of schemes
that implies it.  This form is kept for the consumers that hold a chart comparison for one
morphism and nothing more. -/
theorem formallyUnramified_iff_isZero_sheafOfDifferentials_of_chart
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hchart : SheafOfDifferentialsChartComparison B S hS f) :
    FormallyUnramified f.hom ↔ IsZero (sheafOfDifferentials B S hS f) := by
  refine ⟨fun hf => ?_, fun hzero => ?_⟩
  · obtain ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, -, hdiag, hψ⟩ :=
      (formallyUnramified_iff_surjectiveEtaleChart B S hS X.2 Y.2 f.hom).mp hf
    exact isZero_of_isZero_modulePullback_chart B S hS U (ObjectProperty.homMk a)
      (isEtale_of_presheaf_etale B S hS haEtale) haSurj
      ((hchart U V a b ψ haEtale hbEtale haSurj hdiag).mpr
        ((Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials _).mp hψ))
  · obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.2.exists_atlas
    obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V b hbSurj hbEtale
    refine (formallyUnramified_iff_surjectiveEtaleChart B S hS X.2 Y.2 f.hom).mpr
      ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, hbSurj, hdiag.symm, ?_⟩
    refine (Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials _).mpr
      ((hchart U V a b ψ haEtale hbEtale haSurj hdiag.symm).mp ?_)
    have : (modulePullback B S hS
        (ObjectProperty.homMk a : schemeSpace U ⟶ X)).Additive :=
      (modulePullbackAdjunction B S hS _).left_adjoint_additive
    exact Functor.map_isZero _ hzero

/-- **Stacks 04G9.** A morphism `f : X ⟶ Y` of algebraic spaces over `S` is formally unramified
exactly when its sheaf of differentials `Ω_{X/Y}` is a zero object.

The invertibility clause of Stacks 04CS, read at zero objects for an arbitrary morphism of
schemes of the site, is `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeVanishing`;
Stacks 04CU turns it into the chart-square comparison that the proof consumes,
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison`, and
`AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials_of_chart` is the
proof proper; see there. -/
@[stacks 04G9, ega "IV 17.2.1" "more general"]
theorem formallyUnramified_iff_isZero_sheafOfDifferentials {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    FormallyUnramified f.hom ↔ IsZero (sheafOfDifferentials B S hS f) :=
  formallyUnramified_iff_isZero_sheafOfDifferentials_of_chart B S hS f
    (sheafOfDifferentialsChartComparison B S hS f)

end AlgebraicGeometry.Space

end
