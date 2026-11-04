module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartNonvanishingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The base change of a module to a chart scheme is its chart restriction

Let `X` be an algebraic space over `S` and let `𝓕` be a quasi-coherent `𝒪_X`-module.  The two
readings of `𝓕` on the scheme of an étale chart `A` of `X` which this tree carries are

* `AlgebraicGeometry.Space.chartRestrictionSchemeModule`, the restriction of `𝓕` to the Zariski
  site of `chartScheme A`, which the chartwise comparisons of the tensor powers of an invertible
  module are stated for; and
* `AlgebraicGeometry.Space.baseChangeModule`, the reading of `𝓕` on a scheme `U` of the site
  equipped with an arbitrary morphism `p : h_U ⟶ X`, which the relative-ampleness machinery and
  the first step of Stacks 0GUT are stated for.

At a chart — that is, when `p` is the structure morphism `A.1.hom` of an étale chart and `U` is
the chart's object — the two agree.  This file records that identification and transports
invertibility and ampleness across it, which is what lets the output of
`AlgebraicGeometry.Space.exists_affine_etale_cover_hasResolutionProperty_of_isRelativelyAmple`
be fed to the chartwise statements.

## Main results

* `AlgebraicGeometry.Space.baseChangeModuleIsoChartRestrictionSchemeModule`: the identification.
* `AlgebraicGeometry.Space.isInvertibleModule_chartRestrictionSchemeModule_of_baseChangeModule`
  and `AlgebraicGeometry.Space.isAmple_chartRestrictionSchemeModule_of_baseChangeModule`: the
  transport of invertibility and of ampleness from the `baseChangeModule` reading to the chart
  restriction.
* `AlgebraicGeometry.Space.etaleChartOfIsPullback`: the étale chart of `X` presented by a
  cartesian square over an étale chart of the target of a morphism `f : X ⟶ Y`, together with
  `AlgebraicGeometry.Space.etaleChartOfIsPullback_hom` and
  `AlgebraicGeometry.Space.toOver_etaleChartOfIsPullback` identifying its data.
* `AlgebraicGeometry.Space.isAmple_chartRestrictionSchemeModule_of_isRelativelyAmple` and
  `AlgebraicGeometry.Space.hasResolutionProperty_chartScheme_of_isRelativelyAmple`: the two
  conclusions of the first step of Stacks 0GUT, read on the chart of `X` the square presents.
* `AlgebraicGeometry.Space.isSurjective_etaleChartOfIsPullback` and
  `AlgebraicGeometry.Space.coversTop_etaleChartOfIsPullback`: that chart is surjective in the
  spelling `AlgebraicGeometry.Space.IsSurjective` which the covering statements of the small
  étale site consume, and therefore covers the final object of that site.

## Hypotheses carried, and why

`AlgebraicGeometry.Space.baseChangeModuleIsoChartRestrictionSchemeModule` carries
`hF : 𝓕.IsQuasicoherentOnSite`.  It is an input and not part of the conclusion: the comparison it
is built from, `AlgebraicGeometry.Space.restrictToChartIsoChartSpaceIdEtaleChart`, factors through
`AlgebraicGeometry.Space.chartSchemeModule`, which is defined only for a quasi-coherent module,
and the two readings are genuinely different functors on a module that is not quasi-coherent —
one is a Zariski sheafification of the étale sections, the other a Zariski restriction of an
étale inverse image.  In every intended use `𝓕` is invertible, hence quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible` (Stacks 0B8Q), so nothing is
lost.

## Implementation notes

The identification is not new mathematics; it is a change of spelling.
`AlgebraicGeometry.Space.restrictToChartIsoChartSpaceIdEtaleChart` already states it with the
right-hand side written out as a `restrictToChartScheme` at an identity chart, and
`AlgebraicGeometry.Space.baseChangeModule` is by definition exactly that term:
`AlgebraicGeometry.Space.chartSpace_eq_yoneda` makes the algebraic space a chart represents the
Yoneda algebraic space of the chart's object definitionally, and
`AlgebraicGeometry.Space.chartToSpace` at a chart is the structure morphism of that chart.  What
this file adds is the named statement at the `baseChangeModule` spelling, so that a consumer need
not rely on that chain of definitional unfoldings.

The transports are `Stacks.SheafOfModules.isInvertible_of_iso` — `Stacks.Ample.IsInvertibleModule`
is an `abbrev` for `Stacks.SheafOfModules.IsInvertible` with the sheaf condition supplied, so it
applies with no bridge — and `Stacks.RelativeVeryAmple.isAmple_congr`.  No file-local copy of
either is needed.

The chart presented by a cartesian square is built from
`AlgebraicGeometry.Space.isEtale_of_isPullback_yoneda` (Stacks 03FU for a representable source,
which needs no algebraic-space hypothesis) followed by
`AlgebraicGeometry.Space.presheaf_etale_of_isEtale`.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- **The reading of a quasi-coherent `𝒪_X`-module on the scheme of an étale chart along the
chart's structure morphism is its chart restriction.**

This is `AlgebraicGeometry.Space.restrictToChartIsoChartSpaceIdEtaleChart` with its right-hand
side spelled as `AlgebraicGeometry.Space.baseChangeModule`, which it is by definition. -/
def baseChangeModuleIsoChartRestrictionSchemeModule (A : SmallEtale B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    baseChangeModule B S hS F ((SmallEtale.toOver B S hS X.1).obj A) A.1.hom ≅
      chartRestrictionSchemeModule B S hS X F A :=
  (restrictToChartIsoChartSpaceIdEtaleChart B S hS X A F hF).symm

/-- **Invertibility of the chart restriction, from invertibility of the reading on the chart
scheme.**  Transport along
`AlgebraicGeometry.Space.baseChangeModuleIsoChartRestrictionSchemeModule`. -/
theorem isInvertibleModule_chartRestrictionSchemeModule_of_baseChangeModule
    (A : SmallEtale B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite)
    (hinv : Stacks.Ample.IsInvertibleModule (chartScheme A)
      (baseChangeModule B S hS F ((SmallEtale.toOver B S hS X.1).obj A) A.1.hom)) :
    Stacks.Ample.IsInvertibleModule (chartScheme A)
      (chartRestrictionSchemeModule B S hS X F A) :=
  have := hinv
  Stacks.SheafOfModules.isInvertible_of_iso _ _
    (baseChangeModuleIsoChartRestrictionSchemeModule B S hS X A F hF)

/-- **Ampleness of the chart restriction, from ampleness of the reading on the chart scheme.**
Transport along `AlgebraicGeometry.Space.baseChangeModuleIsoChartRestrictionSchemeModule` by
`Stacks.RelativeVeryAmple.isAmple_congr`. -/
theorem isAmple_chartRestrictionSchemeModule_of_baseChangeModule
    (A : SmallEtale B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite)
    (hinv : Stacks.Ample.IsInvertibleModule (chartScheme A)
      (baseChangeModule B S hS F ((SmallEtale.toOver B S hS X.1).obj A) A.1.hom))
    (hamp : @Stacks.Ample.IsAmple (chartScheme A)
      (baseChangeModule B S hS F ((SmallEtale.toOver B S hS X.1).obj A) A.1.hom) hinv) :
    @Stacks.Ample.IsAmple (chartScheme A) (chartRestrictionSchemeModule B S hS X F A)
      (isInvertibleModule_chartRestrictionSchemeModule_of_baseChangeModule
        B S hS X A F hF hinv) :=
  have := hinv
  have := isInvertibleModule_chartRestrictionSchemeModule_of_baseChangeModule
    B S hS X A F hF hinv
  (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (baseChangeModuleIsoChartRestrictionSchemeModule B S hS X A F hF)).mp hamp

/-! ### The chart of `X` presented by a cartesian square over an étale chart of `Y` -/

variable {Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {V U : BigFppfOver B S hS}

/-- **The étale chart of `X` presented by a cartesian square over an étale chart of `Y`.**  If
`g : h_V ⟶ Y` is étale and `p : h_U ⟶ X`, `q : U ⟶ V` present `U` as the fibre product
`V ×_Y X`, then `p` is an étale chart of `X`: étaleness of a morphism with representable source
is stable under base change (Stacks 03FU). -/
def etaleChartOfIsPullback {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk p,
    presheaf_etale_of_isEtale B S hS (isEtale_of_isPullback_yoneda B S hS hsq.flip hg)⟩

/-- The object of the big fppf site underlying
`AlgebraicGeometry.Space.etaleChartOfIsPullback` is the scheme the square presents. -/
theorem toOver_etaleChartOfIsPullback {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    (SmallEtale.toOver B S hS X.1).obj (etaleChartOfIsPullback B S hS X hg hsq) = U :=
  rfl

/-- The structure morphism of `AlgebraicGeometry.Space.etaleChartOfIsPullback` is the projection
the square provides. -/
theorem etaleChartOfIsPullback_hom {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    (etaleChartOfIsPullback B S hS X hg hsq).1.hom = p :=
  rfl

/-- The scheme of `AlgebraicGeometry.Space.etaleChartOfIsPullback` is the scheme the square
presents. -/
theorem chartScheme_etaleChartOfIsPullback {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    chartScheme (etaleChartOfIsPullback B S hS X hg hsq) =
      (BigFppfOver.toScheme B S hS).obj U :=
  rfl

/-- **The first step of Stacks 0GUT, read on the étale chart of `X` the square presents.**  Let
`L` be an invertible `f`-ample module on `X`, let `g : h_V ⟶ Y` be an étale morphism from an
affine scheme of the site, and let `p`, `q` present `U` as `V ×_Y X`.  Then the restriction of
`L` to the scheme of the étale chart of `X` given by `p` is ample.

This is `AlgebraicGeometry.Space.isAmple_baseChangeModule_of_isRelativelyAmple` carried across
`AlgebraicGeometry.Space.baseChangeModuleIsoChartRestrictionSchemeModule`.  Invertibility of `L`
on `X` is a hypothesis of Stacks 0D31 and hence of Stacks 0GUT, not something derived here; it
supplies both the invertibility of the chart restriction, through the instance
`AlgebraicGeometry.Space.isInvertibleModule_chartRestrictionSchemeModule`, and its
quasi-coherence, through Stacks 0B8Q. -/
theorem isAmple_chartRestrictionSchemeModule_of_isRelativelyAmple
    (L : Modules.{u, u} B S hS X.1 X.2) (hLinv : IsInvertibleModule X L)
    (hL : IsRelativelyAmple B S hS f L)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    letI A := etaleChartOfIsPullback B S hS X hg hsq
    ∃ hinv : Stacks.Ample.IsInvertibleModule (chartScheme A)
        (chartRestrictionSchemeModule B S hS X L A),
      @Stacks.Ample.IsAmple (chartScheme A) (chartRestrictionSchemeModule B S hS X L A) hinv := by
  have hLqc : L.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS X L (hLinv.toAlgebraicGeometry _ _ _)
  obtain ⟨hinv, hamp⟩ := isAmple_baseChangeModule_of_isRelativelyAmple hL V U hVaff g p q hsq
  exact ⟨isInvertibleModule_chartRestrictionSchemeModule_of_baseChangeModule
      B S hS X (etaleChartOfIsPullback B S hS X hg hsq) L hLqc hinv,
    isAmple_chartRestrictionSchemeModule_of_baseChangeModule
      B S hS X (etaleChartOfIsPullback B S hS X hg hsq) L hLqc hinv hamp⟩

/-- **The chart of `X` presented by a cartesian square over a surjective étale chart of `Y` is
surjective**, in the spelling
`AlgebraicGeometry.Space.IsSurjective` that the covering statements of the small étale site
consume, out of the `MorphismProperty.presheaf` spelling that the first step of Stacks 0GUT
records.

The bridge between the two spellings of surjectivity for a morphism from a scheme to an
algebraic space is Stacks 03H5,
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`; surjectivity then passes
to the base change by Stacks 03MH, here in the presheaf form
`AlgebraicGeometry.Space.isSurjective_of_isPullback_presheaf`. -/
theorem isSurjective_etaleChartOfIsPullback {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    (hgsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    IsSurjective B S hS (etaleChartOfIsPullback B S hS X hg hsq).1.hom :=
  isSurjective_of_isPullback_presheaf (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_yoneda B S hS V) X.2 Y.2 hsq.flip
    ((presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.2 V g).mp hgsurj)

/-- **The chart of `X` presented by a cartesian square over a surjective étale chart of `Y`
covers the final object of the small étale site of `X`**, so that it may be used as a one-element
cover.  This is `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` fed by
`AlgebraicGeometry.Space.isSurjective_etaleChartOfIsPullback`. -/
theorem coversTop_etaleChartOfIsPullback {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    (hgsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    (SmallEtale.topology B S hS X.1).CoversTop
      (fun _ : PUnit.{u + 2} => etaleChartOfIsPullback B S hS X hg hsq) :=
  SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 _
    (isSurjective_etaleChartOfIsPullback B S hS X hg hgsurj hsq)

/-- **The resolution property of the chart of `X` the square presents.**  This is
`AlgebraicGeometry.Space.hasResolutionProperty_baseChange_of_isRelativelyAmple` read at
`AlgebraicGeometry.Space.chartScheme`, which is the same scheme on the nose. -/
theorem hasResolutionProperty_chartScheme_of_isRelativelyAmple
    {L : Modules.{u, u} B S hS X.1 X.2} (hL : IsRelativelyAmple B S hS f L)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {g : yoneda.obj V ⟶ Y.1} (hg : IsEtale B S hS g)
    {p : yoneda.obj U ⟶ X.1} {q : U ⟶ V} (hsq : IsPullback p (yoneda.map q) f.hom g) :
    _root_.AlgebraicGeometry.HasResolutionProperty
      (chartScheme (etaleChartOfIsPullback B S hS X hg hsq)) :=
  hasResolutionProperty_baseChange_of_isRelativelyAmple hL V U hVaff g p q hsq

end AlgebraicGeometry.Space

end
