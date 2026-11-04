module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Regular and normal algebraic spaces

Regularity and normality of an algebraic space are the étale-local scheme properties
`AlgebraicGeometry.IsRegular` and `AlgebraicGeometry.IsNormal` asked of it through
`AlgebraicGeometry.Space.HasEtaleLocalProperty`: the space is regular, respectively normal,
when it admits a surjective étale atlas by a regular, respectively normal, scheme. With both
notions read off the same atlas, a regular algebraic space is normal because a regular scheme
is normal.

Normality of a scheme is local in the étale topology, so by Stacks 03E6 it makes sense for an
algebraic space, and by Stacks 03E8 the some-chart and every-chart forms agree. Since normality
of a scheme is here the condition that every local ring of its structure sheaf be a normal
domain, this is exactly the source's reading of normality of an algebraic space as a condition
on the local rings of its étale charts.

The consequence drawn here is the normality assertion of part (1) of Stacks 07U4, for an
arbitrary algebraic space equipped with normalization data: the normalization of such a space
is a normal algebraic space. It is the companion of
`AlgebraicGeometry.Space.NormalizationData.isIntegralHom_of_representable`, which is the
integrality assertion of the same part but only for a representable algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.IsNormal` is normality of an algebraic space over `S`.

## Main results

* `AlgebraicGeometry.Space.isNormal_of_isRegular`: a regular algebraic space is normal.
* `AlgebraicGeometry.Space.isNormal_iff_forall_etale`: an algebraic space is normal exactly
  when every étale scheme over it is a normal scheme. This is Stacks 03E8 at normality.
* `AlgebraicGeometry.Space.isNormal_iff_of_representable`: a representable algebraic space is
  normal exactly when its representing scheme is.
* `AlgebraicGeometry.Space.isNormal_of_iso_yoneda`: a presheaf isomorphic to the one
  represented by an object of the site is normal as soon as the underlying scheme of that
  object is.
* `AlgebraicGeometry.Space.NormalizationData.isNormal`: the normalization of an algebraic
  space equipped with normalization data is a normal algebraic space. This is the normality
  assertion of part (1) of Stacks 07U4.
* `AlgebraicGeometry.Space.NormalizationData.isNormal_of_representable`: the representable
  case of the previous result.

## Implementation notes

For the implication from regularity only an atlas is needed, so no algebraicity hypothesis is
imposed on the presheaf: the witnessing chart of regularity is itself a witnessing chart of
normality, and the scheme-level implication `AlgebraicGeometry.isNormal_of_isRegular` is applied
to it.

**The shape of the definition of normality.** Two idioms for an étale-local condition coexist in
this layer, and only one of them applies. `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` and
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint` — the idioms behind
`AlgebraicGeometry.Space.IsFlat` and `AlgebraicGeometry.Space.IsFlatAt` — test a
`CategoryTheory.MorphismProperty` of schemes on a commuting square of charts of a *morphism*,
and normality is not a property of a morphism. The idiom for an *absolute* étale-local property
of the space itself is `AlgebraicGeometry.Space.HasEtaleLocalProperty`, which is Stacks 03E6 and
takes a `CategoryTheory.ObjectProperty Scheme`; it is what `AlgebraicGeometry.Space.IsNoetherian`
uses for local Noetherianity and what
`StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace` uses for reducedness. Normality is
defined through it here, for the same reason.

The definition is an abbreviation, as `AlgebraicGeometry.Space.IsNoetherian` and
`AlgebraicGeometry.Space.IsFlat` are: a client holding a chart can use the existential directly
and the two theorems of Stacks 03E8 apply to it without an unfolding lemma. It is not a class and
no instance is synthesised through it.

**Why there is no tag on the definition.** The source has no tag for normality of an algebraic
space. It has Definition 03E6, which defines "`X` has `P`" for an étale-local property `P` of
schemes and is already carried by `AlgebraicGeometry.Space.HasEtaleLocalProperty`, together with
Remark 03E7, whose item (7) records that normality is such a property by Stacks 034F. That record
is itself a declaration of this library, `AlgebraicGeometry.isLocal_isNormal_etalePrecoverage`,
which carries `@[stacks 034F]`, so neither tag belongs on this definition.

**The locality, and what it buys.** Both halves of Stacks 03E8 instantiate at normality, which is
what `AlgebraicGeometry.Space.isNormal_iff_forall_etale` and
`AlgebraicGeometry.Space.isNormal_iff_of_representable` record: a client holding normality of the
space may deduce normality of an arbitrary étale chart of it, and not only the converse. The
some-chart existential remains the definition, so
`AlgebraicGeometry.Space.hasEtaleLocalProperty_of_representable` — the half of the representable
case that is free of locality — is still the cheapest way in, and it is what
`AlgebraicGeometry.Space.isNormal_of_iso_yoneda` uses.

Independence of the atlas for regularity is Stacks 03E8 as well, and it is not used here. Both of
its inputs are available if a client wants it: regularity of schemes is local for the étale
precoverage by `AlgebraicGeometry.isRegular_isLocal_etale`, and normality is local for the smooth
precoverage by `AlgebraicGeometry.isNormal_isLocal_smooth` (Stacks 034F), hence for the étale
precoverage, étale coverings being smooth ones.

**The scope of the 07U4 result.** Part (1) of Stacks 07U4 asserts two things of the normalization
of an algebraic space satisfying the equivalent conditions of Stacks 0BB1: that it is normal and
that the normalization morphism is integral.

Normality is proved here for an arbitrary algebraic space with normalization data, by
`AlgebraicGeometry.Space.NormalizationData.isNormal`. It needs *no* étale descent and no locality
of normality: the chart condition of `AlgebraicGeometry.Space.NormalizationData`, applied to an
atlas of the space, exhibits a surjective étale chart of the *normalization* whose underlying
scheme is the normalization scheme of the atlas, and that scheme is normal by Stacks 035Q. Since
`AlgebraicGeometry.Space.IsNormal` is the some-chart existential, that chart is already the whole
statement.

Integrality is not promoted here, and the reason is not étale descent of normality but descent
of *representability*: `AlgebraicGeometry.Space.IsIntegralHom` of the normalization morphism
requires its base change along an arbitrary morphism from a representable presheaf to be an
integral morphism of schemes, and the chart condition controls only the base changes over the
atlas. Discharging that is
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
`AlgebraicGeometry.IsIntegralHom`. That descent statement is proved unconditionally, in a file
this one does not import, as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isIntegralHom`, out of fppf
descent of integrality of morphisms of schemes
(`AlgebraicGeometry.isIntegralHom_descendsAlong_fppf`) rather than through the affine route and
`RingHom.CodescendsAlong RingHom.IsIntegral RingHom.FaithfullyFlat`, which neither Mathlib nor
this library has. So integrality in this generality is proved, one file downstream, as
`AlgebraicGeometry.Space.NormalizationData.isIntegralHom` in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIntegral`; the representable case, needing
no descent, is `AlgebraicGeometry.Space.NormalizationData.isIntegralHom_of_representable`.

Accordingly nothing here carries `@[stacks 07U4]`: part (1) is the conjunction of the two
assertions, and only normality is stated in this file. The conjunction is
`AlgebraicGeometry.Space.NormalizationData.isNormal_and_isIntegralHom`, which is where the tag
sits. That part (1) holds with no normalization data assumed — the data being constructed from
the hypotheses of the tag by
`AlgebraicGeometry.Space.nonempty_normalizationData` — is
`AlgebraicGeometry.Space.exists_normalizationData_isNormal_isIntegralHom`. A normalization of a
representable algebraic space is constructed separately, with no quotient to form, in
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction`.

## References

* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
* [Stacks Project, Tag 034F](https://stacks.math.columbia.edu/tag/034F)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E7](https://stacks.math.columbia.edu/tag/03E7)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BGT](https://stacks.math.columbia.edu/tag/0BGT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0BGT.** A regular algebraic space is normal: a surjective étale atlas by a
regular scheme is one by a normal scheme. -/
@[stacks 0BGT]
theorem isNormal_of_isRegular (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hreg : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsRegular X)) :
    HasEtaleLocalProperty B S hS F
      (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal X) := by
  obtain ⟨U, f, hsurjective, hetale, hregular⟩ := hreg
  exact ⟨U, f, hsurjective, hetale, _root_.AlgebraicGeometry.isNormal_of_isRegular _ hregular⟩

section Normality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over `S` is *normal* when the property `AlgebraicGeometry.IsNormal` of
schemes — every local ring of the structure sheaf is a normal domain — holds étale-locally on
it in the sense of `AlgebraicGeometry.Space.HasEtaleLocalProperty`, that is on some surjective
étale scheme chart.

This is Stacks 03E6 taken at normality, which Remark 03E7, item (7), records as a property of
schemes local in the étale topology. -/
abbrev IsNormal (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal X)

/-- **Stacks 03E8 at normality.** An algebraic space over `S` is normal — that is, some
surjective étale scheme chart of it is a normal scheme — exactly when the underlying scheme of
every object of the site étale over it is normal.

This is `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale` instantiated at normality,
which is possible because normality of a scheme is local for the étale precoverage
(`AlgebraicGeometry.isLocal_isNormal_etalePrecoverage`, Stacks 034F). -/
theorem isNormal_iff_forall_etale (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    IsNormal B S hS F ↔
      ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ F),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g →
        _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj V) :=
  exists_atlas_iff_forall_etale B S hS F
    (fun X : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal X) hF

/-- **Stacks 03E8 at normality, representable case.** A presheaf isomorphic to the one
represented by an object of the big fppf site of `S` is a normal algebraic space exactly when
the underlying scheme of that object is a normal scheme.

The direction that does not need locality of normality is
`AlgebraicGeometry.Space.isNormal_of_iso_yoneda`; the converse is
`AlgebraicGeometry.Space.exists_atlas_iff_of_representable`, which uses
`AlgebraicGeometry.isLocal_isNormal_etalePrecoverage`. -/
theorem isNormal_iff_of_representable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (X : BigFppfOver B S hS) (e : F ≅ yoneda.obj X) :
    IsNormal B S hS F ↔
      _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj X) :=
  exists_atlas_iff_of_representable B S hS F
    (fun Y : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal Y) X e

/-- A presheaf isomorphic to the one represented by an object of the big fppf site of `S` is a
normal algebraic space as soon as the underlying scheme of that object is a normal scheme: the
isomorphism is itself a surjective étale chart. -/
theorem isNormal_of_iso_yoneda {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : BigFppfOver B S hS) (e : F ≅ yoneda.obj X)
    (hX : _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj X)) :
    IsNormal B S hS F :=
  hasEtaleLocalProperty_of_representable B S hS F
    (fun Y : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal Y) X e hX

namespace NormalizationData

variable {B S hS}

/-- **Stacks 07U4, part (1): normality.** The normalization of an algebraic space over `S`
equipped with normalization data is a normal algebraic space over `S`.

Choose a surjective étale scheme atlas `f : U ⟶ F` of the space. The chart condition of
`AlgebraicGeometry.Space.NormalizationData` applied to `f` produces an object `Uν` of the site
whose underlying scheme is the normalization scheme of the underlying scheme of `U`, together
with a Cartesian square exhibiting `yoneda.obj Uν ⟶ D.space` as the base change of `f` along
the normalization morphism. Base change preserves the relatively representable forms of
surjectivity and étaleness, so that morphism is a surjective étale chart of `D.space`; and its
source is a normal scheme by Stacks 035Q, part (1). Since
`AlgebraicGeometry.Space.IsNormal` is the existence of one such chart, that is the statement.

No étale locality of normality is used: the chart condition hands over precisely the chart the
some-chart definition asks for.

It does **not** carry `@[stacks 07U4]`: part (1) asserts normality of the normalization *and*
integrality of the normalization morphism, and this is only the first of the two. The second is
`AlgebraicGeometry.Space.NormalizationData.isIntegralHom`, which needs effective descent of
representability and so lives one file downstream, and the conjunction carrying the tag is
`AlgebraicGeometry.Space.NormalizationData.isNormal_and_isIntegralHom`. -/
theorem isNormal {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    Space.IsNormal B S hS D.space := by
  obtain ⟨U, f, hfs, hfe⟩ := hF.exists_atlas
  obtain ⟨hU, Uν, p, g, e, hp, hpb⟩ := D.chart U f
    (isSurjective_of_presheafSurjective B S hS f hfs)
    (isEtale_of_presheaf_etale B S hS hfe)
  have base_change (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (h : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb.flip h
  refine ⟨Uν, g, base_change _ hfs, base_change _ hfe, ?_⟩
  exact @_root_.AlgebraicGeometry.isNormal_of_iso _ _ e
      (Scheme.isNormal_normalizationScheme _ hU)

/-- **Stacks 07U4, part (1) for a representable algebraic space: normality.** The
normalization of the algebraic space represented by an object of the big fppf site of `S` is a
normal algebraic space over `S`.

This is the representable case of `AlgebraicGeometry.Space.NormalizationData.isNormal`, kept
because a client holding a representable algebraic space has no algebraicity hypothesis to
supply: `AlgebraicGeometry.isAlgebraicSpace_yoneda` supplies it. -/
theorem isNormal_of_representable {X : BigFppfOver B S hS}
    (D : NormalizationData B S hS (yoneda.obj X)) :
    Space.IsNormal B S hS D.space :=
  D.isNormal (isAlgebraicSpace_yoneda B S hS X)

end NormalizationData

end Normality

end AlgebraicGeometry.Space

end
