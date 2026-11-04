module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal

/-!
# The normalization morphism of an algebraic space is integral

Let `F` be an algebraic space over `S` equipped with normalization data
`AlgebraicGeometry.Space.NormalizationData`. The chart condition of that structure makes the
base change of the normalization morphism along a surjective étale scheme chart an integral
morphism of algebraic spaces, which is
`AlgebraicGeometry.Space.NormalizationData.isIntegralHom_pullback_snd`. This file promotes that
chart-local statement to integrality of the normalization morphism itself, and so completes
part (1) of Stacks Tag 07U4 for an arbitrary algebraic space: its other half, normality of the
normalization, is `AlgebraicGeometry.Space.NormalizationData.isNormal`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.isIntegralHom`: the normalization morphism of an
  algebraic space equipped with normalization data is an integral morphism of algebraic spaces.
* `AlgebraicGeometry.Space.NormalizationData.isNormal_and_isIntegralHom`: the conjunction of
  that with normality of the normalization, which is part (1) of Stacks Tag 07U4.

## Implementation notes

The promotion is étale descent of *representability*, not of integrality:
`AlgebraicGeometry.Space.IsIntegralHom` of the normalization morphism asks for its base change
along an arbitrary morphism from a representable presheaf to be an integral morphism of schemes,
while the chart condition controls only the base changes over one atlas. The hypothesis that
discharges this is `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
`AlgebraicGeometry.IsIntegralHom`, which is now available unconditionally as
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isIntegralHom`; the implementation
notes of `StacksFrontier.AlgebraicGeometry.Spaces.Normal` record this as the then-missing input.

The chart-local hypothesis of `AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart` is the
represented-base-change form, which is stronger than
`AlgebraicGeometry.Space.IsIntegralHom`; the two are interchanged by
`AlgebraicGeometry.Space.isIntegralHom_iff_representable`, Stacks 03ZQ, which needs the fibre
product `F^ν ×_F U` to be an algebraic space and supplies that from
`AlgebraicGeometry.Space.isAlgebraicSpace_pullback`.

No hypothesis corresponding to the equivalent conditions of Stacks 0BB1 appears: the chart field
of `AlgebraicGeometry.Space.NormalizationData` already produces, for every surjective étale
scheme chart, the finiteness of the sets of irreducible components of its quasi-compact opens.
Quantifying over all normalization data rather than over a chosen one follows the convention of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationComparison`, and is the stronger statement.
The existence of normalization data for an arbitrary algebraic space satisfying condition (2) of
Stacks 0BB1 — the construction half of Tag 07U4 — is proved downstream of this file by
`AlgebraicGeometry.Space.nonempty_normalizationData`, so part (1) holds with
no data assumed; that combination is
`AlgebraicGeometry.Space.exists_normalizationData_isNormal_isIntegralHom`
(`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSiteChart`).

## References

* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace NormalizationData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 07U4, part (1): integrality.** The normalization morphism of an algebraic space
over `S` equipped with normalization data is an integral morphism of algebraic spaces.

Over a surjective étale scheme atlas of the space the base change of the normalization morphism
is integral by `AlgebraicGeometry.Space.NormalizationData.isIntegralHom_pullback_snd`, and
effective descent for integral morphisms along the atlas —
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isIntegralHom` — promotes that to
representability of the normalization morphism with integral represented base changes. -/
theorem isIntegralHom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    Space.IsIntegralHom B S hS D.hom := by
  obtain ⟨U, f, hfs, hfe⟩ := hF.exists_atlas
  have hUsp : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hPull : IsAlgebraicSpace B S hS (pullback D.hom f) :=
    isAlgebraicSpace_pullback B S hS D.hom f D.isAlgebraicSpace hUsp hF
  have hV := (isIntegralHom_iff_representable B S hS (pullback.snd D.hom f) hPull hUsp).1
    (D.isIntegralHom_pullback_snd hF U f
      (isSurjective_of_presheafSurjective B S hS f hfs)
      (isEtale_of_presheaf_etale B S hS hfe))
  have _hri := Stacks.Descent.isIntegralHom_respectsIso.{u}
  have hres := presheaf_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isIntegralHom B S hS)
    D.isAlgebraicSpace.isSheaf hF.isSheaf hfs hfe hV.2
  exact (isIntegralHom_iff_representable B S hS D.hom D.isAlgebraicSpace hF).2
    ⟨hres.rep, hres⟩

/-- **Stacks 07U4, part (1).** Let `F` be an algebraic space over `S` equipped with
normalization data. Then the normalization of `F` is a normal algebraic space over `S` and the
normalization morphism is integral.

The two halves are `AlgebraicGeometry.Space.NormalizationData.isNormal` and
`AlgebraicGeometry.Space.NormalizationData.isIntegralHom`. The hypotheses of Stacks 0BB1 are
carried by the chart field of `AlgebraicGeometry.Space.NormalizationData`, which produces for
every surjective étale scheme chart the finiteness of the sets of irreducible components of its
quasi-compact opens. -/
@[stacks 07U4 "part (1)"]
theorem isNormal_and_isIntegralHom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F) :
    Space.IsNormal B S hS D.space ∧ Space.IsIntegralHom B S hS D.hom :=
  ⟨D.isNormal hF, D.isIntegralHom hF⟩

end NormalizationData

end AlgebraicGeometry.Space

end
