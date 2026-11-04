module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction

/-!
# Tag 0BB2: the normalization of an algebraic space, as a defined object

`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction` proves that an algebraic
space `F` over `S` satisfying condition (2) of Tag 0BB1 — every quasi-compact open of every
étale scheme chart of `F` has finitely many irreducible components — admits normalization data:
an inhabitant of `AlgebraicGeometry.Space.NormalizationData`, which is an algebraic space `F^ν`
over `S` together with a morphism `ν_F : F^ν ⟶ F` whose base change along every surjective
étale scheme chart of `F` is the normalization of that chart.

This file names the normalization of such a space, which is **Tag 0BB2**:
`AlgebraicGeometry.Space.normalization` is the morphism `ν_F : F^ν ⟶ F` constructed in Tag 07U4,
for an algebraic space satisfying the equivalent conditions of Tag 0BB1. It is the morphism of
`AlgebraicGeometry.Space.normalizationData`, the construction of Tag 07U4
(`AlgebraicGeometry.Space.NormSpaceGluing.normalizationDataOfPresentation`: the quotient
`U^ν / R^ν` of the normalized étale presentation) run on a chosen surjective étale chart; no
normalization datum is an input.

It also records the existence together with part (1) of Tag 07U4 at the hypotheses the tag
itself carries, in `AlgebraicGeometry.Space.exists_normalizationData_isNormal_isIntegralHom`.

## Main definitions

* `AlgebraicGeometry.Space.normalizationPresheaf` is the normalization `F^ν` and
  `AlgebraicGeometry.Space.normalization` the normalization morphism `ν_F : F^ν ⟶ F`, which is
  **Tag 0BB2**.

## Main results

* `AlgebraicGeometry.Space.exists_normalizationData_isNormal_isIntegralHom`: an algebraic space
  satisfying condition (2) of Tag 0BB1 has normalization data, its normalization is normal and
  its normalization morphism is integral. This is the construction together with part (1) of
  Tag 07U4, at the hypotheses of the tag.
* `AlgebraicGeometry.Space.normalization_chart`: the defining chart condition — along every
  surjective étale scheme chart, `ν_F` base changes to the normalization of the chart.
* `AlgebraicGeometry.Space.existsUnique_iso_normalization`: every normalization datum of `F` is
  identified with `ν_F` by a unique isomorphism over `F`, so `ν_F` is independent, up to unique
  isomorphism, of the presentation the construction chooses.
* `AlgebraicGeometry.Space.isAlgebraicSpace_normalizationPresheaf`,
  `AlgebraicGeometry.Space.isNormal_normalizationPresheaf` and
  `AlgebraicGeometry.Space.isIntegralHom_normalization` carry part (1) of Tag 07U4 over to the
  morphism Tag 0BB2 names; `AlgebraicGeometry.Space.isSurjective_normalization`,
  `AlgebraicGeometry.Space.bijOn_codimensionZeroPoints_normalization` and
  `AlgebraicGeometry.Space.existsUnique_lift_normalization` do the same for parts (2) to (4) of
  Tag 0BB4.

## Implementation notes

The construction of Tag 07U4 needs a surjective étale presentation of `F`, and no presentation
is canonical, so the definition runs it on a chosen one, exactly as the source does ("if we
choose a surjective étale morphism `g : U → X` …"). The source then shows that the result is
independent of the choice up to unique isomorphism; here that is
`AlgebraicGeometry.Space.existsUnique_iso_normalization`, which compares `ν_F` with *every*
normalization datum, in particular with the construction at any other presentation.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB2](https://stacks.math.columbia.edu/tag/0BB2)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-! ### Tag 07U4 at the hypotheses of the tag -/

/-- **Stacks 07U4, the construction together with part (1), at the hypotheses of the tag.** Let
`F` be an algebraic space over `S` satisfying condition (2) of Tag 0BB1: every quasi-compact
open of every étale scheme chart of `F` has finitely many irreducible components. Then there
*is* normalization data for `F` — an algebraic space `F^ν` over `S` together with a morphism
`ν_F : F^ν ⟶ F` whose base change along every surjective étale scheme chart of `F` is the
normalization of that chart — with `F^ν` normal and `ν_F` integral.

Nothing is assumed beyond the two hypotheses the tag itself carries: no normalization data is
given, `F` is not assumed representable, and no bound on sizes is imposed. The datum is
`AlgebraicGeometry.Space.nonempty_normalizationData`, which forms `F^ν` as the quotient of a
normalized étale presentation, and the two properties are
`AlgebraicGeometry.Space.NormalizationData.isNormal_and_isIntegralHom`.

The other three parts of the tag are stated for an arbitrary
`AlgebraicGeometry.Space.NormalizationData` and so are unconditional as they stand; what this
statement adds to them is that their hypothesis is always satisfiable. Part (2), the
identification of the normalization of a representable algebraic space with the normalization
scheme of the representing scheme, is
`AlgebraicGeometry.Space.NormalizationData.exists_iso_yoneda_normalizationScheme`. Part (3), the
unique lift of a morphism carrying points of codimension zero to points of codimension zero, is
`AlgebraicGeometry.Space.NormalizationData.existsUnique_normalizationLift`. Part (4), the
identification of the normalization of the source of a smooth — in particular an étale —
morphism with the base change of the normalization of the target, is
`AlgebraicGeometry.Space.NormalizationData.isIso_pullbackLift_of_isSmooth`. -/
@[stacks 07U4 "the construction and part (1) at the hypotheses of the tag: an algebraic space \
satisfying condition (2) of Tag 0BB1 has normalization data, its normalization is normal, and \
its normalization morphism is integral"]
theorem exists_normalizationData_isNormal_isIntegralHom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) :
    ∃ D : NormalizationData B S hS F,
      Space.IsNormal B S hS D.space ∧ Space.IsIntegralHom B S hS D.hom :=
  (nonempty_normalizationData B S hS hF hfin).elim
    fun D => ⟨D, D.isNormal_and_isIntegralHom hF⟩

/-! ### Tag 0BB2: the normalization of an algebraic space -/

/-- **The normalization `F^ν` of an algebraic space satisfying the conditions of Tag 0BB1**, as a
presheaf on the big fppf site of `S`: the space of the normalization datum
`AlgebraicGeometry.Space.normalizationData` built by the construction of Tag 07U4, that is the
quotient `U^ν / R^ν` of the normalized étale presentation at a chosen surjective étale scheme
chart `U ⟶ F` with kernel pair `R = U ×_F U`.

This is the source of the normalization morphism `AlgebraicGeometry.Space.normalization`, which
carries the tag; the object is named here so that the morphism has a domain to be stated against,
exactly as `AlgebraicGeometry.Scheme.normalizationScheme` does for Tag 035N. That it is an
algebraic space over `S` is
`AlgebraicGeometry.Space.isAlgebraicSpace_normalizationPresheaf`, and that it is normal is
`AlgebraicGeometry.Space.isNormal_normalizationPresheaf`. -/
def normalizationPresheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (normalizationData B S hS hF hfin).space

/-- **Stacks 0BB2, the normalization of an algebraic space.** Let `F` be an algebraic space over
`S` satisfying the equivalent conditions of Tag 0BB1. The *normalization* of `F` is the morphism

`ν_F : F^ν ⟶ F`

constructed in Tag 07U4. Concretely it is the morphism of the normalization datum
`AlgebraicGeometry.Space.normalizationData`, which is the construction of Tag 07U4,
`AlgebraicGeometry.Space.NormSpaceGluing.normalizationDataOfPresentation`, run on a chosen
surjective étale scheme chart `w : h_U ⟶ F` and its kernel pair `R = U ×_F U`: the
normalizations of the charts `R^ν ⇉ U^ν` form an étale equivalence relation,
`F^ν = U^ν / R^ν` (`AlgebraicGeometry.Space.normalizationPresheaf`) is its quotient, an
algebraic space by Tag 02WW, and `ν_F` is the morphism `F^ν ⟶ F` through which the
normalization `U^ν ⟶ U ⟶ F` of the chart descends. No normalization datum or other structure is
an input: the definition depends on `F` and on the two hypotheses of the tag only.

**Defining properties.** `ν_F` is characterised, up to unique isomorphism over `F`, by its
*chart condition*: along every surjective étale scheme chart `U ⟶ F` its base change is the
normalization `U^ν ⟶ U` of the chart (`AlgebraicGeometry.Space.normalization_chart`). Any
morphism with this property — any `AlgebraicGeometry.Space.NormalizationData` for `F` — is
identified with `ν_F` by a unique isomorphism over `F`
(`AlgebraicGeometry.Space.existsUnique_iso_normalization`), so the choice of the chart made by
the construction affects nothing up to unique isomorphism, as in the source. `ν_F` is moreover
the universal morphism to `F` from a normal algebraic space which carries points of codimension
zero to points of codimension zero (`AlgebraicGeometry.Space.existsUnique_lift_normalization`).

**The theorems of Tag 07U4 about it.** Part (1): `F^ν` is an algebraic space
(`AlgebraicGeometry.Space.isAlgebraicSpace_normalizationPresheaf`), normal
(`AlgebraicGeometry.Space.isNormal_normalizationPresheaf`), and `ν_F` is integral
(`AlgebraicGeometry.Space.isIntegralHom_normalization`); at the hypotheses of the tag this is
also `AlgebraicGeometry.Space.exists_normalizationData_isNormal_isIntegralHom`. Parts (2) to (4)
— the comparison with the normalization of a scheme, the unique lift `f^ν` of a morphism
preserving codimension-zero points, and `X^ν ≅ X ×_Y Y^ν` along a smooth morphism — are
`AlgebraicGeometry.Space.NormalizationData.exists_iso_yoneda_normalizationScheme`,
`AlgebraicGeometry.Space.NormalizationData.existsUnique_normalizationLift` and
`AlgebraicGeometry.Space.NormalizationData.isIso_pullbackLift_of_isSmooth`, which hold for every
normalization datum and so in particular for `AlgebraicGeometry.Space.normalizationData`, whose
morphism this is. Surjectivity and the bijection on codimension-zero points (Tag 0BB4) are
`AlgebraicGeometry.Space.isSurjective_normalization` and
`AlgebraicGeometry.Space.bijOn_codimensionZeroPoints_normalization`.

The hypothesis carried is condition (2) of Tag 0BB1,
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents`, which the comparisons of that
tag —
`AlgebraicGeometry.Space.exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents`,
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_iff_finite_codimensionZeroPoints`,
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_iff_finite_irreducibleComponents`
and `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_iff_of_isRepresentable` —
identify with each of the other conditions, so it is the hypothesis Tag 0BB2 itself carries.
Nothing further is assumed: `F` is not assumed representable and no bound on sizes is
imposed. -/
@[stacks 0BB2 "the normalization ν_F : F^ν ⟶ F of an algebraic space satisfying the conditions \
of Tag 0BB1, defined as the construction of Tag 07U4 (the quotient of the normalized étale \
presentation); unique up to unique isomorphism over F by existsUnique_iso_normalization"]
def normalization (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F) :
    normalizationPresheaf B S hS hF hfin ⟶ F :=
  (normalizationData B S hS hF hfin).hom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  (hfin : HasLocallyFiniteIrreducibleComponents B S hS F)

/-- **The normalization of an algebraic space is again an algebraic space over `S`**, by the
corresponding field of the normalization datum. -/
theorem isAlgebraicSpace_normalizationPresheaf :
    IsAlgebraicSpace B S hS (normalizationPresheaf B S hS hF hfin) :=
  (normalizationData B S hS hF hfin).isAlgebraicSpace

/-- **The chart condition defining the normalization.** Along every surjective étale scheme chart
`f : h_U ⟶ F` the normalization morphism `ν_F` base changes to the normalization of the chart:
there are a scheme `U^ν` of the site, isomorphic to the normalization scheme of `U` compatibly
with the projections to `U`, and a cartesian square with sides `ν_F` and `U^ν ⟶ U`. -/
theorem normalization_chart (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : IsSurjective B S hS f) (hfe : IsEtale B S hS f) :
    ∃ (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
        IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
          (irreducibleComponents V).Finite)
      (Uν : BigFppfOver B S hS) (p : Uν ⟶ U)
      (g : yoneda.obj Uν ⟶ normalizationPresheaf B S hS hF hfin)
      (e : ((BigFppfOver.toScheme B S hS).obj Uν) ≅
        Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU),
        (BigFppfOver.toScheme B S hS).map p =
          e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU ∧
        IsPullback g (yoneda.map p) (normalization B S hS hF hfin) f :=
  (normalizationData B S hS hF hfin).chart U f hf hfe

/-- **The normalization of an algebraic space is unique up to unique isomorphism.** Every
normalization datum `D` of `F` — an algebraic space with a morphism to `F` satisfying the chart
condition `AlgebraicGeometry.Space.normalization_chart` — is identified with the normalization
`ν_F : F^ν ⟶ F` of Tag 0BB2 by a unique isomorphism over `F`. So `ν_F` does not depend, up to
unique isomorphism, on the presentation the construction of Tag 07U4 chooses. -/
theorem existsUnique_iso_normalization (D : NormalizationData B S hS F) :
    ∃! e : normalizationPresheaf B S hS hF hfin ≅ D.space,
      e.hom ≫ D.hom = normalization B S hS hF hfin :=
  (normalizationData B S hS hF hfin).existsUnique_iso_hom D hF

/-- **The normalization of an algebraic space is normal.** This is the normality clause of
part (1) of Tag 07U4 at the morphism Tag 0BB2 names; it is untagged because the tag sits on
`AlgebraicGeometry.Space.exists_normalizationData_isNormal_isIntegralHom`, which states both
properties at the hypotheses of the tag. -/
theorem isNormal_normalizationPresheaf :
    Space.IsNormal B S hS (normalizationPresheaf B S hS hF hfin) :=
  ((normalizationData B S hS hF hfin).isNormal_and_isIntegralHom hF).1

/-- **The normalization morphism of an algebraic space is integral.** This is the integrality
clause of part (1) of Tag 07U4 at the morphism Tag 0BB2 names, untagged for the reason given at
`AlgebraicGeometry.Space.isNormal_normalizationPresheaf`. -/
theorem isIntegralHom_normalization :
    Space.IsIntegralHom B S hS (normalization B S hS hF hfin) :=
  ((normalizationData B S hS hF hfin).isNormal_and_isIntegralHom hF).2

/-- **The normalization morphism of an algebraic space is surjective**, Tag 0BB4 part (2) at the
morphism Tag 0BB2 names. -/
theorem isSurjective_normalization :
    IsSurjective B S hS (normalization B S hS hF hfin) :=
  (normalizationData B S hS hF hfin).isSurjective_hom hF

/-- **The normalization morphism of an algebraic space is a bijection on points of codimension
zero**, Tag 0BB4 part (3) at the morphism Tag 0BB2 names. -/
theorem bijOn_codimensionZeroPoints_normalization :
    Set.BijOn (pointsMap B S hS (normalizationPresheaf B S hS hF hfin)
        (normalization B S hS hF hfin))
      {x : points B S hS (normalizationPresheaf B S hS hF hfin) | localRingDimension B S hS x = 0}
      {x : points B S hS F | localRingDimension B S hS x = 0} :=
  (normalizationData B S hS hF hfin).bijOn_codimensionZeroPoints_hom hF

/-- **The universal property of the normalization of an algebraic space**, Tag 0BB4 part (4) at
the morphism Tag 0BB2 names: a morphism to `F` from a normal algebraic space which carries points
of codimension zero to points of codimension zero factors uniquely through `ν_F`. -/
theorem existsUnique_lift_normalization {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z)
    (hZnormal : HasEtaleLocalProperty B S hS Z fun Y : Scheme.{u} => AlgebraicGeometry.IsNormal Y)
    (f : Z ⟶ F)
    (hgeneric : ∀ z : points B S hS Z, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS Z f z) = 0) :
    ∃! g : Z ⟶ normalizationPresheaf B S hS hF hfin, g ≫ normalization B S hS hF hfin = f :=
  (normalizationData B S hS hF hfin).existsUnique_lift_hom hF hZ hZnormal f hgeneric

end AlgebraicGeometry.Space

end
