module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing

/-!
# Regular functions inject into meromorphic functions on every étale chart

Let `X` be an algebraic space over a scheme `S` satisfying the two standing hypotheses of
Stacks 0EN6: every weakly associated point of `X` has codimension `0`, and `X` has locally
finite irreducible components.  Over an *affine* object `U` of the small étale site of `X` the
ring `𝒦_X(U)` of meromorphic functions is the total ring of fractions of `𝒪_X(U)`
(`AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj`), and the localization
map of a total ring of fractions is injective; so `𝒪_X(U) ⟶ 𝒦_X(U)` is injective there.

This file removes the affineness hypothesis.  The affine opens of the scheme underlying an
arbitrary étale chart `U`, read as étale charts over `U` by
`AlgebraicGeometry.Space.openChart`, generate a covering sieve of `U`, so a sheaf on the small
étale site is separated for that family: two sections over `U` which agree on every affine open
of the chart are equal.  Applying this to the structure sheaf, and the affine case to each
affine open, gives injectivity of `𝒪_X(U) ⟶ 𝒦_X(U)` for every `U`.

## Main results

* `AlgebraicGeometry.Space.eq_of_openChart_restriction_eq`: a sheaf of types on the small étale
  site is separated for the family of affine opens of a chart, and
  `AlgebraicGeometry.Space.eq_of_openChart_restriction_eq_commRingCat` is the same statement for
  a sheaf of commutative rings.
* `AlgebraicGeometry.Space.injective_toMeromorphicFunctionSheaf_app_of_isAffine`: over an affine
  chart, regular functions inject into meromorphic functions.
* `AlgebraicGeometry.Space.injective_toMeromorphicFunctionSheaf_app`: the same over an arbitrary
  chart.
* `AlgebraicGeometry.Space.eq_of_openChart_restriction_eq_meromorphic`: two meromorphic
  functions over a chart which agree on every affine open of the chart are equal.

## Implementation notes

The covering family is supplied by
`AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology`, which turns any open cover
of the scheme underlying a chart into a covering sieve of that chart; the cover used here is the
family of all affine opens, which covers by `AlgebraicGeometry.iSup_affineOpens_eq_top`.  That
is the general form of `AlgebraicGeometry.Space.SmallEtale.etalePrecoverage_openChartInclusion`,
which states the same fact for the affine opens specifically but in the étale precoverage of
*schemes*.

Note that `AlgebraicGeometry.Scheme.affineOpens` is cut out by
`AlgebraicGeometry.IsAffineOpen`, which unfolds to affineness of the open subscheme; since
`AlgebraicGeometry.Space.chartScheme_openChart` holds by `rfl`, a witness of
`IsAffineOpen O` *is* a witness that the chart `openChart … U O` has affine underlying scheme,
and no transport is needed.

The separatedness statement is given twice, once for `Type` coefficients and once for
`CommRingCat` coefficients; the second is *not* deduced from the first.  For `Type`
coefficients the sheaf condition is `CategoryTheory.Presieve.IsSheaf` and separatedness is
`CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`, while for `CommRingCat` coefficients it is
`CategoryTheory.Presheaf.IsSheaf` and separatedness is
`CategoryTheory.Presheaf.IsSheaf.isSeparated`, which goes through corepresentability of the
forgetful functor rather than through
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`.  Deducing one from the other along the
latter is not available here: the small étale site has its objects one universe above its
morphisms, so Mathlib's forgetful comparison — which asks the coefficients to have limits of the
size of the site — does not apply, exactly as recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf`.

The `Algebra` instance in the statement of
`AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj` is introduced by a `letI`
inside that statement, so a caller must reintroduce the same `letI`; with it in scope the
`algebraMap` of the total ring of fractions is the component of `𝒪_X ⟶ 𝒦_X` by `rfl`.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

/-! ### Separatedness for the affine opens of a chart -/

section Separated

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **A sheaf of types on the small étale site is separated for the affine opens of a chart.**
Two sections over an étale chart `U` whose restrictions to the chart cut out by every affine
open of the scheme underlying `U` agree are equal. -/
theorem eq_of_openChart_restriction_eq (G : (SmallEtale B S hS F)ᵒᵖ ⥤ Type v)
    (hG : Presieve.IsSheaf (SmallEtale.topology B S hS F) G) (U : SmallEtale B S hS F)
    {a b : G.obj (op U)}
    (h : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      G.map (openChartInclusion B S hS F U O).op a =
        G.map (openChartInclusion B S hS F U O).op b) :
    a = b := by
  refine (hG _ (ofArrows_openChartInclusion_mem_topology B S hS F U
    (fun O : (chartScheme U).affineOpens ↦ (O : (chartScheme U).Opens))
    (iSup_affineOpens_eq_top _))).isSeparatedFor.ext ?_
  intro V f hf
  obtain ⟨O, g, rfl⟩ := Sieve.ofArrows.exists hf
  simp only [op_comp, G.map_comp, types_comp_apply, h O.1 O.2]

/-- **A sheaf of commutative rings on the small étale site is separated for the affine opens of a
chart.**  This is `AlgebraicGeometry.Space.eq_of_openChart_restriction_eq` for `CommRingCat`
coefficients. -/
theorem eq_of_openChart_restriction_eq_commRingCat
    (G : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{v})
    (hG : Presheaf.IsSheaf (SmallEtale.topology B S hS F) G) (U : SmallEtale B S hS F)
    {a b : G.obj (op U)}
    (h : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      (G.map (openChartInclusion B S hS F U O).op).hom a =
        (G.map (openChartInclusion B S hS F U O).op).hom b) :
    a = b := by
  refine hG.isSeparated U _ (ofArrows_openChartInclusion_mem_topology B S hS F U
    (fun O : (chartScheme U).affineOpens ↦ (O : (chartScheme U).Opens))
    (iSup_affineOpens_eq_top _)) a b ?_
  intro V f hf
  obtain ⟨O, g, rfl⟩ := Sieve.ofArrows.exists hf
  simp only [op_comp, G.map_comp, CommRingCat.comp_apply, h O.1 O.2]

end Separated

/-! ### Regular functions inject into meromorphic functions -/

section Injective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Over an affine chart, regular functions inject into meromorphic functions.**  Under the two
standing hypotheses of Stacks 0EN6, the ring `𝒦_X(U)` of meromorphic functions over an affine
object `U` of the small étale site is the total ring of fractions of `𝒪_X(U)`, and the
localization map of a total ring of fractions is injective. -/
theorem injective_toMeromorphicFunctionSheaf_app_of_isAffine
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (chartScheme U)) :
    Function.Injective (((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom) := by
  let : Algebra ((structurePresheaf B S hS X.1).obj (op U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin U hU
  have h := IsFractionRing.injective ((structurePresheaf B S hS X.1).obj (op U))
    ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U))
  have e : algebraMap ((structurePresheaf B S hS X.1).obj (op U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) =
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom := rfl
  rwa [e] at h

/-- **Two meromorphic functions over a chart which agree on every affine open of the chart are
equal.**  This is `AlgebraicGeometry.Space.eq_of_openChart_restriction_eq_commRingCat` for the
sheaf of meromorphic functions. -/
theorem eq_of_openChart_restriction_eq_meromorphic (U : SmallEtale B S hS X.1)
    {a b : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)}
    (h : ∀ O : (chartScheme U).Opens, IsAffineOpen O →
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
          (openChartInclusion B S hS X.1 U O).op).hom a =
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
          (openChartInclusion B S hS X.1 U O).op).hom b) :
    a = b :=
  eq_of_openChart_restriction_eq_commRingCat B S hS X.1 _
    (meromorphicFunctionSheaf B S hS X.1 X.2).property U h

/-- **Regular functions inject into meromorphic functions over every étale chart.**  Under the
two standing hypotheses of Stacks 0EN6 the map `𝒪_X(U) ⟶ 𝒦_X(U)` is injective for every object
`U` of the small étale site, affine or not: two regular functions with the same image agree on
every affine open of the chart by the affine case and naturality of `𝒪_X ⟶ 𝒦_X`, hence agree
because `𝒪_X` is a sheaf. -/
theorem injective_toMeromorphicFunctionSheaf_app
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1) :
    Function.Injective (((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom) := by
  intro s t hst
  refine eq_of_openChart_restriction_eq_commRingCat B S hS X.1
    (structureSheaf B S hS X.1 X.2).obj (structureSheaf B S hS X.1 X.2).property U ?_
  intro O hO
  refine injective_toMeromorphicFunctionSheaf_app_of_isAffine B S hS X hwa hfin
    (openChart B S hS X.1 U O) hO ?_
  have hnat : ∀ x : (structureSheaf B S hS X.1 X.2).obj.obj (op U),
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app
            (op (openChart B S hS X.1 U O))).hom
          (((structureSheaf B S hS X.1 X.2).obj.map
            (openChartInclusion B S hS X.1 U O).op).hom x) =
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
            (openChartInclusion B S hS X.1 U O).op).hom
          (((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom x) := fun x ↦ by
    simpa only [CommRingCat.comp_apply] using ConcreteCategory.congr_hom
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.naturality
        (openChartInclusion B S hS X.1 U O).op) x
  rw [hnat s, hnat t, hst]

end Injective

end AlgebraicGeometry.Space

end
