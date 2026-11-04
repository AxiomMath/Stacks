module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableGenusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableGenusLociOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableHasGenusIff
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SemistableLocusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.UniversallyBijectiveGlobalFunctions

/-!
# `Curves^{semistable} = ∐_{g ≥ 1} Curves^{semistable}_g` (Stacks 0E71)

**Stacks 0E71.** There is a decomposition into open and closed substacks
`Curves^{semistable} = ∐_{g ≥ 1} Curves^{semistable}_g` where each `Curves^{semistable}_g` is
characterized as follows:

1. given a family of curves `f : X → S`, the classifying morphism `S → Curves` factors through
   `Curves^{semistable}_g` exactly when `X → S` is a semistable family of curves and `R¹f_*𝒪_X`
   is a locally free `𝒪_S`-module of rank `g`;
2. given a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the following are equivalent:
   (a) the classifying morphism `Spec(k) → Curves` factors through `Curves^{semistable}_g`,
   (b) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of
   `X` is `g`, and `X` has no rational tail,
   (c) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of
   `X` is `g`, and `ω_X^{⊗m}` is globally generated for `m ≥ 2`.

## Main results

In the namespace `AlgebraicGeometry`:

* `curvesSemistableOfGenus_isOpenSubstack_and_factors_iff`: **Stacks 0E71**, the decomposition
  and part (1).
* `factors_curvesSemistableOfGenus_over_field_iff_noRationalTail_and_globallyGenerated`:
  **Stacks 0E71**, part (2).

## Implementation notes

`Curves^{semistable}_g` is the strictly full subcategory of families of curves that are
semistable with all fibres of genus `g`, `AlgebraicGeometry.IsSemistableCurveFamilyOfFibreGenus`.
That it is cut out by the rank of `R¹f_*𝒪_X` is part (1). The decomposition is read as follows:
each `Curves^{semistable}_g` is an open substack of `Curves` contained in `Curves^{semistable}`,
and over every semistable family the loci of the `Curves^{semistable}_g` are open and closed
subsets of its base, pairwise disjoint, empty for `g = 0`, and covering the base for `g ≥ 1`.

## References

* [Stacks Project, Tag 0E71](https://stacks.math.columbia.edu/tag/0E71)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
-/

@[expose] public section

open CategoryTheory
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

open C1590Private

/-- The semistable locus is open, from the field-fibre and prestable inputs. -/
private theorem isOpenCurvesLocus_isSemistableCurveFamily :
    IsOpenCurvesLocus B hZ (IsSemistableCurveFamily B hZ) :=
  isOpenCurvesLocus_isSemistableCurveFamily_of
    (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
      (hasEtaleLocalSchemeCharts B hZ))
    (hasUniversallyBijectiveGlobalFunctions_of (hasEtaleLocalSchemeCharts B hZ))
    (prestableSemistableFibresOpen B hZ)

/-- The semistable genus-`g` locus is open. -/
private theorem isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g) :=
  C1590Private.isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus
    (isOpenCurvesLocus_isSemistableCurveFamily B hZ)
    (prestableGenusLociOpen_of (hasEtaleLocalSchemeCharts B hZ)) g

/-- For every `g`, `Curves^{semistable}_g` is an open substack of `Curves` contained in
`Curves^{semistable}`: its inclusion is representable by algebraic spaces and an open immersion.
Part (1): the classifying morphism of a family of curves `f : X → S` factors through
`Curves^{semistable}_g` exactly when `f` is semistable and `R¹f_*𝒪_X` is a locally free
`𝒪_S`-module of rank `g`. Over every semistable family with base `S`, the loci of the
`Curves^{semistable}_g` are open and closed subsets of `S`, pairwise disjoint, empty for `g = 0`
and covering `S` for `g ≥ 1`: so `Curves^{semistable} = ∐_{g ≥ 1} Curves^{semistable}_g` as open
and closed substacks. -/
@[stacks 0E71 "the decomposition Curves^{semistable} = ∐_{g ≥ 1} Curves^{semistable}_g into \
open and closed substacks, and part (1)"]
theorem curvesSemistableOfGenus_isOpenSubstack_and_factors_iff :
    (∀ g : ℕ,
      ((show ObjectProperty (CurveFamily B hZ) from
          IsSemistableCurveFamilyOfFibreGenus B hZ g).IsClosedUnderIsomorphisms ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g)
            (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus
              (isOpenCurvesLocus_isSemistableCurveFamily_of
                (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
                  (hasEtaleLocalSchemeCharts B hZ))
                (hasUniversallyBijectiveGlobalFunctions_of (hasEtaleLocalSchemeCharts B hZ))
                (prestableSemistableFibresOpen B hZ))
              (prestableGenusLociOpen_of (hasEtaleLocalSchemeCharts B hZ)) g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsSemistableCurveFamilyOfFibreGenus B hZ g)
            (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus
              (isOpenCurvesLocus_isSemistableCurveFamily_of
                (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of
                  (hasEtaleLocalSchemeCharts B hZ))
                (hasUniversallyBijectiveGlobalFunctions_of (hasEtaleLocalSchemeCharts B hZ))
                (prestableSemistableFibresOpen B hZ))
              (prestableGenusLociOpen_of (hasEtaleLocalSchemeCharts B hZ)) g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ,
        IsSemistableCurveFamilyOfFibreGenus B hZ g X → IsSemistableCurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsSemistableCurveFamilyOfFibreGenus B hZ g),
            z ⋙ ObjectProperty.ι (IsSemistableCurveFamilyOfFibreGenus B hZ g) = y) ↔
          IsSemistableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
            CurveFamily.HasGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g)) ∧
    ∀ G : CurveFamily B hZ, IsSemistableCurveFamily B hZ G →
      ∃ Ω : ℕ → Set ((BigFppfOver.toScheme B integerBase hZ).obj G.base),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          Ω 0 = ∅ ∧ ⋃ (g : ℕ) (_ : 1 ≤ g), Ω g = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsSemistableCurveFamilyOfFibreGenus B hZ g F ↔
              Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ Ω g :=
  curvesSemistableOfGenus_isOpenSubstack_and_factors_iff_of
    (isOpenCurvesLocus_isSemistableCurveFamily B hZ)
    (prestableGenusLociOpen_of (hasEtaleLocalSchemeCharts B hZ))
    (prestableHasGenusIff_of (hasEtaleLocalSchemeCharts B hZ))

/-- Let `g ≥ 1` and let `X` be a proper scheme of dimension at most one over a field `k` (with
`Spec k` in the site, so that the classifying morphism `Spec k ⟶ Curves` of `X` exists). The
classifying morphism of `X` factors through `Curves^{semistable}_g` (a) exactly when (b) the
singularities of `X` are at-worst-nodal, `dim X = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is `g`
and `X` has no rational tail, and (a) exactly when (c) the singularities of `X` are
at-worst-nodal, `dim X = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is `g` and `ω_X^{⊗m}` is globally
generated for every `m ≥ 2`. -/
@[stacks 0E71 "part (2): (a) ⇔ (b) and (a) ⇔ (c), for a proper scheme of dimension at most one \
over a field"]
theorem factors_curvesSemistableOfGenus_over_field_iff_noRationalTail_and_globallyGenerated
    {g : ℕ} (hg : 1 ≤ g)
    {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamilyOfFibreGenus B hZ g) = y) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g ∧
          ∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
    ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamilyOfFibreGenus B hZ g) = y) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
        (hdim1 : topologicalKrullDim X.left = 1)
        (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)),
        haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hΓ
        haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
        letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
          hdim1 hnodal
        genus X.hom = g ∧ ∀ m : ℕ, 2 ≤ m → SheafOfModules.IsGeneratedByGlobalSections
          (tensorPower X.left.presheaf X.left.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k))) m)) :=
  ⟨factors_curvesSemistableOfGenus_over_field_iff_noRationalTail hg
      (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus B hZ g) X hk hdim U y hy e,
    factors_curvesSemistableOfGenus_over_field_iff_globallyGenerated
      (isOpenCurvesLocus_isSemistableCurveFamilyOfFibreGenus B hZ g) X hk hdim U y hy e⟩

end AlgebraicGeometry

end
