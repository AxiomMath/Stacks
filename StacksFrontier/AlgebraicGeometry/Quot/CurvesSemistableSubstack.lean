module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOverField
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SemistableLocusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.UniversallyBijectiveGlobalFunctions

/-!
# The open substack of semistable curves (Stacks 0E70)

Stacks 0E70 produces an open substack `Curves^{semistable} ⊂ Curves` such that

1. the classifying morphism of a family of curves `X ⟶ S` factors through it exactly when
   `X ⟶ S` is a semistable family of curves (Stacks 0E6Z), and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the following are equivalent:
   (a) the classifying morphism `Spec k ⟶ Curves` factors through it,
   (b) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of
   `X` is at least one and `X` has no rational tail,
   (c) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and
   `ω_X^{⊗ m}` is globally generated for every `m ≥ 2`.

`Curves^{semistable}` is the strictly full subcategory of semistable families; semistability passes
along morphisms of families (`AlgebraicGeometry.CurveFamily.isSemistableCurveFamily_of_hom`), so it
is a category fibred in groupoids over the big fppf site, `AlgebraicGeometry.curvesSubstack`.

## Main results

* `AlgebraicGeometry.curvesSemistable_isOpenSubstack`: **Stacks 0E70, the open substack**.
* `AlgebraicGeometry.curvesSemistable_isOpenSubstack_and_factors_iff`: **Stacks 0E70**, the whole
  statement.

## Implementation notes

As in Stacks 0E6U (`AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff`), the
classifying morphism of a family over `U` is a scheme-valued point `y` of `Curves` over `U`, and
that of a proper scheme `X` over `k` is any such point whose family is identified with the family
of curves `AlgebraicGeometry.curveFamilyOfScheme X`; `k = H⁰(X, 𝒪_X)` is the bijectivity of
`k ≅ Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)`, read as an isomorphism of rings, and `ω_X` is the dualizing sheaf
`Stacks.Duality.dualizingSheafOverField`, invertible on an at-worst-nodal curve.

## References

* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

open C1590Private

/-- **Stacks 0E70, the open substack.** `Curves^{semistable}`, the strictly full subcategory of
semistable families of curves (Stacks 0E6Z), is an open substack of `Curves`: semistability is
invariant under isomorphism, and the inclusion `Curves^{semistable} ⟶ Curves` is representable by
algebraic spaces and an open immersion. -/
theorem curvesSemistable_isOpenSubstack :
    ObjectProperty.IsClosedUnderIsomorphisms (IsSemistableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSemistableCurveFamily B hZ)
          (CurveFamily.isSemistableCurveFamily_of_hom B hZ)).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSemistableCurveFamily B hZ)
          (CurveFamily.isSemistableCurveFamily_of_hom B hZ)) :=
  isOpenImmersion_curvesSubstackInclusion <| isOpenCurvesLocus_isSemistableCurveFamily_of
    (isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres_of (hasEtaleLocalSchemeCharts B hZ))
    (hasUniversallyBijectiveGlobalFunctions_of (hasEtaleLocalSchemeCharts B hZ))
    (prestableSemistableFibresOpen B hZ)

/-- There is an open substack `Curves^{semistable} ⊂ Curves` — the strictly full subcategory of
semistable families of curves (Stacks 0E6Z), whose inclusion is representable by algebraic spaces
and an open immersion — such that

1. the classifying morphism of a family of curves `X ⟶ S` factors through it exactly when
   `X ⟶ S` is a semistable family of curves, and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1` (with `Spec k` in the site, so that
   its classifying morphism `Spec k ⟶ Curves` exists), the classifying morphism of `X` factors
   through it (a) exactly when (b) the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
   `k = H⁰(X, 𝒪_X)`, the genus of `X` is at least one and `X` has no rational tail, and (a)
   exactly when (c) the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
   `k = H⁰(X, 𝒪_X)` and `ω_X^{⊗ m}` is globally generated for every `m ≥ 2`. -/
@[stacks 0E70 "the whole statement: the open substack Curves^{semistable} and parts (1) and (2)"]
theorem curvesSemistable_isOpenSubstack_and_factors_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsSemistableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSemistableCurveFamily B hZ)
          (CurveFamily.isSemistableCurveFamily_of_hom B hZ)).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSemistableCurveFamily B hZ)
          (CurveFamily.isSemistableCurveFamily_of_hom B hZ))) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSemistableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSemistableCurveFamily B hZ) = y) ↔
        IsSemistableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSemistableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSemistableCurveFamily B hZ) = y) ↔
        letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
        Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ 1 ≤ genus X.hom ∧
            ∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSemistableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSemistableCurveFamily B hZ) = y) ↔
        letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
        haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
        ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
          (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)),
          haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hΓ
          haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
          letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
            hdim1 hnodal
          ∀ m : ℕ, 2 ≤ m → SheafOfModules.IsGeneratedByGlobalSections
            (tensorPower X.left.presheaf X.left.ringCatSheaf.2
              (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k))) m))) :=
  ⟨curvesSemistable_isOpenSubstack B hZ, fun U y hy => factors_curvesSemistable_iff B hZ U y hy,
    fun _ _ hk X _ hdim U y hy e =>
      ⟨factors_curvesSemistable_over_field_iff X hk hdim U y hy e,
        factors_curvesSemistable_over_field_iff_globallyGenerated X hk hdim U y hy e⟩⟩

end AlgebraicGeometry

end
