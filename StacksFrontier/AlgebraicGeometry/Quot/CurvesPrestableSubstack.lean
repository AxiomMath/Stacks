module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.H0FibreRankSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci

/-!
# The substack of prestable curves (Stacks 0E6U)

Stacks 0E6U produces an open substack `Curves^{prestable} ⊂ Curves` such that

1. the classifying morphism of a family of curves `X ⟶ S` factors through it exactly when
   `X ⟶ S` is a prestable family of curves (Stacks 0E6T), and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
   `Spec k ⟶ Curves` factors through it exactly when the singularities of `X` are
   at-worst-nodal, `dim(X) = 1` and `k = H⁰(X, 𝒪_X)`.

`Curves^{prestable}` is the strictly full subcategory of prestable families; prestability passes
along morphisms of families (`AlgebraicGeometry.CurveFamily.isPrestableCurveFamily_of_hom`), so
it is a category fibred in groupoids over the big fppf site, `AlgebraicGeometry.curvesSubstack`.

## Main results

* `AlgebraicGeometry.factors_curvesPrestable_iff`: part (1), a family factors through
  `Curves^{prestable}` exactly when it is prestable.
* `AlgebraicGeometry.factors_curvesPrestable_over_field_iff`: part (2), the criterion over a
  field.
* `AlgebraicGeometry.isOpenCurvesLocus_isPrestableCurveFamily`: condition (o) of Section 0E0E for
  `Curves^{prestable}`.
* `AlgebraicGeometry.curvesPrestable_isOpenSubstack`: `Curves^{prestable}` is an open substack.
* `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff`: the whole statement.

## Implementation notes

The family of curves of a proper scheme `X` of dimension at most one over a field `k` is
`AlgebraicGeometry.curveFamilyOfScheme`; `k = H⁰(X, 𝒪_X)` is the bijectivity of
`k ≅ Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)`, read as an isomorphism of rings. The singularity condition is
`Stacks.Curves.HasAtWorstNodalSingularities` (Stacks 0C47).

## References

* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0BY5](https://stacks.math.columbia.edu/tag/0BY5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry


variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The substack `Curves^{prestable}` and its universal properties -/

/-- The classifying morphism of a family of curves `X ⟶ S` factors through the strictly full
subcategory `Curves^{prestable}` of prestable families (Stacks 0E6T) exactly when `X ⟶ S` is
prestable: a scheme-valued point `y` of `Curves` over `U` lifts to `Curves^{prestable}` exactly
when the family `y(U)` it classifies is prestable. -/
@[stacks 0E6U "part (1)"]
theorem factors_curvesPrestable_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
      IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact (z.obj _).property
  · intro h
    exact ⟨ObjectProperty.lift _ y fun T =>
      CurveFamily.isPrestableCurveFamily_of_hom (y.map (Over.homMk T.hom (by simp))) h, rfl⟩

/-- Let `X` be a proper scheme over a field `k` with `dim(X) ≤ 1` (with `Spec k` in the site, so
that its classifying morphism `Spec k ⟶ Curves` exists). The classifying morphism of `X` factors
through `Curves^{prestable}` exactly when the singularities of `X` are at-worst-nodal,
`dim(X) = 1` and `k = H⁰(X, 𝒪_X)`. -/
@[stacks 0E6U "part (2)"]
theorem factors_curvesPrestable_over_field_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
      ((letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
        Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
        topologicalKrullDim X.left = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)) :=
  ((factors_curvesPrestable_iff B hZ U y hy).trans
    ⟨fun h => CurveFamily.isPrestableCurveFamily_of_hom e.inv h,
      fun h => CurveFamily.isPrestableCurveFamily_of_hom e.hom h⟩).trans
    (isPrestableCurveFamily_curveFamilyOfScheme_iff (B := B) (hZ := hZ) hk X hdim)

/-! ### Openness of `Curves^{prestable}` -/

/-- **Condition (o) of Section 0E0E for `Curves^{prestable}`, given semicontinuity.** Given
`hbetti`, that for every proper, flat, finitely presented `f : X ⟶ U` the function
`dim_k H⁰(X_k, 𝒪)` on the points of `U` is upper semicontinuous, `Curves^{prestable}` satisfies
condition (o). -/
theorem isOpenCurvesLocus_isPrestableCurveFamily_of_h0FibreRank
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p)) :
    IsOpenCurvesLocus B hZ (IsPrestableCurveFamily B hZ) :=
  isOpenCurvesLocus_isPrestableCurveFamily_of
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
      (Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ))

/-- **Condition (o) of Section 0E0E for `Curves^{prestable}`.** Every family of curves has an
open subspace of its base, compatible with base change, over which exactly the prestable base
changes live. -/
theorem isOpenCurvesLocus_isPrestableCurveFamily :
    IsOpenCurvesLocus B hZ (IsPrestableCurveFamily B hZ) :=
  isOpenCurvesLocus_isPrestableCurveFamily_of_h0FibreRank B hZ
    Space.exists_upperSemicontinuous_h0FibreRank

/-- `Curves^{prestable}`, the strictly full subcategory of prestable families of curves
(Stacks 0E6T), is an open substack of `Curves`: prestability is invariant under isomorphism, and
the inclusion `Curves^{prestable} ⟶ Curves` is representable by algebraic spaces and an open
immersion. -/
@[stacks 0E6U "the open substack Curves^{prestable} of Curves"]
theorem curvesPrestable_isOpenSubstack :
    ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          CurveFamily.isPrestableCurveFamily_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          CurveFamily.isPrestableCurveFamily_of_hom) :=
  isOpenImmersion_curvesSubstackInclusion (isOpenCurvesLocus_isPrestableCurveFamily B hZ)

/-- There is an open substack `Curves^{prestable} ⊂ Curves` — the strictly full subcategory of
prestable families of curves, whose inclusion is representable by algebraic spaces and an open
immersion — such that

1. the classifying morphism of a family of curves `X ⟶ S` factors through it exactly when
   `X ⟶ S` is a prestable family of curves, and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
   `Spec k ⟶ Curves` of `X` factors through it exactly when the singularities of `X` are
   at-worst-nodal, `dim(X) = 1` and `k = H⁰(X, 𝒪_X)`. -/
@[stacks 0E6U "the whole statement: the open substack Curves^{prestable} and parts (1) and (2)"]
theorem curvesPrestable_isOpenSubstack_and_factors_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          CurveFamily.isPrestableCurveFamily_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          CurveFamily.isPrestableCurveFamily_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        ((letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
          Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
          topologicalKrullDim X.left = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)))) :=
  ⟨curvesPrestable_isOpenSubstack B hZ, factors_curvesPrestable_iff B hZ,
    factors_curvesPrestable_over_field_iff B hZ⟩

end AlgebraicGeometry

end
