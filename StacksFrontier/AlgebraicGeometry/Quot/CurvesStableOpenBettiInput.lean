module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01BettiInput
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenH01Statements

/-!
# `Curves^{stable}` over the Betti input alone

The open substack `Curves^{stable}` of `Curves`, and the characterizations of the families and of
the curves over a field that factor through it, under three hypotheses: `hbetti`, an upper
semicontinuous function computing the rank of `H⁰(X_p, 𝒪_{X_p})` on the fibres of a proper, flat,
finitely presented morphism; `hsch`, the at-worst-nodal criterion for a scheme locally of finite
type over a field; and `hrel`, the relative openness of stable fibres on prestable families. The
structure-sheaf input of `curvesStable_isOpenSubstack_and_factors_iff_of_h01Statements` is
supplied by `Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`.

## Main results

* `AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff_of_betti`: the open substack
  `Curves^{stable}`, with parts (1) and (2) of Tag 0E76, under `hbetti`, `hsch` and `hrel`.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

open Stacks.AlgebraicGeometry.ComponentDegrees

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The open substack of stable curves, over the Betti input.** Given `hbetti`, an upper
semicontinuous function computing the rank of `H⁰(X_p, 𝒪_{X_p})` on the fibres of every proper,
flat, finitely presented morphism to a scheme, there is an open substack `Curves^{stable}` of
`Curves` such that

1. the classifying morphism of a family of curves factors through it exactly when the family is
   stable, and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, factoring through it is equivalent
   both to `X` having at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, genus at
   least two and no rational tails or bridges, and to `X` having at-worst-nodal singularities,
   `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and `ω_X` invertible and ample.

The remaining inputs are the at-worst-nodal criterion over a field (`hsch`) and the relative
openness of stable fibres on prestable families (`hrel`). -/
theorem curvesStable_isOpenSubstack_and_factors_iff_of_betti
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsStableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          (isOpenCurvesLocus_isStableCurveFamily_of_prestable
            (isOpenCurvesLocus_isPrestableCurveFamily_of
              (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_betti hbetti))
                hrel).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          (isOpenCurvesLocus_isStableCurveFamily_of_prestable
            (isOpenCurvesLocus_isPrestableCurveFamily_of
              (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_betti hbetti))
                hrel).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        IsStableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ g k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
      (((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          HasGenusTwoNoRationalTailNoRationalBridge k
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW))) ∧
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          ∃ _ : SheafOfModules.IsInvertible
              ((BigFppfOver.toScheme B integerBase hZ).obj T).toRingedSpace.presheaf
              (structureSheafRing
                ((BigFppfOver.toScheme B integerBase hZ).obj T).toRingedSpace).property
              (Stacks.Duality.dualizingSheafOverField
                ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)),
            Scheme.Modules.IsAmple ((BigFppfOver.toScheme B integerBase hZ).obj T)
              (Stacks.Duality.dualizingSheafOverField
                ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)))))) :=
  curvesStable_isOpenSubstack_and_factors_iff_of_h01Statements hbetti
    (Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ)
    hsch hrel

end AlgebraicGeometry

end
