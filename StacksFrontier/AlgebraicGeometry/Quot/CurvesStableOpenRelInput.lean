module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpenBettiInput
public import StacksFrontier.AlgebraicGeometry.Quot.H0FibreRankSemicontinuity

/-!
# `Curves^{stable}` from the nodal criterion and relative openness

Stacks 0E76 says that `Curves^{stable}` is an open substack of `Curves`, that a family of curves
factors through it exactly when it is stable, and that a proper scheme of dimension at most one
over a field factors through it exactly when it is a stable curve, in either of two equivalent
formulations. This file proves it from two inputs: `hsch`, the at-worst-nodal criterion for a
scheme over a field (part (2) of Stacks 0DSY), and `hrel`, the relative openness of stable fibres
on prestable families (Stacks 0E74).

## Main results

* `AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff_of_rel`: given `hsch` and `hrel`,
  `Curves^{stable}` is an open substack of `Curves` with the two characterizations of
  Stacks 0E76.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

open Stacks.AlgebraicGeometry.ComponentDegrees

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Assume the at-worst-nodal criterion for schemes over a field (`hsch`, part (2) of
Stacks 0DSY) and the relative openness of stable fibres on prestable families (`hrel`,
Stacks 0E74). Then there is an open substack `Curves^{stable}` of `Curves` — the strictly full
subcategory of stable families of curves (Stacks 0E75), whose inclusion is representable by
algebraic spaces and an open immersion — such that

1. the classifying morphism of a family of curves factors through it exactly when the family is
   stable, and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, factoring through it is equivalent
   both to `X` having at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, genus at
   least two and no rational tails or bridges, and to `X` having at-worst-nodal singularities,
   `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and `ω_X` invertible and ample. -/
theorem curvesStable_isOpenSubstack_and_factors_iff_of_rel
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
          CurveFamily.isStableCurveFamily_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          CurveFamily.isStableCurveFamily_of_hom)) ∧
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
  curvesStable_isOpenSubstack_and_factors_iff_of_betti
    Space.exists_upperSemicontinuous_h0FibreRank hsch hrel

end AlgebraicGeometry

end
