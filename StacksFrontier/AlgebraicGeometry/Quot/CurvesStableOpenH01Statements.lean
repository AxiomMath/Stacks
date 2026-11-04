module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpen

/-!
# `Curves^{stable}` over the statements of the cohomological inputs of Stacks 0E6I

`AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff_of_inputs` proves Stacks 0E76 from
the inputs of Stacks 0E6U and the relative openness of stable fibres on prestable families. This
file restates it over the two inputs in the shape in which Stacks 0E0R (at `i = 0`, for
`𝓕 = 𝒪_X`) and Stacks 0E6B part (a) are stated for algebraic spaces — the `hbetti` and `hstruct`
of `StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs`. The conclusion is unchanged; only the
inputs are.

## Main results

* `AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff_of_h01Statements`: Stacks 0E76,
  the open substack, part (1) and part (2).

No declaration of this file carries a `stacks` attribute: the inputs are still hypotheses.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
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

/-- **Stacks 0E76, over the statements of Stacks 0E0R (at `i = 0`) and 0E6B (a).** The whole
statement of `AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff_of_inputs`, with
condition (o) for `Curves^{h0,1}` and the reading of `f_*𝒪_X = 𝒪_S` over a field supplied from
`hbetti` (Stacks 0E0R at `i = 0`, for `𝓕 = 𝒪_X`) and `hstruct` (Stacks 0E6B, part (a)): there is
an open substack `Curves^{stable}` of `Curves` such that

1. the classifying morphism of a family of curves factors through it exactly when the family is
   stable, and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, factoring through it is equivalent
   both to `X` having at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, genus at
   least two and no rational tails or bridges, and to `X` having at-worst-nodal singularities,
   `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and `ω_X` invertible and ample.

The remaining inputs are the at-worst-nodal criterion over a field (`hsch`) and the relative
openness of stable fibres on prestable families (`hrel`). -/
theorem curvesStable_isOpenSubstack_and_factors_iff_of_h01Statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
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
              (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct))
                hrel).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          (isOpenCurvesLocus_isStableCurveFamily_of_prestable
            (isOpenCurvesLocus_isPrestableCurveFamily_of
              (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct))
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
                ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)))))) := by
  have hpush : ∀ X : CurveFamily B hZ,
      CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X := fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct hX
  have hPre := isOpenCurvesLocus_isPrestableCurveFamily_of
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct)
  refine ⟨(curvesStable_isOpenSubstack_and_factors_iff_of_prestable hPre hrel).1,
    (curvesStable_isOpenSubstack_and_factors_iff_of_prestable hPre hrel).2, ?_⟩
  intro k _ T W g hW hproper hdim U y hy e
  have hstable := isStableCurveFamily_curveFamilyOverFieldOfProper_iff_of B hZ hpush hsch
    isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hd hn C hC)
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hd hn C hC)
    (fun f _ g' f' h => ⟨Stacks.Duality.dualizingSheafOverFieldBaseChangeIso f g' f' h⟩)
  have hample := hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField_of
    isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hd hn C hC)
    (fun _ _ _ _ _ hd _ hn C hC _ _ =>
      invertibleCurveDegree_pullback_dualizingSheafOverField_eq_zero_of_isRationalBridge hd hn C hC)
    (fun κ _ _ f _ _ _ hd _ _ => invertibleCurveDegree_dualizingSheafOverField κ f hd)
  rw [factors_curvesSubstack_iff_of_iso
    (isOpenCurvesLocus_isStableCurveFamily_of_prestable hPre hrel) U y hy _ e,
    hstable k g hW hproper hdim]
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) := by
    have := hproper
    infer_instance
  refine ⟨⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩, ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, ?_⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, ?_⟩⟩⟩
  · exact (hample k _ h2 h3 h1).1 h4
  · exact (hample k _ h2 h3 h1).2 h4

end AlgebraicGeometry

end
