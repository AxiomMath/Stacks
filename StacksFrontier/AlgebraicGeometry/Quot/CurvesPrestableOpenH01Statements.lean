module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen

/-!
# `Curves^{prestable}` over the statements of the cohomological inputs of Stacks 0E6I

`AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of_inputs` proves Stacks 0E6U
from condition (o) for `Curves^{h0,1}`, part (2) of Stacks 0E6I and the at-worst-nodal criterion
over a field. This file supplies the first two from the inputs in the shape in which Stacks 0E0R
(at `i = 0`, for `𝓕 = 𝒪_X`) and Stacks 0E6B part (a) are stated for algebraic spaces — the
`hbetti` and `hstruct` of `StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs`. The conclusion is
unchanged; only the inputs are.

## Main results

* `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of_h01Statements`: Stacks
  0E6U, the open substack, part (1) and part (2).

## References

* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Stacks 0E6U, over the statements of Stacks 0E0R (at `i = 0`), 0E6B (a) and 0DSY (2).** The
whole statement of `AlgebraicGeometry.curvesPrestable_isOpenSubstack_and_factors_iff_of_inputs`,
with both parts of Stacks 0E6I derived from `hbetti` (Stacks 0E0R at `i = 0`, for `𝓕 = 𝒪_X`) and
`hstruct` (Stacks 0E6B, part (a)); the remaining input is the criterion for at-worst-nodal
morphisms over a field (`hsch`). -/
theorem curvesPrestable_isOpenSubstack_and_factors_iff_of_h01Statements
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
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞))) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of
            (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
              hstruct)).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsPrestableCurveFamily B hZ)
          (isOpenCurvesLocus_isPrestableCurveFamily_of
            (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
              hstruct)).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
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
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsPrestableCurveFamily B hZ) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop))) :=
  have hpush : ∀ X : CurveFamily B hZ,
      CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X := fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct hX
  curvesPrestable_isOpenSubstack_and_factors_iff_of_inputs
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct)
    (fun {_ _} g k _ hW hflat hproper hlfp hqc hsep hqsep hdim =>
      CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hflat hproper
        hlfp hqc hsep hqsep hdim)
    hsch

end AlgebraicGeometry

end
