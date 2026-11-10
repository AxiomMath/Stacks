module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalPicardCharts

/-!
# Stacks 0DSQ over a presentation of the stack of curves

The form of Stacks 0DSQ proved from Picard charts, the theorem whose name ends in
`_diagonal_curves_of_picardCharts`, takes four inputs, the first of which is `h`, the
algebraicity of the stack of curves (Stacks 0D5A). This file replaces that one by *presentation
data*: an algebraic stack `𝒳` over the big fppf site of the integers together with an equivalence
`E` over the site between the category of families of curves and `𝒳`.

That is the shape in which `AlgebraicGeometry.nodalCurvesOpenSubstack` and
`AlgebraicGeometry.classifying_factors_nodalCurvesOpenSubstack_iff` state Stacks 0DSY, and in
which `AlgebraicGeometry.curvesOpenSubstackOfIsOpenCurvesLocus` states the open substacks of
Section 0E0E: the algebraicity of the stack of curves is not assumed as a proposition, it is
carried by whichever algebraic stack the user has in hand. Algebraicity of
`AlgebraicGeometry.curvesFiberedCategory` itself is then a consequence, Stacks 03YQ applied to
`E` (`AlgebraicGeometry.isAlgebraicStack_curvesFiberedCategory_of_presentation`), so the
conclusion can still be stated about the canonical object
`AlgebraicGeometry.curvesAlgebraicStack` and is letter for letter the conclusion of Stacks 0DSQ:
the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite presentation, in
the sense of Stacks 04XB.

## Main results

* `AlgebraicGeometry.isAlgebraicStack_curvesFiberedCategory_of_presentation`: the stack of
  curves is algebraic as soon as it has an algebraic presentation (Stacks 03YQ).
* The theorem whose name ends in `_diagonal_curves_of_presentation`: over a presentation of
  the stack of curves, its diagonal is separated and of finite presentation (Stacks 0DSQ).

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The stack of curves is algebraic as soon as it has an algebraic presentation** (Stacks
03YQ). If `𝒳` is an algebraic stack over the big fppf site of the integers and `E` is an
equivalence over that site between the category of families of curves and `𝒳`, then
`AlgebraicGeometry.curvesFiberedCategory` is itself an algebraic stack. -/
theorem isAlgebraicStack_curvesFiberedCategory_of_presentation
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val :=
  Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ
    (𝒴 := (curvesFiberedCategory B hZ).val)
    (StacksRepresentableCFG.equivalenceOverOfIsEquivalence
      CurveDeformation.curvesProjectionOver_isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids E.functor hE E.isEquivalence_functor).symm
    𝒳.property

/-- **Stacks 0DSQ over a presentation of the stack of curves.** Let `𝒳` be an algebraic stack
over the big fppf site of the integers and `E` an equivalence over that site between the category
of families of curves and `𝒳`. Suppose moreover that the stack of curves is limit preserving
(`hlim`, Stacks 0D55), that `Picardstack_{X/T}` has smooth charts through the ample locus
(`hchart`, Stacks 0D04 with Stacks 09DS, and Stacks 0DPJ), and that `Isom_V(Y, X) ⟶ V`, base
changed to an étale chart `U` from a Noetherian affine scheme along which both families are
H-projective schemes, is quasi-compact (`hproj`, Stacks 0DPR with Riemann–Roch). Then the
diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite presentation, both
in the sense of Stacks 04XB. -/
theorem isSeparated_isRelativelyFinitePresentation_diagonal_curves_of_presentation
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hchart : ∀ (X : CurveFamily B hZ) (K : Type u) (_ : Field K)
      (hK : B.Contains (Spec (.of K)))
      (x : (schemeOverIntegers B).obj (B.obj hK) ⟶ X.base)
      (A₀ : Space.PicardObject X.picardSituation), A₀.T = X.picardTestScheme x →
        A₀.IsInAmpleLocus →
        ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
          Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
          ∃ (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π)
            (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (.of K')))
            (y : (schemeOverIntegers B).obj (B.obj hK') ⟶ T')
            (e : (schemeOverIntegers B).obj (B.obj hK') ⟶ (schemeOverIntegers B).obj (B.obj hK)),
            y ≫ π = e ≫ x ∧
            (Space.PicardSituation.pullbackObject A
              (X.picardTestSchemeMap y π ≫ eqToHom hA.symm)).IsInAmpleLocus)
    (hproj : ∀ (F G : CurveFamily B hZ) (hb : G.base = F.base) (U : BigFppfOver B integerBase hZ)
      (φ : U ⟶ F.base),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ F.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap φ) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) →
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ G.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap (φ ≫ eqToHom hb.symm)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) →
      Space.IsQuasiCompact B integerBase hZ
        (pullback.snd (CurveFamily.isomFunctorProjection F G
          (G.toBase.hom ≫ yoneda.map (eqToHom hb))) (yoneda.map φ))) :
    Stack.IsSeparated B integerBase hZ
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ
          (curvesAlgebraicStack B hZ
            (isAlgebraicStack_curvesFiberedCategory_of_presentation B hZ 𝒳 E hE)).val
          (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
            (isAlgebraicStack_curvesFiberedCategory_of_presentation B hZ 𝒳 E hE))).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ
            (isAlgebraicStack_curvesFiberedCategory_of_presentation B hZ 𝒳 E hE)))) :=
  isSeparated_isRelativelyFinitePresentation_diagonal_curves_of_picardCharts
    B hZ (isAlgebraicStack_curvesFiberedCategory_of_presentation B hZ 𝒳 E hE) hlim hchart hproj

end AlgebraicGeometry

end
