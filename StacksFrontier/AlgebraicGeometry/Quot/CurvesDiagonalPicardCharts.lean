module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsSmoothLocallyPolarized
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalNoetherianPolarizedOf

/-!
# The diagonal of the stack of curves over Picard charts

Assume that the stack of curves is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`,
Stacks 0D55), that the H-projective case of the quasi-compactness of `Isom_U(Y, X) ⟶ U` holds
(`hproj`, Stacks 0DPR with Riemann–Roch), and that the Picard objects of every family of curves
admit smooth charts staying in the relative ample locus (`hchart`, Stacks 0D04 with Stacks 09DS,
and Stacks 0DPJ). Then the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of
finite presentation (Stacks 0DSQ), and the morphism `Curves → Spec(ℤ)` is quasi-separated and
locally of finite presentation (Stacks 0DSS).

## Main results

* `isSeparated_isRelativelyFinitePresentation_diagonal_curves_of_picardCharts`: the
  diagonal of the stack of curves is separated and of finite presentation.
* `isQuasiSeparated_isLocallyOfFinitePresentation_curves_of_picardCharts`: the morphism
  `Curves → Spec(ℤ)` is quasi-separated and locally of finite presentation.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSQ over the Picard-chart inputs.** Given that the stack of curves is algebraic
(`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), and that `Isom_V(Y, X) ⟶ V`, base
changed to an étale chart `U` from a Noetherian affine scheme along which both families are
H-projective schemes, is quasi-compact (`hproj`, Stacks 0DPR with Riemann–Roch), and that the
Picard objects of every family of curves admit smooth charts staying in the relative ample locus
(`hchart`, Stacks 0D04 with Stacks 09DS, and Stacks 0DPJ), the diagonal
`Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite presentation, both in the
sense of Stacks 04XB. -/
theorem isSeparated_isRelativelyFinitePresentation_diagonal_curves_of_picardCharts
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
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
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :=
  isSeparated_isRelativelyFinitePresentation_diagonal_curves_of_isSmoothLocallyPolarized
    B hZ h hlim (CurveFamily.isSmoothLocallyPolarized hchart) hproj

/-- **Stacks 0DSS over the Picard-chart inputs.** Given that the stack of curves is algebraic
(`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), and the H-projective case of the
quasi-compactness of `Isom_U(Y, X) ⟶ U` (`hproj`, Stacks 0DPR with Riemann–Roch), and that the
Picard objects of every family of curves admit smooth charts staying in the relative ample locus
(`hchart`, Stacks 0D04 with Stacks 09DS, and Stacks 0DPJ), the morphism `Curves → Spec(ℤ)` is
quasi-separated and locally of finite presentation. -/
theorem isQuasiSeparated_isLocallyOfFinitePresentation_curves_of_picardCharts
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
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
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isQuasiSeparated_isLocallyOfFinitePresentation_curves_of_isSmoothLocallyPolarized
    B hZ h hlim (CurveFamily.isSmoothLocallyPolarized hchart) hproj

end AlgebraicGeometry

end
