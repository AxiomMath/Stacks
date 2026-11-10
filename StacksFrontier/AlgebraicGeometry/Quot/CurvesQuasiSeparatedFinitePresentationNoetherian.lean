module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalNoetherianReduction
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalPolarizedReduction
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation

/-!
# Curves → Spec(ℤ) is quasi-separated and locally of finite presentation, from Noetherian bases

This file proves that the morphism `Curves → Spec(ℤ)` is quasi-separated and locally of finite
presentation (Stacks 0DSS), under explicit hypotheses on the stack of curves.

The argument has two steps.
* Quasi-separatedness asks that the diagonal be quasi-compact and quasi-separated (Stacks 04YW).
  That is immediate from Stacks 0DSQ, the diagonal being of finite presentation.
* Local finite presentation follows from limit preservation, Stacks 0D55, by Stacks 0CMY.

Here the finite presentation of the diagonal is obtained from its reduction to Noetherian affine
bases. The hypotheses are:
* `h`, the algebraicity of the stack of curves, Stacks 0D5A;
* `hlim`, Stacks 0D55;
* `hsep` and `hiso`, the separatedness of `Isom_𝒳(y₁, y₂)` and its identification with
  `Isom_U(Y, X)`;
* `hN`, the quasi-compactness of `Isom_V(Y, X) ⟶ V` over Noetherian affine bases `V`.

## Main results

* Stacks 0DSS from Noetherian affine bases, under the hypotheses above.
* Stacks 0DSS with the Noetherian hypothesis `hN` replaced by two others: every family of curves is
  smooth locally polarized (`hpol`, the shape of Stacks 0DQ0), and `Isom` is quasi-compact over
  Noetherian affine bases where both families are projective (`hproj`, Stacks 0DPR with
  Riemann–Roch).

## References

* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSS from Noetherian affine bases.** Suppose the stack of curves is algebraic (`h`,
Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55). Suppose also that, for every pair of
objects of its small model over a common `U`, `Isom_𝒳(y₁, y₂) ⟶ U` is separated (`hsep`) and is
`Isom_U(Y, X) ⟶ U` (`hiso`). Finally suppose `Isom_V(Y, X) ⟶ V` is quasi-compact over Noetherian
affine bases `V` (`hN`). Then the morphism `Curves → Spec(ℤ)` is quasi-separated and locally of
finite presentation. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curves_of_noetherian
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hsep : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      letI : (curvesSmall B hZ).val.p.IsFibered :=
        (curvesSmall B hZ).isFiberedInGroupoids.isFibered
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)))
    (hiso : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      letI : (curvesSmall B hZ).val.p.IsFibered :=
        (curvesSmall B hZ).isFiberedInGroupoids.isFibered
      Nonempty (Arrow.mk (OverShriek.relocalizeToYoneda U.hom
            (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
          yoneda.map (eqToHom y₁.2.symm)) ≅
        Arrow.mk (CurveFamily.isomFunctorProjection
          (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
          (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ)
          ((ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ).toBase.hom ≫
            yoneda.map (eqToHom (y₂.2.trans y₁.2.symm))))))
    (hN : ∀ (F' G' : CurveFamily B hZ) (hb' : G'.base = F'.base),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) →
        Space.IsQuasiCompact B integerBase hZ
          (CurveFamily.isomFunctorProjection F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb')))) :
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h
    hlim <| And.right <|
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_noetherian
    B hZ h hlim hsep hiso hN

/-- **Stacks 0DSS from polarizations.** Suppose the stack of curves is algebraic (`h`, Stacks
0D5A) and limit preserving (`hlim`, Stacks 0D55). Suppose also that, for every pair of objects
of its small model over a common `U`, `Isom_𝒳(y₁, y₂) ⟶ U` is separated (`hsep`) and is
`Isom_U(Y, X) ⟶ U` (`hiso`). Moreover suppose that every family of curves is smooth locally
polarized (`hpol`, the shape of Stacks 0DQ0). Finally suppose `Isom_U(Y, X) ⟶ U` is quasi-compact
over Noetherian affine `U` on which both families are projective (`hproj`, Stacks 0DPR with
Riemann–Roch). Then the morphism `Curves → Spec(ℤ)` is quasi-separated and locally of finite
presentation. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curves_of_polarized
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hsep : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      letI : (curvesSmall B hZ).val.p.IsFibered :=
        (curvesSmall B hZ).isFiberedInGroupoids.isFibered
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)))
    (hiso : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      letI : (curvesSmall B hZ).val.p.IsFibered :=
        (curvesSmall B hZ).isFiberedInGroupoids.isFibered
      Nonempty (Arrow.mk (OverShriek.relocalizeToYoneda U.hom
            (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
          yoneda.map (eqToHom y₁.2.symm)) ≅
        Arrow.mk (CurveFamily.isomFunctorProjection
          (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
          (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ)
          ((ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ).toBase.hom ≫
            yoneda.map (eqToHom (y₂.2.trans y₁.2.symm))))))
    (hpol : ∀ X : CurveFamily B hZ, X.IsSmoothLocallyPolarized)
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
  isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h
    hlim <| And.right <|
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_polarized
    B hZ h hlim hsep hiso hpol hproj

end AlgebraicGeometry

end
