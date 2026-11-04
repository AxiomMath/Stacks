module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentationNoetherian
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallIsom

/-!
# Stacks 0DSQ and 0DSS with the isomorphism spaces of `Curves` identified

The reductions of `StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalNoetherianReduction`,
`StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalPolarizedReduction` and
`StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentationNoetherian` take as
arguments `hsep` (the isomorphism spaces `Isom_𝒳(y₁, y₂) ⟶ U` of the small model of the stack of
curves are separated) and `hiso` (they are `Isom_U(Y, X) ⟶ U`). These are
`AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace` and
`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`. This file applies them.

## Main results

* `isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_…`
  with suffix `isNoetherian`: Stacks 0DSQ from `h` (0D5A), `hlim` (0D55) and the
  quasi-compactness of `Isom_V(Y, X) ⟶ V` over Noetherian affine `V` (`hN`).
* The same name with suffix `isSmoothLocallyPolarized`: Stacks 0DSQ from `h`, `hlim`, the smooth
  local polarizations (`hpol`, 0DQ0) and the H-projective case (`hproj`, 0DPR).
* `isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack_of_…`
  with suffixes `isNoetherian` and `isSmoothLocallyPolarized`: Stacks 0DSS from the same inputs.

## Implementation notes

The hypotheses are taken as arguments: `h` is Stacks 0D5A and `hlim` Stacks 0D55; `hpol` is part
of Stacks 0DQ0 and `hproj` follows from Stacks 0DPR.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSQ, from Noetherian affine bases.** Given that the stack of curves is algebraic
(`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), and that `Isom_V(Y, X) ⟶ V` is
quasi-compact for families of curves over Noetherian affine bases `V` (`hN`, the last paragraph
of the source's proof), the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of
finite presentation, both in the sense of Stacks 04XB. -/
theorem isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_isNoetherian
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hN : ∀ (F' G' : CurveFamily B hZ) (hb' : G'.base = F'.base),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) →
        Space.IsQuasiCompact B integerBase hZ
          (CurveFamily.isomFunctorProjection F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb')))) :
    Stack.IsSeparated B integerBase hZ
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :=
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_noetherian
    B hZ h hlim (fun _ y₁ y₂ => curvesSmall.isSeparated_relocalizeToYoneda_isomSpace y₁ y₂)
    (fun _ y₁ y₂ => curvesSmall.nonempty_arrowIso_isomFunctorProjection y₁ y₂) hN

/-- **Stacks 0DSQ, from the smooth local polarizations and the H-projective case.** Given that
the stack of curves is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55),
that every family of curves is smooth locally polarized (`hpol`, Stacks 0DQ0), and that
`Isom_V(Y, X) ⟶ V`, base changed to an étale chart `U` from a Noetherian affine scheme along which
both families are H-projective schemes, is quasi-compact (`hproj`, Stacks 0DPR with
Riemann–Roch), the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite
presentation, both in the sense of Stacks 04XB. -/
theorem isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_isSmoothLocallyPolarized
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
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
    Stack.IsSeparated B integerBase hZ
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :=
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_polarized
    B hZ h hlim (fun _ y₁ y₂ => curvesSmall.isSeparated_relocalizeToYoneda_isomSpace y₁ y₂)
    (fun _ y₁ y₂ => curvesSmall.nonempty_arrowIso_isomFunctorProjection y₁ y₂) hpol hproj

/-- **Stacks 0DSS, from Noetherian affine bases.** Given that the stack of curves is algebraic
(`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), and that `Isom_V(Y, X) ⟶ V` is
quasi-compact over Noetherian affine bases `V` (`hN`), the morphism `Curves → Spec(ℤ)` is
quasi-separated and locally of finite presentation. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack_of_isNoetherian
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
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
    hlim (isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_isNoetherian
      B hZ h hlim hN).2

/-- **Stacks 0DSS, from the smooth local polarizations and the H-projective case.** Given that
the stack of curves is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55),
that every family of curves is smooth locally polarized (`hpol`, Stacks 0DQ0), and the
H-projective case of the quasi-compactness of `Isom_U(Y, X) ⟶ U` (`hproj`, Stacks 0DPR with
Riemann–Roch), the morphism `Curves → Spec(ℤ)` is quasi-separated and locally of finite
presentation. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack_of_isSmoothLocallyPolarized
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
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
    hlim (isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_isSmoothLocallyPolarized
      B hZ h hlim hpol hproj).2

end AlgebraicGeometry

end
