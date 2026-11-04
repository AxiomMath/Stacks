module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalIsomSpace
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallAutomorphisms

/-!
# The diagonal of the stack of curves, reduced to Noetherian affine bases (Stacks 0DSQ)

**Stacks 0DSQ**: the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite
presentation. This module proves it, read as in Properties of Stacks, Section 04XB, at
`AlgebraicGeometry.curvesAlgebraicStack B hZ h`, from the following hypotheses:

* `h`, the algebraicity of the stack of curves (Stacks 0D5A), at an arbitrary descent universe;
* `hlim`, the limit preservation of the stack of curves (Stacks 0D55);
* `hiso`, which identifies the base change of `Δ` at a pair of families of curves with
  `Isom_U(Y, X)` of Stacks 0DPP, and `hsep`, the separatedness of `Isom_U(Y, X)` over `U`
  (Stacks 0DPN and 0DPP);
* `hN`: `Isom_V(Y, X) ⟶ V` is quasi-compact for families of curves `Y` and `X` over a Noetherian
  affine scheme `V`.

## Main results

* `AlgebraicGeometry.isQuasiCompact_relativeDiagonal_curvesAlgebraicStack_of_noetherian`: the
  quasi-compactness clause from `h`, `hlim`, `hiso` and `hN`.

Stacks 0DSQ itself, from `h`, `hlim`, `hsep`, `hiso` and `hN`, is the theorem
`isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_noetherian`

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0DPN](https://stacks.math.columbia.edu/tag/0DPN)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

/-- Quasi-compactness of morphisms of spaces is invariant under isomorphism of arrows. -/
private theorem isQuasiCompact_respectsIso (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) :
    MorphismProperty.RespectsIso (@Space.IsQuasiCompact B integerBase hZ) :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun f g e hf =>
    Space.isQuasiCompact_of_arrowIso B integerBase hZ f.hom g.hom e.hom.left e.hom.right
      e.hom.w hf)

namespace curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

attribute [local instance] isFibered locallySmall_curveFamily

attribute [local implicit_reducible] schemeSpace ShrinkHoms.fromShrinkHoms ShrinkHoms.inverse
  curvesSmall curvesSmallBased

/-- **`Isom_𝒳(y₁, y₂)` is quasi-compact over `U`, from Noetherian affine bases.** Let `y₁` and
`y₂` be objects of the small model of the stack of curves over `U` whose isomorphism space
`Isom_𝒳(y₁, y₂)`, read over `Spec(ℤ)`, is an algebraic space (`halg`). Given the limit
preservation of the stack of curves (`hlim`, Stacks 0D55), the identification of
`Isom_𝒳(y₁, y₂) ⟶ U` with `Isom_U(Y, X) ⟶ U` (`hiso`, the statement of
`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`) and the
quasi-compactness of `Isom_V(Y', X') ⟶ V` over Noetherian affine bases `V` (`hN`), the
structure morphism of `Isom_𝒳(y₁, y₂)` is quasi-compact. -/
theorem isQuasiCompact_relocalizeToYoneda_isomSpace_of_noetherian
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hiso : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
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
          (CurveFamily.isomFunctorProjection F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb'))))
    {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U)
    (halg : IsAlgebraicSpace B integerBase hZ
      ((OverShriek.relocalizePresheafFunctor U.hom).obj
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂))) :
    Space.IsQuasiCompact B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)) := by
  obtain ⟨e⟩ := hiso U y₁ y₂
  have halg' := isAlgebraicSpace_of_iso B integerBase hZ (Arrow.leftFunc.mapIso e).symm halg
  have hqc := CurveFamily.isQuasiCompact_isomFunctorProjection_of_affine
    (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
    (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ) (y₂.2.trans y₁.2.symm) halg'
    (fun F' G' hb' haff =>
      CurveFamily.isQuasiCompactSpace_isomFunctor_of_isLimitPreserving hlim hN F' G' hb' haff)
  have := isQuasiCompact_respectsIso B hZ
  exact (Space.isQuasiCompact_comp_isIso_iff B integerBase hZ _
    (yoneda.map (eqToHom y₁.2.symm))).1 ((MorphismProperty.arrow_mk_iso_iff _ e).2 hqc)

end curvesSmall

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSQ, separatedness, from that of `Isom_𝒳(y₁, y₂)`.** Given that the stack of
curves is algebraic (`h`, Stacks 0D5A) and that `Isom_𝒳(y₁, y₂) ⟶ U` is separated for every pair
of objects of the small model of the stack of curves over a common `U` (`hsep`, the statement of
`AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`, from Stacks 0DPN and
0DPP), the diagonal of the stack of curves is separated in the sense of Stacks 04XB. -/
theorem isSeparated_relativeDiagonal_curvesAlgebraicStack_of_isSeparated_isomSpace
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hsep : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      letI : (curvesSmall B hZ).val.p.IsFibered :=
        (curvesSmall B hZ).isFiberedInGroupoids.isFibered
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂))) :
    Stack.IsSeparated B integerBase hZ
      (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) := by
  intro U y hy F hF hE
  have := Space.isSeparated_respectsIso B integerBase hZ
  exact (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B integerBase hZ
    (@Space.IsSeparated B integerBase hZ)
    (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
    (Stack.faithful_schemeStack_p.{u, w} B integerBase hZ) U y hy F hF hE).2 (hsep _ _ _)

/-- **Stacks 0DSQ, quasi-compactness, from Noetherian affine bases.** Given that the stack of
curves is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), the
identification of the base changes of its diagonal with `Isom_U(Y, X)` (`hiso`, the statement of
`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`), and the
quasi-compactness of `Isom_V(Y, X) ⟶ V` for families of curves over Noetherian affine bases `V`
(`hN`), the diagonal of the stack of curves is quasi-compact in the sense of Stacks 04XB. -/
theorem isQuasiCompact_relativeDiagonal_curvesAlgebraicStack_of_noetherian
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
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
    Stack.IsQuasiCompact B integerBase hZ
      (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) := by
  intro U y hy F hF hE
  have := isQuasiCompact_respectsIso B hZ
  let PA : MorphismProperty ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
    fun X _ _ => IsAlgebraicSpace B integerBase hZ X
  have : PA.RespectsIso := MorphismProperty.RespectsIso.of_respects_arrow_iso _
    (fun f g e hf => isAlgebraicSpace_of_iso B integerBase hZ (Arrow.leftFunc.mapIso e).symm hf)
  have halg := (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B integerBase hZ PA
    (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
    (Stack.faithful_schemeStack_p.{u, w} B integerBase hZ) U y hy F hF hE).1
    ((spacesOverSmallerBaseFunctor B U.left.1 integerBase U.left.2 hZ U.hom).obj ⟨F, hF⟩).property
  exact (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B integerBase hZ
    (@Space.IsQuasiCompact B integerBase hZ)
    (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
    (Stack.faithful_schemeStack_p.{u, w} B integerBase hZ) U y hy F hF hE).2
    (curvesSmall.isQuasiCompact_relocalizeToYoneda_isomSpace_of_noetherian hlim hiso hN _ _ halg)

/-- **Stacks 0DSQ, from Noetherian affine bases.** Given that the stack of curves is algebraic
(`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), that `Isom_𝒳(y₁, y₂) ⟶ U` is
separated (`hsep`, Stacks 0DPN and 0DPP) and is `Isom_U(Y, X) ⟶ U` (`hiso`) for every pair of
objects of the small model of the stack of curves over a common `U`, and that `Isom_V(Y, X) ⟶ V`
is quasi-compact for families of curves over Noetherian affine bases `V` (`hN`, the last
paragraph of the source's proof: Stacks 0DQ0, 0DPR and Riemann–Roch), the diagonal
`Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite presentation, both in the
sense of Stacks 04XB. -/
theorem
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_noetherian
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
    Stack.IsSeparated B integerBase hZ
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :=
  ⟨isSeparated_relativeDiagonal_curvesAlgebraicStack_of_isSeparated_isomSpace B hZ h hsep,
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B integerBase hZ _,
    fun U y hy F hF hE =>
      ⟨isLocallyOfFinitePresentation_diagonal_curvesAlgebraicStack B hZ h hlim U y hy F hF hE,
        isQuasiCompact_relativeDiagonal_curvesAlgebraicStack_of_noetherian B hZ h hlim hiso hN
          U y hy F hF hE,
        Space.isQuasiSeparated_of_isSeparated B integerBase hZ
          (isSeparated_relativeDiagonal_curvesAlgebraicStack_of_isSeparated_isomSpace B hZ h hsep
            U y hy F hF hE)⟩⟩

end AlgebraicGeometry

end
