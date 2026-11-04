module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallIsom
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesQuasiSeparatedFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalIsomSpace

/-!
# The diagonal of the stack of curves (Stacks 0DSQ)

**Stacks 0DSQ**: the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite
presentation. It is stated at `AlgebraicGeometry.curvesAlgebraicStack B hZ h`, the small model of
the stack of curves as an object of `AlgebraicGeometry.Stack.AlgebraicStacks`, which takes `h`,
the algebraicity of the stack of curves (Stacks 0D5A), as an argument. Both properties are read as
in Properties of Stacks, Section 04XB: every algebraic space representing a base change of `Δ`
along a scheme-valued point has the property.

## Separatedness

The source's argument: the base change of `Δ` along a point `(Y, X, α)` over a scheme `U` is the
algebraic space `Isom_U(Y, X)`, which is separated over `U` by Moduli Stacks, Lemmas 0DPN and
0DPP. The base change is `Isom_𝒳(y₁, y₂)` by
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace`, which is
`Isom_U(Y, X)` by `AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`, and
`AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace` concludes. This part
needs no input beyond the algebraicity `h` which the statement is formed at.

## Quasi-compactness and finite presentation

The source's argument for quasi-compactness of `Δ` has two steps. By Properties of Stacks, Lemma
04XD it suffices to check it after base change along a smooth surjective
`U = ∐ Uᵢ ⟶ Curves × Curves` from affine schemes through which `PolarizedCurves × PolarizedCurves`
is covered, using Stacks 0DQ0; each `Uᵢ` is then Noetherian. For a Noetherian affine `U` and two
polarized families `(Y, 𝒩)` and `(X, ℒ)` over it, `Isom_U(Y, X)` lies in `Mor^{P', ℳ}_U(Y, X)` by
Riemann–Roch (Stacks 0AYX, 0B9T), which is of finite presentation over `U` by Stacks 0DPR.

Neither input can be stated in this development yet: Stacks 0DQ0 is a statement about the
1-morphism `PolarizedCurves ⟶ Curves` of algebraic stacks, which needs `PolarizedCurves` as an
algebraic stack (Stacks 0D4X through 0DPZ, and Stacks 0DPJ, 0D3D), and the numerical loci
`Mor^{P, ℳ}` of Stacks 0DPQ are built on Euler characteristics given as data
(`AlgebraicGeometry.Space.HilbertOverEulerData`), not on cohomology, so Stacks 0DPR cannot be
stated for the invariants of `ℳ`. The quasi-compactness clause is therefore proved here from the
quasi-compactness of `Isom_U(Y, X) ⟶ U` for all families of curves `Y` and `X` over a common
base (the argument `hqc`), which is what the two steps of the source establish; every algebraic
space representing a base change of `Δ` is such an `Isom_U(Y, X)`. The local finite presentation
clause is `AlgebraicGeometry.isLocallyOfFinitePresentation_diagonal_curvesAlgebraicStack`, from
Stacks 0D55, and quasi-separatedness follows from separatedness.

None of these declarations is registered: all take `h` (Stacks 0D5A), the finite presentation
clause takes `hlim` (Stacks 0D55), both not yet proved here, and the quasi-compactness
clause takes `hqc`.

## Main results

* `AlgebraicGeometry.isSeparated_relativeDiagonal_curvesAlgebraicStack`: the diagonal of the stack
  of curves is separated.
* `AlgebraicGeometry.isQuasiSeparated_relativeDiagonal_curvesAlgebraicStack`: hence
  quasi-separated.
* `AlgebraicGeometry.isQuasiCompact_relativeDiagonal_curvesAlgebraicStack_of`: it is
  quasi-compact as soon as every `Isom_U(Y, X) ⟶ U` is.
* `isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack`: the
  statement of Stacks 0DSQ, from `h`, `hlim` and `hqc`.
* `isQuasiSeparated_isLocallyOfFinitePresentation_curvesAlgebraicStack_of_isomQuasiCompact`: the
  statement of Stacks 0DSS, its argument `hdiag` discharged by Stacks 0DSQ.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0DPN](https://stacks.math.columbia.edu/tag/0DPN)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSQ, separatedness.** Given that the stack of curves is algebraic (`h`, Stacks
0D5A), its diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated in the sense of Stacks
04XB: every algebraic space representing a base change of `Δ` along a scheme-valued point
`(Y, X, α)` over `U` is `Isom_U(Y, X)`, which is separated over `U` (Stacks 0DPN, 0DPP). -/
theorem isSeparated_relativeDiagonal_curvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    Stack.IsSeparated B integerBase hZ
      (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) := by
  intro U y hy F hF hE
  have := Space.isSeparated_respectsIso B integerBase hZ
  exact (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B integerBase hZ
    (@Space.IsSeparated B integerBase hZ)
    (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
    (Stack.faithful_schemeStack_p.{u, w} B integerBase hZ) U y hy F hF hE).2
    (curvesSmall.isSeparated_relocalizeToYoneda_isomSpace _ _)

/-- **The diagonal of the stack of curves is quasi-separated**, being separated (Stacks 03KK).
Given that the stack of curves is algebraic (`h`, Stacks 0D5A). -/
theorem isQuasiSeparated_relativeDiagonal_curvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    Stack.IsQuasiSeparated B integerBase hZ
      (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) :=
  fun U y hy F hF hE => Space.isQuasiSeparated_of_isSeparated B integerBase hZ
    (isSeparated_relativeDiagonal_curvesAlgebraicStack B hZ h U y hy F hF hE)

/-- **Stacks 0DSQ, quasi-compactness, from that of `Isom_U(Y, X)`.** Given that the stack of
curves is algebraic (`h`, Stacks 0D5A), its diagonal is quasi-compact in the sense of Stacks 04XB
as soon as `Isom_U(Y, X) ⟶ U` is quasi-compact for all families of curves `Y` and `X` over a
common base `U` (`hqc`): every algebraic space representing a base change of `Δ` is such an
`Isom_U(Y, X)`. The source proves `hqc` in the last two paragraphs of the proof of Stacks 0DSQ,
from Stacks 0DQ0 and 0DPR. -/
theorem isQuasiCompact_relativeDiagonal_curvesAlgebraicStack_of
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hqc : ∀ (F G : CurveFamily B hZ) (hb : G.base = F.base),
      Space.IsQuasiCompact B integerBase hZ
        (CurveFamily.isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb)))) :
    Stack.IsQuasiCompact B integerBase hZ
      (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) := by
  intro U y hy F hF hE
  have : MorphismProperty.RespectsIso (@Space.IsQuasiCompact B integerBase hZ) :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun f g e hf =>
      Space.isQuasiCompact_of_arrowIso B integerBase hZ f.hom g.hom e.hom.left e.hom.right
        e.hom.w hf)
  exact (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B integerBase hZ
    (@Space.IsQuasiCompact B integerBase hZ)
    (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
    (Stack.faithful_schemeStack_p.{u, w} B integerBase hZ) U y hy F hF hE).2
    (curvesSmall.isQuasiCompact_relocalizeToYoneda_isomSpace_of _ _ (hqc _ _ _))

/-- **Stacks 0DSQ, from the quasi-compactness of `Isom_U(Y, X)`.** Given that the stack of curves
is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), and that
`Isom_U(Y, X) ⟶ U` is quasi-compact for all families of curves `Y` and `X` over a common base
(`hqc`), the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite
presentation, both in the sense of Stacks 04XB. Separatedness is
`AlgebraicGeometry.isSeparated_relativeDiagonal_curvesAlgebraicStack`; finite presentation is
local finite presentation
(`AlgebraicGeometry.isLocallyOfFinitePresentation_diagonal_curvesAlgebraicStack`, from Stacks
0D55 by Stacks 0CMW and 0CMY), quasi-compactness
(`AlgebraicGeometry.isQuasiCompact_relativeDiagonal_curvesAlgebraicStack_of`) and
quasi-separatedness
(`AlgebraicGeometry.isQuasiSeparated_relativeDiagonal_curvesAlgebraicStack`). -/
theorem isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hqc : ∀ (F G : CurveFamily B hZ) (hb : G.base = F.base),
      Space.IsQuasiCompact B integerBase hZ
        (CurveFamily.isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb)))) :
    Stack.IsSeparated B integerBase hZ
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :=
  ⟨isSeparated_relativeDiagonal_curvesAlgebraicStack B hZ h,
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B integerBase hZ _,
    fun U y hy F hF hE =>
      ⟨isLocallyOfFinitePresentation_diagonal_curvesAlgebraicStack B hZ h hlim U y hy F hF hE,
        isQuasiCompact_relativeDiagonal_curvesAlgebraicStack_of B hZ h hqc U y hy F hF hE,
        isQuasiSeparated_relativeDiagonal_curvesAlgebraicStack B hZ h U y hy F hF hE⟩⟩

/-- **Stacks 0DSS, from the quasi-compactness of `Isom_U(Y, X)`.** Given that the stack of curves
is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), and that
`Isom_U(Y, X) ⟶ U` is quasi-compact for all families of curves `Y` and `X` over a common base
(`hqc`), the morphism `Curves → Spec(ℤ)` is quasi-separated and locally of finite presentation:
the finite presentation of the diagonal, the argument `hdiag` of
`isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack`,
is the finite presentation clause of Stacks 0DSQ
(`isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack`). -/
theorem isQuasiSeparated_isLocallyOfFinitePresentation_curvesAlgebraicStack_of_isomQuasiCompact
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hqc : ∀ (F G : CurveFamily B hZ) (hb : G.base = F.base),
      Space.IsQuasiCompact B integerBase hZ
        (CurveFamily.isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb)))) :
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h
    hlim (isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack
      B hZ h hlim hqc).2

end AlgebraicGeometry

end
