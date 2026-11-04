module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingFinitePresentationEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalSituationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine

/-!
# The stack of curves is quasi-separated and locally of finite presentation (Stacks 0DSS)

**Stacks 0DSS**: the morphism `Curves → Spec(ℤ)` is quasi-separated and locally of finite
presentation. It is stated at `AlgebraicGeometry.curvesAlgebraicStack B hZ h`, the small model of
the stack of curves as an object of `AlgebraicGeometry.Stack.AlgebraicStacks`, which takes `h`,
the algebraicity of the stack of curves (Stacks 0D5A), as an argument; the two predicates are this
library's Stacks 04YW (`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated`) and Stacks 06Q2
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation`) of the structure
morphism `AlgebraicGeometry.Stack.structureMorphism` of Stacks 050D.

## Local finite presentation

The source's proof: by Stacks 0CMY it suffices that `Curves` is limit preserving, which is
Stacks 0D55. Limit preservation transports to the small model along its equivalence over the site
(`AlgebraicGeometry.Stack.isLimitPreserving_of_equivalenceOver`); it makes the structure functor
to the site limit preserving on objects
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving`), hence
also the structure morphism of Stacks 050D, whose target, the algebraic stack of `Spec(ℤ)` itself,
is limit preserving by Stacks 0CMX
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_toTerminalCFG`); Stacks 0CMY (2) ⟹ (3)
concludes.

## Quasi-separatedness

Quasi-separatedness of `Curves → Spec(ℤ)` asks that its diagonal be quasi-compact and
quasi-separated (Stacks 04YW), which is immediate from the finite presentation of the diagonal,
Stacks 0DSQ. The local finite presentation clause of Stacks 0DSQ follows from Stacks 0D55 in the
same way as above
(`AlgebraicGeometry.isLocallyOfFinitePresentation_diagonal_curvesAlgebraicStack`); the
quasi-compactness and quasi-separatedness clauses of Stacks 0DSQ are not proved here, and the whole
statement of Stacks 0DSS is stated with the finite presentation of the diagonal as the argument
`hdiag`.

None of these declarations is registered: all take `h` (Stacks 0D5A) and `hlim` (Stacks 0D55),
and the whole statement takes `hdiag` in addition.

## Main results

All names below are in the namespace `AlgebraicGeometry`.

* `isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack`: the local finite
  presentation clause of Stacks 0DSS.
* `isLocallyOfFinitePresentation_diagonal_curvesAlgebraicStack`: the local finite presentation
  clause of Stacks 0DSQ.
* `Stack.AlgebraicStacks.isQuasiSeparated_of_isRelativelyFinitePresentation_relativeDiagonal`:
  a 1-morphism whose diagonal is of finite presentation is quasi-separated.
* `isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack`:
  the statement of Stacks 0DSS, from the finite presentation of the diagonal.

## References

* [Stacks Project, Tag 0DSS](https://stacks.math.columbia.edu/tag/0DSS)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0D55](https://stacks.math.columbia.edu/tag/0D55)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The small model of the stack of curves is limit preserving** in the sense of Artin's Axioms,
Definition 07XL, when the stack of curves is: the two are equivalent over the site
(`AlgebraicGeometry.curvesSmallEquivalenceOver`). -/
theorem isLimitPreserving_curvesSmall
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B integerBase hZ (curvesSmall B hZ) :=
  Stack.isLimitPreserving_of_equivalenceOver B integerBase hZ (curvesSmall B hZ)
    (curvesFiberedCategory B hZ) (curvesSmallEquivalenceOver B hZ).symm hlim

/-- **The structure morphism of the algebraic stack of the base is limit preserving.** The
algebraic stack represented by `S` is limit preserving in the sense of Artin's Axioms,
Definition 07XL: its structure morphism is locally of finite presentation, being the identity,
and Stacks 0CMX applies. -/
theorem Stack.isLimitPreserving_schemeStack_id (S : Scheme.{u}) (hS : B.Contains S) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS
      (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val :=
  (Stack.AlgebraicStacks.isLimitPreserving_of_isLocallyOfFinitePresentation B S hS _
    (Stack.isLocallyOfFinitePresentation_structureMorphism_schemeStack B S hS _
      (by
        show LocallyOfFinitePresentation (B.inclusion.map (𝟙 _))
        simp only [CategoryTheory.Functor.map_id]
        infer_instance))).1

/-- **Stacks 0DSS, local finite presentation.** Given that the stack of curves is algebraic
(`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), the morphism `Curves → Spec(ℤ)` is
locally of finite presentation in the sense of Stacks 06Q2: by Stacks 0CMY, limit preservation of
the structure morphism suffices. -/
theorem isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ)) :
    Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects
    B integerBase hZ _
    (Stack.isLimitPreservingOnObjects_of_toTerminalCFG B integerBase hZ (curvesSmall B hZ) _
      (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom
      (Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B integerBase hZ
        (curvesSmall B hZ) (isLimitPreserving_curvesSmall B hZ hlim))
      (Stack.isLimitPreserving_schemeStack_id.{u, w} B integerBase hZ))

/-- **The diagonal of the stack of curves is locally of finite presentation**, the local finite
presentation clause of Stacks 0DSQ, read as in Properties of Stacks, Section 04XB: every algebraic
space representing a base change of `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` along a
scheme-valued point is locally of finite presentation. Given that the stack of curves is algebraic
(`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), `Curves → Spec(ℤ)` is locally of
finite presentation, so locally of finite type, hence its diagonal is locally of finite
presentation (Stacks 0CMG); a representable 1-morphism locally of finite presentation is limit
preserving on objects (Stacks 0CMY), which is the condition of Stacks 04XB (Stacks 06CX). This is
the source's argument through Stacks 0CMW and 0CMY. -/
theorem isLocallyOfFinitePresentation_diagonal_curvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (Stack.AlgebraicStacks.twoFibreProduct B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))).val.val.obj)
    (hy : y ⋙ (Stack.AlgebraicStacks.twoFibreProduct B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))).val.val.p =
      Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (curvesAlgebraicStack B hZ h).val.val.p
        (Stack.AlgebraicStacks.twoFibreProduct B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))).val.val.p y
        (CatFiberedInGroupoids.homFunctor (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))).hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Space.IsLocallyOfFinitePresentation B integerBase hZ
      (algebraicSpaceMap B integerBase hZ U
        ((spacesOverSmallerBaseFunctor B U.left.1 integerBase U.left.2 hZ U.hom).obj
          ⟨F, hF⟩)).hom := by
  let f := Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)
  have hΔ := Stack.AlgebraicStacks.isLocallyOfFinitePresentation_relativeDiagonal B integerBase hZ
    f (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
      (isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim))
  exact (Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B integerBase hZ
    _ _ (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ f).hom
    (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B integerBase hZ f)).1
    (Stack.AlgebraicStacks.isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation B integerBase
      hZ _ hΔ) U y hy F hF hE

/-- **A 1-morphism whose diagonal is of finite presentation is quasi-separated.** If the relative
diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` of a 1-morphism of algebraic stacks is of finite presentation in the
sense of Properties of Stacks, Section 04XB, then it is quasi-compact and quasi-separated there,
which is quasi-separatedness of `f` (Stacks 04YW). -/
theorem Stack.AlgebraicStacks.isQuasiSeparated_of_isRelativelyFinitePresentation_relativeDiagonal
    (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    (hΔ : Stack.AlgebraicStacks.IsRelativelyFinitePresentation B S hS
      (Stack.AlgebraicStacks.relativeDiagonal B S hS f)) :
    Stack.AlgebraicStacks.IsQuasiSeparated B S hS f :=
  ⟨fun U y hy F hF hE => (hΔ.2 U y hy F hF hE).2.1,
    fun U y hy F hF hE => (hΔ.2 U y hy F hF hE).2.2⟩

/-- **Stacks 0DSS, from the finite presentation of the diagonal.** Given that the stack of curves
is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`, Stacks 0D55), and that its diagonal
`Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is of finite presentation (`hdiag`, the finite
presentation clause of Stacks 0DSQ), the morphism `Curves → Spec(ℤ)` is quasi-separated and
locally of finite presentation. This is the source's proof: quasi-separatedness asks that the
diagonal be quasi-compact and quasi-separated, which is immediate from Stacks 0DSQ, and local
finite presentation is Stacks 0CMY applied to Stacks 0D55. -/
theorem isQuasiSeparated_and_isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hdiag : Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
      (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))) :
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  ⟨Stack.AlgebraicStacks.isQuasiSeparated_of_isRelativelyFinitePresentation_relativeDiagonal B
      integerBase hZ _ hdiag,
    isLocallyOfFinitePresentation_structureMorphism_curvesAlgebraicStack B hZ h hlim⟩

end AlgebraicGeometry

end
