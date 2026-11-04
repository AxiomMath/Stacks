/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDeligneMumfordLocus

/-!
# The Deligne–Mumford open substack of the stack of curves (Stacks 0DSW)

**Stacks 0DSW**: there is an open substack `Curves^DM ⊂ Curves` such that (1) it is the largest
open substack of `Curves` which is DM; (2) a family of curves `X → S` is classified by a
morphism `S → Curves` factoring through it exactly when `Aut_S(X)` is unramified over `S`;
(3) for `X` proper of dimension `≤ 1` over a field `k`, the point `Spec k → Curves` classifying
`X` factors through it iff `Aut(X)` is geometrically reduced over `k` of dimension `0`, iff
`Aut(X) → Spec k` is unramified.

The statement is that of `AlgebraicGeometry.curvesSmall.exists_deligneMumfordLocus`
(`AlgebraicGeometry.CurvesDeligneMumfordLocus`), at the algebraic stack of curves: its only input,
the algebraicity of `Curves` (Stacks 0D5A), is
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory`, the same algebraic stack
on which Stacks 0DSQ and 0DSS are stated.

## Main results

* `AlgebraicGeometry.curvesSmall.exists_deligneMumfordLocus_unconditional`: **Stacks 0DSW.**

## References

* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

namespace curvesSmall

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- There exists an open substack `Curves^DM ⊂ Curves` of the algebraic stack of curves over
`Spec ℤ` such that

1. `Curves^DM` is the maximal open substack of `Curves` which is DM: it is Deligne–Mumford, and
   every Deligne–Mumford open substack of `Curves` is contained in it;
2. for a family of curves `X → S`, the classifying morphism `S → Curves` factors through
   `Curves^DM` if and only if the group algebraic space `Aut_S(X)` is unramified over `S`;
3. for a field-valued point `x : Spec k → Curves`, classifying a proper `X` of dimension `≤ 1`
   over `k`, the following are equivalent: `x` factors through `Curves^DM`; `Aut(X)` is
   geometrically reduced over `k` of dimension `0`; `Aut(X) → Spec k` is unramified. -/
@[stacks 0DSW]
theorem exists_deligneMumfordLocus_unconditional :
    ∃ W : Stack.OpenSubstack (curvesAlgebraicStack B hZ
        (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)),
      (Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          W.toAlgebraicStack ∧
        ∀ V : Stack.OpenSubstack (curvesAlgebraicStack B hZ
            (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)),
          Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
              V.toAlgebraicStack →
            V.property ≤ W.property) ∧
      (∀ F : CurveFamily B hZ,
        W.property (ShrinkHoms.toShrinkHoms F) ↔
          Space.IsUnramified B integerBase hZ (CurveFamily.autFunctorProjection F)) ∧
      ∀ x : Stack.FieldValuedPoint B integerBase hZ (curvesAlgebraicStack B hZ
          (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)).val.val,
        List.TFAE
          [W.property x.obj,
            Space.IsGeometricallyReduced x.carrier B
                (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
                (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
                (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) ∧
              Space.dimension B (Spec (.of x.carrier))
                (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
                (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
                (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) = 0,
            Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ
              (curvesAlgebraicStack B hZ
                (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)) x] :=
  exists_deligneMumfordLocus (C1590Private.isAlgebraicStack_curvesFiberedCategory.{u, w} B hZ)

end curvesSmall

end AlgebraicGeometry

end
