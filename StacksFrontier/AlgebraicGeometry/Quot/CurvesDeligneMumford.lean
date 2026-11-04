module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# The Deligne–Mumford locus of the stack of curves (Stacks 0DSW)

Given that the stack of curves `Curves` is algebraic (Stacks 0D5A), its Deligne–Mumford locus
`Curves^DM` (Stacks 0DSM) is the largest Deligne–Mumford open substack, and its objects are the
families of curves `X → S` whose automorphism group algebraic space `Aut_S(X)` is unramified
over `S`. Over a field, it is equivalent that `Aut(X)` is unramified, and — when `Aut(X)` is
locally of finite type over the field, as the diagonal of `Curves` makes it (Stacks 0DSQ) — that
it is geometrically reduced of dimension zero.

## Main results

* `AlgebraicGeometry.curvesSmall.exists_largest_isAbsolutelyDM_openSubstack`: Stacks 0DSW (1).
* `AlgebraicGeometry.curvesSmall.dmLocus_toShrinkHoms_iff`: Stacks 0DSW (2).
* `AlgebraicGeometry.curvesSmall.tfae_dmLocus_fieldValuedPoint`: Stacks 0DSW (3).

Parts (1) and (2) hold for every algebraic stack
(`AlgebraicGeometry.Stack.exists_largest_isAbsolutelyDM_openSubstack_eq_dmLocus`,
`AlgebraicGeometry.Stack.dmLocus_iff_isUnramified_automorphismGroupSpace`); here they are read at
the stack of curves, the automorphism group space of an object being the automorphism functor of
the family it classifies
(`AlgebraicGeometry.curvesSmall.holdsOnEveryEtaleChart_automorphismGroupSpace_iff`).

These are not registered for Stacks 0DSW: they are stated at
`AlgebraicGeometry.curvesAlgebraicStack`, which takes the algebraicity of the stack of curves
(Stacks 0D5A) as an argument, and part (3) takes the local finite type of `Aut(X)` (a consequence
of Stacks 0DSQ) as an argument.

## References

* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
* [Stacks Project, Tag 0DSM](https://stacks.math.columbia.edu/tag/0DSM)
* [Stacks Project, Tag 0DSN](https://stacks.math.columbia.edu/tag/0DSN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace curvesSmall

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Stacks 0DSW (1), at the stack of curves.** -/
theorem exists_largest_isAbsolutelyDM_openSubstack :
    ∃ W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      W.property =
        Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h) ∧
      Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal W.toAlgebraicStack ∧
      ∀ V : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
            V.toAlgebraicStack →
          V.property ≤ W.property :=
  Stack.exists_largest_isAbsolutelyDM_openSubstack_eq_dmLocus B integerBase hZ B.contains_terminal _

/-- **Stacks 0DSW (2), at the stack of curves.** A family of curves `X → S` is classified by an
object of the Deligne–Mumford locus exactly when `Aut_S(X) → S` is unramified. -/
theorem dmLocus_toShrinkHoms_iff (F : CurveFamily B hZ) :
    Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h)
        (ShrinkHoms.toShrinkHoms F) ↔
      Space.IsUnramified B integerBase hZ (CurveFamily.autFunctorProjection F) :=
  (Stack.dmLocus_iff_isUnramified_automorphismGroupSpace B integerBase hZ B.contains_terminal
    (curvesAlgebraicStack B hZ h) (U := F.base) ⟨ShrinkHoms.toShrinkHoms F, rfl⟩).trans
    (holdsOnEveryEtaleChart_automorphismGroupSpace_iff ⟨ShrinkHoms.toShrinkHoms F, rfl⟩ _ _)

/-- **Stacks 0DSW (3), at the stack of curves.** Let `x : Spec k → Curves` be a field-valued point,
classifying a proper curve `X` over `k`, whose automorphism group algebraic space `Aut(X)` is
locally of finite type over `k`. The following are equivalent: `x` factors through `Curves^DM`;
`Aut(X)` is geometrically reduced over `k` and has dimension `0`; `Aut(X) → Spec k` is
unramified. -/
theorem tfae_dmLocus_fieldValuedPoint
    (x : Stack.FieldValuedPoint B integerBase hZ (curvesAlgebraicStack B hZ h).val.val)
    (hlft : Space.IsLocallyOfFiniteType B x.base.left.1 x.base.left.2
      (Stack.automorphismGroupSpace B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (curvesAlgebraicStack B hZ h).property x.base ⟨x.obj, x.over⟩).obj.X.hom) :
    List.TFAE
      [Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h) x.obj,
        Space.IsGeometricallyReduced x.carrier B
            (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) ∧
          Space.dimension B (Spec (.of x.carrier))
            (Stack.contains_spectrum_fieldValuedPoint B integerBase hZ x)
            (Stack.automorphismGroupSpaceOverField B integerBase hZ _ x)
            (Stack.isAlgebraicSpace_automorphismGroupSpaceOverField B integerBase hZ _ x) = 0,
        Stack.IsUnramifiedAutomorphismGroupSpace B integerBase hZ
          (curvesAlgebraicStack B hZ h) x] := by
  tfae_have 1 ↔ 3 := Stack.dmLocus_apply_iff_isUnramifiedAutomorphismGroupSpace B integerBase hZ
    B.contains_terminal _ x
  tfae_have 3 ↔ 2 :=
    Stack.isUnramifiedAutomorphismGroupSpace_iff_isGeometricallyReduced_and_dimension_eq_zero B
      integerBase hZ _ x hlft
  tfae_finish

end curvesSmall

end AlgebraicGeometry

end
