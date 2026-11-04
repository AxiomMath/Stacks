module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsModel

/-!
# The small model of the stack of curves

The category `CurveFamily B hZ` of families of curves of Stacks 0D4Z has morphisms in
`Type (u + 1)`: a morphism of families is a cartesian square, and its morphism of total spaces is a
morphism of presheaves on the big fppf site, whose objects live one universe up. The 2-category
`AlgebraicGeometry.Stack.AlgebraicStacks.{u, w}` asks for categories over the site with morphisms
in the universe `u` of the schemes, so `AlgebraicGeometry.curvesFiberedCategory` is not an object
of it, and no statement about the stack of curves as an object of that 2-category typechecks.

This is a matter of presentation only. The hom sets of `CurveFamily B hZ` are `u`-small: a morphism
is determined by its morphism of base schemes, a morphism of the site, and its morphism of total
spaces, a morphism of presheaves of `Type u` on the essentially small big fppf site
(`AlgebraicGeometry.locallySmall_presheaf_bigFppfOver`). Shrinking the hom sets
(`StacksRepresentableCFG.shrinkHomsEquivalenceOver`) gives `AlgebraicGeometry.curvesSmall`, a
category fibred in groupoids over the site with morphisms in `Type u`, equivalent over the site to
`AlgebraicGeometry.curvesFiberedCategory`; algebraicity transports along that equivalence by
`AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver`, in both directions.

## Main definitions

* `AlgebraicGeometry.curvesSmall`: the hom-shrunk model of the stack of curves, at hom universe
  `u`.
* `AlgebraicGeometry.curvesSmallEquivalenceOver`: its equivalence over the site with
  `AlgebraicGeometry.curvesFiberedCategory`.
* `AlgebraicGeometry.curvesAlgebraicStack`: given algebraicity of the stack of curves, the model as
  an object of `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Main results

* `AlgebraicGeometry.locallySmall_curveFamily`: the hom sets of `CurveFamily B hZ` are `u`-small.
* `AlgebraicGeometry.isAlgebraicStack_curvesSmall_iff`: the stack of curves is algebraic exactly
  when its small model is.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The hom sets of the category of families of curves are `u`-small.** A morphism of families is
determined by its morphism of base schemes, a morphism of the site, and its morphism of total
spaces, a morphism of presheaves of `Type u` on the big fppf site, which is locally small. -/
theorem locallySmall_curveFamily : LocallySmall.{u} (CurveFamily B hZ) where
  hom_small X Y := by
    have : Small.{u} (X.total.obj ⟶ Y.total.obj) := small_hom_presheaf _ _
    exact small_of_injective (f := fun f : X ⟶ Y => (f.baseMap, f.totalMap.hom)) fun f g h =>
      CurveFamily.Hom.ext (congrArg Prod.fst h) (ObjectProperty.hom_ext _ (congrArg Prod.snd h))

/-- **The small model of the stack of curves.** The category `ShrinkHoms (CurveFamily B hZ)`, with
the families of curves as objects and morphisms in the universe of the site, over the big fppf site
of `Spec(ℤ)` through the projection of `AlgebraicGeometry.curvesFiberedCategory`. -/
noncomputable def curvesSmallBased : BasedCategory.{u, u + 1} (BigFppfOver B integerBase hZ) :=
  letI := locallySmall_curveFamily B hZ
  { obj := ShrinkHoms.{u + 1} (CurveFamily B hZ)
    p := ShrinkHoms.inverse (CurveFamily B hZ) ⋙ curvesProjectionOver B hZ }

/-- The small model of the stack of curves is equivalent over the site to the stack of curves. -/
noncomputable def curvesSmallEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (curvesFiberedCategory B hZ).val.p
      (curvesSmallBased B hZ).p :=
  letI := locallySmall_curveFamily B hZ
  StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} (curvesProjectionOver B hZ)

/-- The small model of the stack of curves is fibred in groupoids. -/
theorem isFiberedInGroupoids_curvesSmall : (curvesSmallBased B hZ).p.IsFiberedInGroupoids :=
  StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
    (curvesSmallEquivalenceOver B hZ).symm (curvesFiberedCategory B hZ).property

/-- **The small model of the stack of curves, as a category fibred in groupoids** at hom universe
`u`, the universes of the objects of `AlgebraicGeometry.Stack.AlgebraicStacks`. -/
noncomputable def curvesSmall :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  ⟨curvesSmallBased B hZ, isFiberedInGroupoids_curvesSmall B hZ⟩

/-- **The stack of curves is algebraic exactly when its small model is**: algebraicity transports
along the equivalence over the site `AlgebraicGeometry.curvesSmallEquivalenceOver`, in both
directions (Stacks 03YQ). -/
theorem isAlgebraicStack_curvesSmall_iff :
    Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesSmall B hZ).val ↔
      Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val :=
  ⟨Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ
      (curvesSmallEquivalenceOver B hZ).symm,
    Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ (curvesSmallEquivalenceOver B hZ)⟩

/-- **The stack of curves as an algebraic stack.** Given that the stack of curves is algebraic, its
small model `AlgebraicGeometry.curvesSmall` as an object of
`AlgebraicGeometry.Stack.AlgebraicStacks`. -/
noncomputable def curvesAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    Stack.AlgebraicStacks.{u, w} B integerBase hZ :=
  ⟨curvesSmall B hZ, (isAlgebraicStack_curvesSmall_iff B hZ).2 h⟩

end AlgebraicGeometry

end
