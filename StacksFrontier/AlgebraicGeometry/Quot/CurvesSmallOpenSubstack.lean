module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenLoci
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothOpenSubstackRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism

/-!
# Open substacks of the small model of the stack of curves

Given that the stack of curves is algebraic, its small model
`AlgebraicGeometry.curvesAlgebraicStack` is an algebraic stack over `Spec(ℤ)`, equivalent over the
site to the category of families of curves. A property of families of curves with condition (o)
of Section 0E0E cuts out an open substack of it (`AlgebraicGeometry.curvesSmallOpenSubstack`).
Smoothness over `Spec(ℤ)` of such an open substack is the smoothness of its inclusion followed by
the structure morphism of Tag 050D, and it passes to smaller properties.

## Main definitions

* `AlgebraicGeometry.curvesSmallEquivalence`: the equivalence of the category of families of
  curves with the small model.
* `AlgebraicGeometry.curvesSmallOpenSubstack`: the open substack cut out by a property with
  condition (o).
* `AlgebraicGeometry.IsSmoothOverIntegers`: smoothness over `Spec(ℤ)` of that open substack.

## Main results

* `AlgebraicGeometry.isSmoothOverIntegers_of_imp`: if `P` implies `Q` and `Curves^Q` is smooth
  over `Spec(ℤ)`, so is `Curves^P`.
* `AlgebraicGeometry.isSmoothOverIntegers_nodal_of_lciPlus`: Tag 0E00 from part (1) of Tag 0DZX,
  through the inclusion `Curves^{nodal} ⊂ Curves^{lci+}`.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E00](https://stacks.math.columbia.edu/tag/0E00)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- The equivalence of the category of families of curves with the small model of the stack of
curves. -/
abbrev curvesSmallEquivalence :
    CurveFamily B hZ ≌ (curvesAlgebraicStack B hZ h).val.val.obj :=
  (curvesSmallEquivalenceOver B hZ).toEquivalence

/-- The equivalence of the category of families of curves with the small model is compatible
with the two projections to the site. -/
theorem curvesSmallEquivalence_functor_comp_p :
    (curvesSmallEquivalence B hZ h).functor ⋙ (curvesAlgebraicStack B hZ h).val.val.p =
      curvesProjectionOver B hZ :=
  (curvesSmallEquivalenceOver B hZ).hom.w

/-- **The open substack of the small model of curves cut out by condition (o).** -/
abbrev curvesSmallOpenSubstack {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) : Stack.OpenSubstack (curvesAlgebraicStack B hZ h) :=
  (curvesOpenSubstackOfIsOpenCurvesLocus B hZ hP (curvesAlgebraicStack B hZ h)
    (curvesSmallEquivalence B hZ h) (curvesSmallEquivalence_functor_comp_p B hZ h)).1

/-- A family of curves lies in the open substack of the small model cut out by `P` exactly when
it has `P`. -/
theorem curvesSmallOpenSubstack_property_iff {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (F : CurveFamily B hZ) :
    (curvesSmallOpenSubstack B hZ h hP).property ((curvesSmallEquivalence B hZ h).functor.obj F) ↔
      P F :=
  curvesOpenSubstackOfIsOpenCurvesLocus_property_iff B hZ hP _ _ _ F

/-- **Smoothness over `Spec(ℤ)` of an open substack of curves.** The open substack of the small
model cut out by `P` is smooth over `Spec(ℤ)`: its inclusion followed by the structure morphism
of the small model to `Spec(ℤ)` (Tag 050D) is smooth. -/
abbrev IsSmoothOverIntegers {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) : Prop :=
  Stack.AlgebraicStacks.IsSmooth B integerBase hZ
    ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
      Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))

/-- If `P` implies `Q` and the open substack of curves cut out by `Q` is smooth over `Spec(ℤ)`, so
is the one cut out by `P`. -/
theorem isSmoothOverIntegers_of_imp {P Q : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (hQ : IsOpenCurvesLocus B hZ Q) (hPQ : ∀ F, P F → Q F)
    (hsm : IsSmoothOverIntegers B hZ h hQ) : IsSmoothOverIntegers B hZ h hP :=
  Stack.OpenSubstack.isSmooth_inclusion_comp_of_le B integerBase hZ _
    (curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ hP hQ hPQ _ _ _) hsm

/-- **Tag 0E00 from part (1) of Tag 0DZX.** If `Curves^{lci+}` is smooth over `Spec(ℤ)`, so is
`Curves^{nodal}`, as `Curves^{nodal} ⊂ Curves^{lci+}`. -/
theorem isSmoothOverIntegers_nodal_of_lciPlus
    (hsm : IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_lciPlus B hZ)) :
    IsSmoothOverIntegers B hZ h (isOpenCurvesLocus_isAtWorstNodal B hZ) :=
  isSmoothOverIntegers_of_imp B hZ h _ _ (isAtWorstNodal_le_lciPlus B hZ) hsm

end AlgebraicGeometry

end
