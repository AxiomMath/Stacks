module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic

/-!
# The two invertibility predicates of Tag 01CS agree

The invertibility predicate of [Stacks, Tag 01CS] is available as two constants,
`AlgebraicGeometry.SheafOfModules.IsInvertible` and `Stacks.SheafOfModules.IsInvertible`, each
asserting that tensoring on the left with `L` is an equivalence `F` satisfying its own copy of the
universal property `TensorLeftUniversal`. This file shows that the two predicates are equivalent.

## Main definitions

* `Stacks.InvertibleBridge.tensorLeftUniversalToTensorInvertible` and
  `Stacks.InvertibleBridge.tensorLeftUniversalOfTensorInvertible`: the passage between the two
  copies of the universal property `TensorLeftUniversal`.

## Main results

* `Stacks.InvertibleBridge.isInvertible_iff`: the two invertibility predicates are equivalent.
* `Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible` and
  `Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible`: the two
  implications, with the hypothesis taken as an instance argument.

## Implementation notes

The two copies of `TensorLeftUniversal` have the same fields `ι` and `bijective` at the same
types, so the passage between them is field-for-field.

No instance is declared in either direction, so that instance search for one predicate never
searches for the other.

The triviality predicates `AlgebraicGeometry.SheafOfModules.IsTrivial` and
`Stacks.SheafOfModules.IsTrivial` are both `abbrev`s for `Nonempty (L ≅ 𝒪)`, so they are already
interchangeable.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.InvertibleBridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}
  {L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
  {F : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}

/-- An `AlgebraicGeometry.SheafOfModules.TensorLeftUniversal` structure for `L` and `F`, viewed
as a `Stacks.SheafOfModules.TensorLeftUniversal` structure with the same fields. -/
def tensorLeftUniversalToTensorInvertible
    (a : AlgebraicGeometry.SheafOfModules.TensorLeftUniversal O hO L F) :
    Stacks.SheafOfModules.TensorLeftUniversal O hO L F where
  ι := a.ι
  bijective := a.bijective

/-- A `Stacks.SheafOfModules.TensorLeftUniversal` structure for `L` and `F`, viewed as an
`AlgebraicGeometry.SheafOfModules.TensorLeftUniversal` structure with the same fields. -/
def tensorLeftUniversalOfTensorInvertible
    (a : Stacks.SheafOfModules.TensorLeftUniversal O hO L F) :
    AlgebraicGeometry.SheafOfModules.TensorLeftUniversal O hO L F where
  ι := a.ι
  bijective := a.bijective

/-- The invertibility predicates `AlgebraicGeometry.SheafOfModules.IsInvertible` and
`Stacks.SheafOfModules.IsInvertible` of a sheaf of modules `L` are equivalent. -/
theorem isInvertible_iff :
    AlgebraicGeometry.SheafOfModules.IsInvertible O hO L ↔
      Stacks.SheafOfModules.IsInvertible O hO L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry O hO L).symm

/-- A sheaf of modules invertible in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`
is invertible in the sense of `Stacks.SheafOfModules.IsInvertible`. -/
theorem stacksIsInvertible_of_algebraicGeometryIsInvertible
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    Stacks.SheafOfModules.IsInvertible O hO L :=
  isInvertible_iff.mp ‹_›

/-- A sheaf of modules invertible in the sense of `Stacks.SheafOfModules.IsInvertible` is
invertible in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem algebraicGeometryIsInvertible_of_stacksIsInvertible
    [Stacks.SheafOfModules.IsInvertible O hO L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible O hO L :=
  isInvertible_iff.mpr ‹_›

end Stacks.InvertibleBridge

end
