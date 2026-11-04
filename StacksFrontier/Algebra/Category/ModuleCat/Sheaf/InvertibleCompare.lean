module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# The two spellings of invertibility of a sheaf of modules agree

Invertibility of a sheaf `L` of `O`-modules — the assertion that a functor with the universal
property of `F ↦ L ⊗_O F` exists and is an equivalence — is formalised twice in this library,
once as `Stacks.SheafOfModules.IsInvertible` and once as
`AlgebraicGeometry.SheafOfModules.IsInvertible`. The two universal-property structures have the
same fields: the natural maps out of the pointwise presheaf tensor products, and the bijectivity
of the induced map on morphisms into a sheaf. This file records that identification, so that a
result proved against one spelling applies to the other without reproving it.

## Main definitions

* `Stacks.SheafOfModules.tensorLeftUniversalEquiv`: the two universal-property structures are
  equivalent.

## Main results

* `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`: the two invertibility predicates
  agree.

## Implementation notes

The transfer is deliberately *not* registered as an instance in either direction: both
predicates are classes, so a pair of instances would make instance search cycle between them.
Use `isInvertible_iff_algebraicGeometry` (or one of its two directions
`IsInvertible.toAlgebraicGeometry` and `IsInvertible.ofAlgebraicGeometry`) explicitly.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- The two formalisations of the universal property of a left tensor functor are the same
structure: both record the natural maps out of the pointwise presheaf tensor products together
with the bijectivity of the induced map on morphisms into a sheaf. -/
def tensorLeftUniversalEquiv :
    TensorLeftUniversal O hO L F ≃
      AlgebraicGeometry.SheafOfModules.TensorLeftUniversal O hO L F where
  toFun a := ⟨a.ι, a.bijective⟩
  invFun a := ⟨a.ι, a.bijective⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The two invertibility predicates for a sheaf of modules agree. -/
theorem isInvertible_iff_algebraicGeometry :
    IsInvertible O hO L ↔ AlgebraicGeometry.SheafOfModules.IsInvertible O hO L := by
  constructor
  · intro h
    obtain ⟨G, hG, ⟨a⟩⟩ := h.exists_tensorFunctor
    exact ⟨G, hG, ⟨tensorLeftUniversalEquiv O hO L G a⟩⟩
  · intro h
    obtain ⟨G, hG, ⟨a⟩⟩ := h.exists_tensorFunctor
    exact ⟨G, hG, ⟨(tensorLeftUniversalEquiv O hO L G).symm a⟩⟩

/-- An invertible sheaf of modules in the `Stacks` spelling is invertible in the
`AlgebraicGeometry` spelling. -/
theorem IsInvertible.toAlgebraicGeometry (h : IsInvertible O hO L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible O hO L :=
  (isInvertible_iff_algebraicGeometry O hO L).mp h

/-- An invertible sheaf of modules in the `AlgebraicGeometry` spelling is invertible in the
`Stacks` spelling. -/
theorem IsInvertible.ofAlgebraicGeometry
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible O hO L) : IsInvertible O hO L :=
  (isInvertible_iff_algebraicGeometry O hO L).mpr h

end Stacks.SheafOfModules

end
