module

public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseGenericFibre

/-!
# An open which is dense in the generic fibre is dense in all nearby fibres

Let `f : X ⟶ Y` be a finite type morphism onto an irreducible base with generic point `η`, and
let `U ⊆ X` be an open subscheme whose trace on the generic fibre is dense there. Then the trace
of `U` on `X_y` is dense for every `y` in some nonempty open subset of `Y`.

This is the complementary form of Stacks Tag 054X: the complement of `U` is closed, and a closed
subset of a topological space is nowhere dense exactly when its complement is dense.

## Main results

* `AlgebraicGeometry.exists_open_dense_fiber_preimage`: the shrinking statement.
* `AlgebraicGeometry.isNowhereDense_compl_iff`: the topological equivalence it rests on.

## References

* [Stacks Project, Tag 054X](https://stacks.math.columbia.edu/tag/054X)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The complement of an open set is nowhere dense exactly when that open set is dense. -/
public theorem isNowhereDense_compl_iff {α : Type*} [TopologicalSpace α] {W : Set α}
    (hW : IsOpen W) : IsNowhereDense Wᶜ ↔ Dense W := by
  rw [hW.isClosed_compl.isNowhereDense_iff, interior_compl, Set.compl_empty_iff,
    dense_iff_closure_eq]

/-- An open subscheme whose trace on the generic fibre of a finite type morphism onto an
irreducible base is dense there has dense trace on every fibre over some nonempty open subset
of the base. -/
public theorem exists_open_dense_fiber_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f] (U : X.Opens) (η : Y)
    (hη : IsGenericPoint η Set.univ)
    (hηU : Dense ((f.fiberι η ⁻¹ᵁ U : (f.fiber η).Opens) : Set ↥(f.fiber η))) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, Dense ((f.fiberι y ⁻¹ᵁ U : (f.fiber y).Opens) : Set ↥(f.fiber y)) := by
  have key (y : Y) : IsNowhereDense (f.fiberι y ⁻¹' (U : Set X)ᶜ) ↔
      Dense ((f.fiberι y ⁻¹ᵁ U : (f.fiber y).Opens) : Set ↥(f.fiber y)) := by
    rw [Set.preimage_compl]
    exact isNowhereDense_compl_iff (U.2.preimage (f.fiberι y).continuous)
  obtain ⟨V, hVopen, hVne, hV⟩ := exists_open_isNowhereDense_fiber f (U : Set X)ᶜ
    U.2.isClosed_compl η hη ((key η).mpr hηU)
  exact ⟨V, hVopen, hVne, fun y hy ↦ (key y).mp (hV y hy)⟩

end AlgebraicGeometry

end
