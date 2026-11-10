module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.CyclePresentation
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.Topology.Dimension.KrullSeparation

/-!
# The reduced closure of a non-closed point has dimension at least one

In a Kolmogorov space the closure of a non-closed point has Krull dimension at least one. For `x`
a non-closed point of a scheme `X`, the reduced induced closed subscheme on `closure {x}` has
topological Krull dimension at least one, and when `X` is proper over a field that dimension is a
natural number `d` with `1 ≤ d`.

## Main results

* `exists_mem_closure_singleton_ne`: a non-closed point has a second point in its closure.
* `one_le_topologicalKrullDim_closure_singleton`: in a Kolmogorov space the closure of a
  non-closed point has Krull dimension at least one.
* `AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isProper`: a nonempty scheme proper
  over a field has a natural-number topological Krull dimension.
* `AlgebraicGeometry.Scheme.IdealSheafData.one_le_topologicalKrullDim_subscheme_closure`: the
  reduced closure of a non-closed point has dimension at least one.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_topologicalKrullDim_subscheme_closure_eq`: over a
  field, for `X` proper, that dimension is a natural number `d` with `1 ≤ d`.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace
open Stacks.AlgebraicGeometry.ComponentDegrees
  (topologicalKrullDim_subscheme_vanishingIdeal_closure)

universe u

/-! ### The topological statement -/

/-- A non-closed point has a second point in its closure. -/
public theorem exists_mem_closure_singleton_ne {T : Type*} [TopologicalSpace T] {x : T}
    (hx : ¬ IsClosed ({x} : Set T)) : ∃ y ∈ closure ({x} : Set T), y ≠ x := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  exact hx (subset_antisymm (fun z hz ↦ hcon z hz) subset_closure ▸ isClosed_closure)

/-- In a Kolmogorov space the closure of a non-closed point has Krull dimension at least one. -/
public theorem one_le_topologicalKrullDim_closure_singleton {T : Type*} [TopologicalSpace T]
    [T0Space T] {x : T} (hx : ¬ IsClosed ({x} : Set T)) :
    (1 : WithBot ℕ∞) ≤ topologicalKrullDim ↥(closure ({x} : Set T)) := by
  obtain ⟨y, hy, hyx⟩ := exists_mem_closure_singleton_ne hx
  refine one_le_topologicalKrullDim_of_specializes_of_ne
    (x := (⟨x, subset_closure rfl⟩ : ↥(closure ({x} : Set T))))
    (y := (⟨y, hy⟩ : ↥(closure ({x} : Set T)))) ?_ ?_
  · exact Topology.IsInducing.subtypeVal.specializes_iff.mp (specializes_iff_mem_closure.mpr hy)
  · exact fun h ↦ hyx (congrArg Subtype.val h).symm

namespace AlgebraicGeometry

/-! ### A nonempty proper scheme over a field has a natural-number dimension -/

/-- The topological Krull dimension of a nonempty scheme proper over a field is a natural
number. -/
public theorem exists_topologicalKrullDim_eq_natCast_of_isProper (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hX : Nonempty X) :
    ∃ d : ℕ, topologicalKrullDim X = (d : WithBot ℕ∞) := by
  have htop : topologicalKrullDim X ≠ ⊤ := topologicalKrullDim_ne_top_of_isProper k f
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact fun h ↦ h.false hX.some
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hm' : m ≠ ⊤ := by rintro rfl; exact htop hm.symm
  exact ⟨m.toNat, by rw [← hm]; exact congrArg _ (ENat.natCast_toNat hm').symm⟩

namespace Scheme.IdealSheafData

/-! ### The reduced closure of a non-closed point -/

variable {X : Scheme.{u}} (x : X)

/-- The reduced induced closed subscheme on the closure of a non-closed point has topological
Krull dimension at least one. -/
public theorem one_le_topologicalKrullDim_subscheme_closure
    (hx : ¬ IsClosed ({x} : Set X)) :
    (1 : WithBot ℕ∞) ≤
      topologicalKrullDim (vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme := by
  rw [topologicalKrullDim_subscheme_vanishingIdeal_closure]
  exact one_le_topologicalKrullDim_closure_singleton hx

/-- For `X` proper over a field, the reduced induced closed subscheme on the closure of a
non-closed point has topological Krull dimension a natural number `d` with `1 ≤ d`. -/
public theorem exists_topologicalKrullDim_subscheme_closure_eq (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hx : ¬ IsClosed ({x} : Set X)) :
    ∃ d : ℕ, 1 ≤ d ∧
      topologicalKrullDim (vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme =
        (d : WithBot ℕ∞) := by
  have hne : Nonempty (vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme :=
    (isIntegral_subscheme_vanishingIdeal_closure x).nonempty
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq_natCast_of_isProper k
    ((vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι ≫ f) hne
  exact ⟨d, by exact_mod_cast (one_le_topologicalKrullDim_subscheme_closure x hx).trans_eq hd, hd⟩

end Scheme.IdealSheafData

end AlgebraicGeometry

end
