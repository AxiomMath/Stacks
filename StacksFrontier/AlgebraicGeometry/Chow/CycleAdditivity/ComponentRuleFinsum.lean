module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Finiteness
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.ComponentRules

/-!
# Extending a component rule over a locally finite sum of cycles

The coefficientwise extension `Stacks.Chow.ComponentRule.extendCoeff` of a component rule commutes
with locally finite sums of cycles: if `α = ∑ᶠ j, D j` coefficientwise and the supports of the
`D j` lie in a locally finite family of sets, then the extension over `α` is, coefficientwise, the
locally finite sum of the extensions over the `D j`.

## Main results

* `Stacks.Chow.ComponentRule.extendCoeff_finsum` — the extension of a component rule over a
  locally finite sum of cycles is the locally finite sum of the extensions.
* `Stacks.Chow.IntegralComponentRule.extendCycleGroup_finsum` — the same identity for the
  homomorphism of cycle groups induced by a rule on integral components.

## References

* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology

namespace Stacks.Chow

universe u v

/-! ### Component rules -/

section ComponentRule

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
  (G : ComponentRule i)

/-- If a coefficient function `α` is the locally finite sum of the cycles `D j`, whose supports
lie in the locally finite family `E`, then the extension of a component rule over `α` is,
coefficientwise, the locally finite sum of its extensions over the `D j`. -/
theorem ComponentRule.extendCoeff_finsum {J : Type*} (D : J → Function.locallyFinsupp X ℤ)
    (E : J → Set X) (hE : LocallyFinite E) (hDE : ∀ j, Function.support (D j) ⊆ E j)
    (α : X → ℤ) (hα : ∀ x : X, α x = ∑ᶠ j : J, D j x) (y : Y) :
    G.extendCoeff α y = ∑ᶠ j : J, G.extendCoeff (D j) y := by
  obtain ⟨t, ht, hAfin⟩ := hE (i y)
  have hgen : ∀ x : X, i y ∈ closure ({x} : Set X) → x ∈ t := fun x hx ↦
    interior_subset ((specializes_iff_mem_closure.2 hx).mem_open isOpen_interior
      (mem_interior_iff_mem_nhds.2 ht))
  set A : Set J := {j | (E j ∩ t).Nonempty}
  set B : Set X := ⋃ j ∈ A,
    {x : X | (∃ a ∈ ({i y} : Set X), a ∈ closure ({x} : Set X)) ∧ D j x ≠ 0}
  have hBfin : B.Finite := hAfin.biUnion fun j _ ↦
    finite_support_inter_generalizations (D j).locallyFiniteSupport isCompact_singleton
  have hvan : ∀ (j : J) (x : X), x ∈ (Set.univ : Set X) →
      D j x * G.cycle x y ≠ 0 → j ∈ A ∧ x ∈ B := by
    intro j x _ hne
    have hDx : D j x ≠ 0 := left_ne_zero_of_mul hne
    have hclos : i y ∈ closure ({x} : Set X) :=
      G.mem_closure_of_apply_ne_zero x y (right_ne_zero_of_mul hne)
    have hjA : j ∈ A := ⟨x, hDE j hDx, hgen x hclos⟩
    exact ⟨hjA, Set.mem_biUnion hjA ⟨⟨i y, rfl, hclos⟩, hDx⟩⟩
  calc G.extendCoeff α y = ∑ᶠ x : X, ∑ᶠ j : J, D j x * G.cycle x y :=
        finsum_congr fun x ↦ by rw [hα x, finsum_mul]
    _ = ∑ᶠ x ∈ (Set.univ : Set X), ∑ᶠ j : J, D j x * G.cycle x y := (finsum_mem_univ _).symm
    _ = ∑ᶠ j : J, ∑ᶠ x ∈ (Set.univ : Set X), D j x * G.cycle x y :=
        finsum_finsum_mem_comm _ Set.univ hAfin hBfin (Set.subset_univ B) hvan
    _ = ∑ᶠ j : J, G.extendCoeff (D j) y := finsum_congr fun j ↦ finsum_mem_univ _

end ComponentRule

/-! ### Rules on integral components -/

section IntegralComponentRule

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {p : X ⟶ C.S} [LocallyOfFiniteType p]
  {q : Y ⟶ C.S} [LocallyOfFiniteType q] {g : Y ⟶ X} {k : ℤ}

/-- If a `(k+1)`-cycle `α` is coefficientwise the locally finite sum of the `(k+1)`-cycles `D j`,
whose supports lie in the locally finite family `E`, then the induced homomorphism
`Z_{k+1}(X) → Z_k(Y)` of a rule on integral components takes `α` to the locally finite sum of the
values it takes on the `D j`. -/
theorem IntegralComponentRule.extendCycleGroup_finsum (R : IntegralComponentRule C p q g k)
    {J : Type*} (D : J → CycleGroup C p (k + 1)) (E : J → Set X) (hE : LocallyFinite E)
    (hDE : ∀ j, Function.support (D j).1 ⊆ E j) (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, (D j).1 x) (y : Y) :
    (R.extendCycleGroup α).1 y = ∑ᶠ j : J, (R.extendCycleGroup (D j)).1 y :=
  R.toComponentRule.extendCoeff_finsum (fun j ↦ (D j).1) E hE hDE α.1 hα y

end IntegralComponentRule

end Stacks.Chow

end
