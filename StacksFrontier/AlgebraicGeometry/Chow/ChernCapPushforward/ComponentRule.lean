module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Finiteness
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence

/-!
# Pushing a coefficientwise construction forward along a proper map

A cycle on `X` built coefficientwise from the integral components of `X` is the extension
`Stacks.Chow.ComponentRule.extend` of a rule attaching a cycle to each point of `X`. This file
proves two identities comparing such a cycle with the proper pushforward of a cycle, at the level
of topological spaces and `Function.locallyFinsupp`:

* pushing forward commutes with the extension: `f_*(∑_x α(x) · c(x)) = ∑_x α(x) · f_*(c(x))`
  (`Stacks.Chow.ComponentRule.map_extendCycle_apply`);
* extending over a pushforward reindexes as a sum over the source:
  `∑_y (f_*α)(y) · c(y) = ∑_x α(x) · w(x) · c(f x)`
  (`Stacks.Chow.ComponentRule.extendCoeff_map_apply`).

## Main results

* `Stacks.Chow.ComponentRule.map_extendCycle_apply` — the pushforward of an extension.
* `Stacks.Chow.ComponentRule.extendCoeff_map_apply` — the extension of a pushforward.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open Set Topology

namespace Stacks.Chow.ComponentRule

/-! ### The pushforward of an extension -/

/-- **Pushing forward an extension.** The pushforward along a spectral map `f` with compact
fibres of the cycle obtained by extending a component rule over `α` is the coefficientwise sum of
the pushforwards of the component cycles. -/
theorem map_extendCycle_apply {X W Z : Type*} [TopologicalSpace X] [TopologicalSpace W]
    [TopologicalSpace Z] [PrespectralSpace Z] {i : W → X} (G : ComponentRule i)
    (hi : Continuous i) {f : W → Z} (hf : IsSpectralMap f) (w : W → ℤ)
    (α : Function.locallyFinsupp X ℤ) {z : Z} (hcpt : IsCompact (f ⁻¹' {z})) :
    Function.locallyFinsupp.map f w hf (G.extendCycle hi α) z =
      ∑ᶠ x : X, α x * Function.locallyFinsupp.map f w hf (G.cycle x) z := by
  set t : Set W := f ⁻¹' {z} with ht
  set A : Set X := {x : X | (∃ a ∈ i '' t, a ∈ closure ({x} : Set X)) ∧ α x ≠ 0} with hA
  have hAfin : A.Finite :=
    finite_support_inter_generalizations α.locallyFiniteSupport (hcpt.image hi)
  set B : Set W := ⋃ x ∈ A, t ∩ Function.support (G.cycle x) with hB
  have hBfin : B.Finite := hAfin.biUnion fun x _ ↦
    (G.cycle x).locallyFiniteSupport.finite_inter_support_of_isCompact hcpt
  have hBt : B ⊆ t := by
    rintro b hb
    obtain ⟨x, -, hbx⟩ := Set.mem_iUnion₂.1 hb
    exact hbx.1
  have hvan : ∀ (x : X) (x' : W), x' ∈ t →
      α x * (G.cycle x x' * w x') ≠ 0 → x ∈ A ∧ x' ∈ B := by
    intro x x' hx't hne
    have hα : α x ≠ 0 := left_ne_zero_of_mul hne
    have hcy : G.cycle x x' ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hxA : x ∈ A := ⟨⟨i x', ⟨x', hx't, rfl⟩, G.mem_closure_of_apply_ne_zero x x' hcy⟩, hα⟩
    exact ⟨hxA, Set.mem_biUnion hxA ⟨hx't, hcy⟩⟩
  have key := finsum_finsum_mem_comm (fun (x : X) (x' : W) ↦ α x * (G.cycle x x' * w x')) t
    hAfin hBfin hBt hvan
  have hL : ∀ x' : W, G.extendCycle hi α x' * w x' =
      ∑ᶠ x : X, α x * (G.cycle x x' * w x') := by
    intro x'
    change (∑ᶠ x : X, α x * G.cycle x x') * w x' = _
    rw [finsum_mul]
    exact finsum_congr fun x ↦ mul_assoc _ _ _
  rw [Function.locallyFinsupp.map_apply, finsum_mem_congr rfl fun x' _ ↦ hL x', key]
  exact finsum_congr fun x ↦ by
    rw [Function.locallyFinsupp.map_apply, mul_finsum_mem]

/-! ### The extension of a pushforward -/

/-- **Extending over a pushforward.** Extending a component rule on `Y` over the pushforward of a
cycle `α` on `X` along a closed spectral map `f` with compact fibres is the coefficientwise sum,
over the points of `X`, of the component cycles of their images, weighted by `α` and by the
pushforward weight. -/
theorem extendCoeff_map_apply {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace V] [PrespectralSpace Y] {j : V → Y} (G : ComponentRule j)
    {f : X → Y} (hf : IsSpectralMap f) (hfc : IsClosedMap f) (w : X → ℤ)
    (α : Function.locallyFinsupp X ℤ) (v : V) (hcpt : IsCompact (f ⁻¹' {j v})) :
    G.extendCoeff (Function.locallyFinsupp.map f w hf α) v =
      ∑ᶠ x : X, α x * w x * G.cycle (f x) v := by
  have hfin : (Function.support fun x : X ↦ α x * w x * G.cycle (f x) v).Finite := by
    refine (finite_support_inter_generalizations α.locallyFiniteSupport hcpt).subset ?_
    intro x hx
    replace hx : α x * w x * G.cycle (f x) v ≠ 0 := hx
    have hα : α x ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hx)
    have hcy : G.cycle (f x) v ≠ 0 := right_ne_zero_of_mul hx
    have hjv : j v ∈ closure ({f x} : Set Y) := G.mem_closure_of_apply_ne_zero (f x) v hcy
    have himg : closure ({f x} : Set Y) ⊆ f '' closure ({x} : Set X) :=
      closure_minimal
        (Set.singleton_subset_iff.2 ⟨x, subset_closure (Set.mem_singleton x), rfl⟩)
        (hfc _ isClosed_closure)
    obtain ⟨a, haclos, hav⟩ := himg hjv
    exact ⟨⟨a, hav, haclos⟩, hα⟩
  have hstep : ∀ y : Y, Function.locallyFinsupp.map f w hf α y * G.cycle y v =
      ∑ᶠ x ∈ f ⁻¹' {y}, α x * w x * G.cycle (f x) v := by
    intro y
    rw [Function.locallyFinsupp.map_apply, finsum_mem_mul]
    exact finsum_mem_congr rfl fun x (hx : f x = y) ↦ by rw [hx]
  change (∑ᶠ y : Y, Function.locallyFinsupp.map f w hf α y * G.cycle y v) = _
  rw [finsum_congr hstep]
  exact finsum_finsum_mem_fiber f _ hfin

end Stacks.Chow.ComponentRule

end
