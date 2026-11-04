module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.LocallyFinsupp

/-!
# Locally finite sums along a proper map

The projection formula of Stacks 02SU compares two locally finite sums: the proper pushforward of
a cycle built coefficientwise from the integral components of `X`, and a cycle built
coefficientwise from the integral components of `Y` out of the proper pushforward. Both are
double sums, and matching them term by term is an exchange of the order of summation together
with a reindexing of a sum over `Y` as a sum over the fibres of `X ⟶ Y`.

This file collects the three facts that make those manipulations legitimate, at the level of
topological spaces and `Function.locallyFinsupp`:

* a cycle has only finitely many components passing through a fixed *compact* set
  (`Stacks.Chow.finite_support_inter_generalizations`) — the reason both double sums have finite
  support, and the only place properness enters;
* the exchange of two `finsum`s whose joint support is contained in a product of finite sets
  (`Stacks.Chow.finsum_finsum_mem_comm`);
* a sum over a space, broken up over the fibres of a map
  (`Stacks.Chow.finsum_finsum_mem_fiber`).

## Main results

* `Stacks.Chow.finite_support_inter_generalizations` — the points of the support of a locally
  finitely supported function that have a point of a given compact set in their closure form a
  finite set.
* `Stacks.Chow.finsum_finsum_mem_comm` — exchanging a `finsum` over a type with a `finsum` over a
  set, under a joint support bound.
* `Stacks.Chow.finsum_finsum_mem_fiber` — a finitely supported sum over a type is the sum over
  the fibres of any map out of it.

## Implementation notes

The first result is the topological heart of the matter. A cycle's support is only *locally*
finite, so the family of integral closed subschemes it is supported on is infinite in general;
but if `W` is a component of the cycle whose closure meets a compact set `K`, then `W` meets
every open containing `K`, and a finite subcover of `K` by opens meeting the support in finitely
many points bounds the number of such `W`. This is used twice in Stacks 02SU, once for the fibre
`p⁻¹(y)` of the proper morphism and once for its image.

## References

* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
-/

@[expose] public noncomputable section

open Set Topology

namespace Stacks.Chow

/-! ### Components of a cycle meeting a compact set -/

/-- A locally finitely supported function has only finitely many points in its support whose
closure meets a given compact set.

In the language of cycles: only finitely many of the integral closed subschemes a cycle is
supported on pass through a fixed compact set. A point `x` of the support whose closure contains
some `a ∈ K` lies in every open containing `a`, because opens are stable under generalization; so
a finite subcover of `K` by opens meeting the support finitely bounds the possibilities for
`x`. -/
theorem finite_support_inter_generalizations {X : Type*} [TopologicalSpace X] {M : Type*} [Zero M]
    {c : X → M} (hc : LocallyFiniteSupport c) {K : Set X} (hK : IsCompact K) :
    {x : X | (∃ a ∈ K, a ∈ closure ({x} : Set X)) ∧ c x ≠ 0}.Finite := by
  choose t ht hfin using hc
  obtain ⟨F, -, hcover⟩ := hK.elim_nhds_subcover (fun a ↦ interior (t a))
    fun a _ ↦ isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 (ht a))
  refine Set.Finite.subset (F.finite_toSet.biUnion fun a _ ↦ hfin a) ?_
  rintro x ⟨⟨a, haK, hax⟩, hcx⟩
  obtain ⟨b, hbF, hab⟩ := Set.mem_iUnion₂.1 (hcover haK)
  exact Set.mem_biUnion hbF
    ⟨interior_subset ((specializes_iff_mem_closure.2 hax).mem_open isOpen_interior hab), hcx⟩

/-! ### Exchanging two locally finite sums -/

/-- Exchanging the order of a sum over a set with a sum over a type, when the terms vanish
outside a product of two finite sets. -/
theorem finsum_finsum_mem_comm {α β M : Type*} [AddCommMonoid M] (F : α → β → M) (t : Set β)
    {A : Set α} {B : Set β} (hA : A.Finite) (hB : B.Finite) (hBt : B ⊆ t)
    (hvan : ∀ (a : α) (b : β), b ∈ t → F a b ≠ 0 → a ∈ A ∧ b ∈ B) :
    (∑ᶠ b ∈ t, ∑ᶠ a : α, F a b) = ∑ᶠ a : α, ∑ᶠ b ∈ t, F a b := by
  have h1 : ∀ b ∈ t, (∑ᶠ a : α, F a b) = ∑ᶠ a ∈ A, F a b := fun b hb ↦
    (finsum_mem_univ fun a ↦ F a b).symm.trans
      (finsum_mem_inter_support_eq' (fun a ↦ F a b) Set.univ A fun a ha ↦
        ⟨fun _ ↦ (hvan a b hb ha).1, fun _ ↦ Set.mem_univ a⟩)
  have h2 : (∑ᶠ b ∈ t, ∑ᶠ a ∈ A, F a b) = ∑ᶠ b ∈ B, ∑ᶠ a ∈ A, F a b := by
    refine finsum_mem_inter_support_eq' (fun b ↦ ∑ᶠ a ∈ A, F a b) t B fun b hb ↦
      ⟨fun hbt ↦ ?_, fun hbB ↦ hBt hbB⟩
    obtain ⟨a, -, hane⟩ := exists_ne_zero_of_finsum_mem_ne_zero hb
    exact (hvan a b hbt hane).2
  have h4 : ∀ a ∈ A, (∑ᶠ b ∈ B, F a b) = ∑ᶠ b ∈ t, F a b := fun a _ ↦
    finsum_mem_inter_support_eq' _ _ _ fun b hb ↦
      ⟨fun h ↦ hBt h, fun h ↦ (hvan a b h hb).2⟩
  have h5 : (∑ᶠ a ∈ A, ∑ᶠ b ∈ t, F a b) = ∑ᶠ a : α, ∑ᶠ b ∈ t, F a b := by
    refine (finsum_mem_inter_support_eq' (fun a ↦ ∑ᶠ b ∈ t, F a b) A Set.univ fun a ha ↦
      ⟨fun _ ↦ Set.mem_univ a, fun _ ↦ ?_⟩).trans (finsum_mem_univ _)
    obtain ⟨b, hbt, hbne⟩ := exists_ne_zero_of_finsum_mem_ne_zero ha
    exact (hvan a b hbt hbne).1
  rw [finsum_mem_congr rfl h1, h2, ← finsum_mem_comm F hA hB, finsum_mem_congr rfl h4, h5]

/-! ### Breaking a sum up over the fibres of a map -/

/-- A finitely supported sum over a type is the sum, over the target of any map out of it, of the
partial sums over the fibres of that map. -/
theorem finsum_finsum_mem_fiber {α β M : Type*} [AddCommMonoid M] (f : α → β) (G : α → M)
    (hG : (Function.support G).Finite) :
    (∑ᶠ b : β, ∑ᶠ a ∈ f ⁻¹' {b}, G a) = ∑ᶠ a : α, G a := by
  classical
  have key : ∀ b : β, (∑ᶠ a ∈ f ⁻¹' {b}, G a) = ∑ a ∈ hG.toFinset with f a = b, G a := by
    intro b
    refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter,
      Set.mem_ofPred_eq, Set.Finite.mem_toFinset, Function.mem_support]
    tauto
  rw [finsum_congr key, finsum_sum_filter f hG.toFinset G, ← finsum_eq_sum G hG]

end Stacks.Chow

end
