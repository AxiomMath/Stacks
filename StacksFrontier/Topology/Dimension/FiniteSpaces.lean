module

public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite spaces of prescribed Krull dimension (Stacks 0057)

Stacks 0057 exhibits, for each `n`, a topological space with `n + 1` points and Krull
dimension `n`. For `n = 1` this is the two-point space `{s, η}` whose open sets are `∅`,
`{η}` and `{s, η}`; in general one takes a chain of `n + 1` points in which the open sets
are the upper sets.

That topology is Mathlib's `Topology.upperSet`, the topology on a preorder whose open sets
are exactly the upper sets, so the space of the tag is `Fin (n + 1)` carrying
`Topology.upperSet`. Everything then follows from the Mathlib API of the mixin class
`Topology.IsUpperSet`, which is the assertion that a given topology is that one.

The dimension computation is an order isomorphism. In the upper-set topology on a finite
linear order the closed sets are the lower sets, so the irreducible closed subsets are
precisely the intervals `Set.Iic k = closure {k}`, and `k ↦ Set.Iic k` is an order
isomorphism `X ≃o TopologicalSpace.IrreducibleCloseds X`. Hence the topological Krull
dimension of `X` — the order-theoretic Krull dimension of its poset of irreducible closed
subsets — is the order-theoretic Krull dimension of `X` itself, which for `Fin (n + 1)` is
`n` (`Order.krullDim_fin`).
-/

@[expose] public section

open TopologicalSpace

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type*} [TopologicalSpace X] [LinearOrder X] [Topology.IsUpperSet X]

/-- In the upper-set topology, `Set.Iic k` is an irreducible closed subset: it is the closure
of the singleton `{k}`. -/
def iic (k : X) : IrreducibleCloseds X where
  carrier := Set.Iic k
  isIrreducible' := by
    rw [← Topology.IsUpperSet.closure_singleton (a := k)]
    exact isIrreducible_singleton.closure
  isClosed' := Topology.IsUpperSet.isClosed_iff_isLower.mpr (isLowerSet_Iic k)

@[simp] lemma coe_iic (k : X) : (iic k : Set X) = Set.Iic k := rfl

/-- `k ↦ Set.Iic k` is strictly monotone. -/
lemma iic_strictMono : StrictMono (iic (X := X)) := fun k k' h => by
  rw [← SetLike.coe_ssubset_coe, coe_iic, coe_iic]
  exact ⟨Set.Iic_subset_Iic.mpr h.le, fun hle => h.not_ge (hle (le_refl k'))⟩

/-- In the upper-set topology on a finite linear order, every irreducible closed subset is an
interval `Set.Iic k`, namely for `k` its greatest element. -/
lemma exists_eq_iic [Finite X] (A : IrreducibleCloseds X) : ∃ k : X, A = iic k := by
  classical
  let _ := Fintype.ofFinite X
  have hlower : IsLowerSet (A : Set X) :=
    Topology.IsUpperSet.isClosed_iff_isLower.mp A.isClosed
  obtain ⟨x, hx⟩ := A.isIrreducible.nonempty
  have hne : (A : Set X).toFinset.Nonempty := ⟨x, Set.mem_toFinset.mpr hx⟩
  refine ⟨(A : Set X).toFinset.max' hne, SetLike.coe_injective ?_⟩
  rw [coe_iic]
  refine Set.eq_of_subset_of_subset (fun i hi => ?_) (fun i hi => ?_)
  · exact Finset.le_max' _ i (Set.mem_toFinset.mpr hi)
  · exact hlower hi (Set.mem_toFinset.mp ((A : Set X).toFinset.max'_mem hne))

/-- In the upper-set topology on a finite linear order, `k ↦ Set.Iic k` is an order
isomorphism onto the poset of irreducible closed subsets. -/
noncomputable def iicOrderIso (X : Type*) [TopologicalSpace X] [LinearOrder X] [Finite X]
    [Topology.IsUpperSet X] : X ≃o IrreducibleCloseds X :=
  StrictMono.orderIsoOfSurjective iic iic_strictMono
    fun A => (exists_eq_iic A).imp fun _ h => h.symm

end TopologicalSpace.IrreducibleCloseds

/-- For the upper-set topology on a finite linear order, the topological Krull dimension is the
order-theoretic Krull dimension of the order itself. -/
theorem topologicalKrullDim_eq_krullDim_of_isUpperSet (X : Type*) [TopologicalSpace X]
    [LinearOrder X] [Finite X] [Topology.IsUpperSet X] :
    topologicalKrullDim X = Order.krullDim X := by
  rw [topologicalKrullDim]
  exact (Order.krullDim_eq_of_orderIso (IrreducibleCloseds.iicOrderIso X)).symm

/-- The Krull dimension of the linear order `Fin (n + 1)` is `n`: the identity is a strictly
increasing series of length `n`, and no series can be longer than the cardinality allows. -/
theorem Order.krullDim_fin (n : ℕ) : Order.krullDim (Fin (n + 1)) = (n : WithBot ℕ∞) := by
  refine le_antisymm (iSup_le fun p => ?_)
    (Order.le_krullDim_iff.mpr ⟨⟨n, id, fun i => i.castSucc_lt_succ⟩, rfl⟩)
  have hlt : p.length < n + 1 := by simpa using p.length_lt_card
  exact Nat.mono_cast (Nat.lt_succ_iff.mp hlt)

/-- **Stacks 0057.** The two-point example: with the upper-set topology on `Fin 2` (so `s = 0`
and `η = 1`), the open sets are exactly `∅`, `{η}` and the whole space. -/
@[stacks 0057]
theorem isOpen_upperSet_fin_two_iff (s : Set (Fin 2)) :
    @IsOpen (Fin 2) (Topology.upperSet (Fin 2)) s ↔
      s = ∅ ∨ s = {(1 : Fin 2)} ∨ s = Set.univ := by
  rw [@Topology.IsUpperSet.isOpen_iff_isUpperSet (Fin 2) _ (Topology.upperSet (Fin 2)) _ s]
  refine ⟨fun h => ?_, ?_⟩
  · by_cases h0 : (0 : Fin 2) ∈ s
    · exact Or.inr (Or.inr (Set.eq_univ_of_forall fun i => by
        fin_cases i
        · exact h0
        · exact h (by decide) h0))
    · by_cases h1 : (1 : Fin 2) ∈ s
      · refine Or.inr (Or.inl (Set.eq_singleton_iff_unique_mem.mpr ⟨h1, fun x hx => ?_⟩))
        fin_cases x
        · exact absurd hx h0
        · rfl
      · exact Or.inl (Set.eq_empty_iff_forall_notMem.mpr fun x hx => by
          fin_cases x
          · exact h0 hx
          · exact h1 hx)
  · rintro (rfl | rfl | rfl)
    · exact isUpperSet_empty
    · intro a b hab ha
      simp only [Set.mem_singleton_iff] at ha ⊢
      subst ha
      exact Fin.le_antisymm (by omega) hab
    · exact isUpperSet_univ

/-- **Stacks 0057.** For every `n : ℕ` there is a topological space with `n + 1` points whose
Krull dimension is `n`, namely `Fin (n + 1)` with the upper-set topology. -/
@[stacks 0057]
theorem exists_finite_space_of_krullDim (n : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : Fintype X),
      Fintype.card X = n + 1 ∧ topologicalKrullDim X = (n : WithBot ℕ∞) :=
  ⟨Fin (n + 1), Topology.upperSet (Fin (n + 1)), inferInstance, Fintype.card_fin _, by
    rw [topologicalKrullDim_eq_krullDim_of_isUpperSet, Order.krullDim_fin]⟩
