module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Monotone.Basic
public import Mathlib.SetTheory.Cardinal.NatCard
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Codimension estimates and avoiding a finite union of subspaces

This file collects four elementary facts of linear algebra and combinatorics which are used to
run finiteness arguments by descending induction on the codimension of a subspace.

The first is a codimension bound: a linear map from a vector space `A` into the space of linear
maps `M →ₗ[k] N`, with `M` and `N` finite-dimensional, has a kernel of codimension at most
`finrank M * finrank N`, simply because its image is a subspace of `M →ₗ[k] N`. The second is
the dimension inequality which, read as a statement about codimensions, says that the
codimension of `V ⊓ W` inside `V` is at least the codimension of `W` inside `A` minus the
codimension of `V` inside `A`.

The third is the key avoidance statement: a finite-dimensional vector space is not the union of
`r` subspaces each of codimension at least `r`. Over an infinite field the bound is not needed
(a vector space over an infinite field is never a finite union of proper subspaces), but over a
finite field it is essential: the plane over `𝔽₂` is the union of its three lines, each of
codimension `1 < 3`. The hypothesis `t.card + finrank (W i) ≤ finrank A` is exactly what makes
the conclusion hold uniformly in the field.

The fourth is the observation that a non-increasing sequence of natural numbers is eventually
constant, which is what terminates such a descending induction.

## Main results

* `Stacks.LinearAlgebra.finrank_quotient_ker_le`: the kernel of a linear map into `M →ₗ[k] N`
  has codimension at most `finrank k M * finrank k N`.
* `Stacks.LinearAlgebra.finrank_add_finrank_le_finrank_add_finrank_inf`: the subadditivity
  inequality `finrank V + finrank W ≤ finrank A + finrank (V ⊓ W)`, equivalently
  superadditivity of codimension.
* `Stacks.LinearAlgebra.exists_notMem_biUnion_of_infinite`: over an infinite field, a vector
  space is not a finite union of proper subspaces.
* `Stacks.LinearAlgebra.exists_notMem_biUnion_of_finite`: the same conclusion over a finite
  field, under the codimension hypothesis, by counting.
* `Stacks.LinearAlgebra.exists_notMem_biUnion`: the uniform statement, for an arbitrary field.
* `Stacks.LinearAlgebra.exists_forall_eq_of_antitone`: a non-increasing `ℕ`-valued sequence is
  eventually constant.

## Implementation notes

The avoidance statement is proved by splitting on whether the field is finite, the two cases
having nothing in common.

Over an infinite field the proof is an induction on the finite index set. Given a vector `v`
avoiding the subspaces indexed by `s` and a further proper subspace `W j`, one picks `u ∉ W j`
and moves along the line `v + c • u`. For an index `i ∈ s` the set of parameters `c` with
`v + c • u ∈ W i` has at most one element: two such parameters would put `u`, hence also `v`,
into `W i`. So only finitely many parameters are forbidden, together with `c = 0`, and an
infinite field has one to spare. This is where the proof needs no codimension hypothesis, only
that each subspace is proper.

Over a finite field the proof is a count with `Nat.card`, through `Module.natCard_eq_pow_finrank`:
writing `q = Nat.card k`, each `W i` has at most `q ^ (finrank A - t.card)` elements, so the
union has at most `t.card * q ^ (finrank A - t.card)` elements, and `t.card < q ^ t.card` because
`q ≥ 2`. A `Fintype A` instance is produced from `Finite A` inside the proof in order to use
`Finset.card_biUnion_le` for the union bound; this is harmless since the statement is a
proposition.

Deducing the uniform statement from the infinite-field case uses the codimension hypothesis only
to see that each `W i` is proper, via `finrank_top`.
-/

@[expose] public section

namespace Stacks.LinearAlgebra

open Module

/-- The kernel of a linear map `Φ : A →ₗ[k] (M →ₗ[k] N)` into the space of linear maps between
two finite-dimensional vector spaces has codimension at most `finrank k M * finrank k N`: the
quotient by the kernel is isomorphic to the range of `Φ`, a subspace of `M →ₗ[k] N`. -/
public theorem finrank_quotient_ker_le (k A M N : Type*) [Field k] [AddCommGroup A] [Module k A]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [FiniteDimensional k M] [FiniteDimensional k N] (Φ : A →ₗ[k] (M →ₗ[k] N)) :
    Module.finrank k (A ⧸ LinearMap.ker Φ) ≤ Module.finrank k M * Module.finrank k N := by
  rw [(LinearMap.quotKerEquivRange Φ).finrank_eq, ← Module.finrank_linearMap k k M N]
  exact Submodule.finrank_le _

/-- Subadditivity of codimension, in the form of a dimension inequality: for subspaces `V` and
`W` of a finite-dimensional vector space `A`,
`finrank V + finrank W ≤ finrank A + finrank (V ⊓ W)`. Rearranged, the codimension of `V ⊓ W`
inside `V` is at least the codimension of `W` inside `A` minus the codimension of `V` inside `A`.
This is the dimension formula for `V ⊔ W` together with `finrank (V ⊔ W) ≤ finrank A`. -/
public theorem finrank_add_finrank_le_finrank_add_finrank_inf {k A : Type*} [Field k]
    [AddCommGroup A] [Module k A] [FiniteDimensional k A] (V W : Submodule k A) :
    Module.finrank k V + Module.finrank k W ≤
      Module.finrank k A + Module.finrank k (V ⊓ W : Submodule k A) := by
  rw [← Submodule.finrank_sup_add_finrank_inf_eq V W]
  exact Nat.add_le_add_right (Submodule.finrank_le _) _

/-- A line through a vector outside a subspace meets that subspace at most once: if `v ∉ W`,
there is at most one scalar `c` with `v + c • u ∈ W`. -/
public theorem subsingleton_setOf_add_smul_mem {k A : Type*} [Field k] [AddCommGroup A]
    [Module k A] (W : Submodule k A) {v u : A} (hv : v ∉ W) :
    {c : k | v + c • u ∈ W}.Subsingleton := by
  intro c₁ hc₁ c₂ hc₂
  by_contra hne
  refine absurd ?_ hv
  have hd : (c₁ - c₂) • u ∈ W := by simpa [sub_smul] using W.sub_mem hc₁ hc₂
  have hui : u ∈ W := by
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne)] using W.smul_mem (c₁ - c₂)⁻¹ hd
  simpa using W.sub_mem hc₁ (W.smul_mem c₁ hui)

/-- If a subspace contains `v` and `v + c • u` for some nonzero scalar `c`, it contains `u`. -/
public theorem mem_of_add_smul_mem {k A : Type*} [Field k] [AddCommGroup A] [Module k A]
    (W : Submodule k A) {v u : A} {c : k} (hc : c ≠ 0) (hv : v ∈ W) (h : v + c • u ∈ W) :
    u ∈ W := by
  have hcu : c • u ∈ W := by simpa using W.sub_mem h hv
  simpa [smul_smul, inv_mul_cancel₀ hc] using W.smul_mem c⁻¹ hcu

/-- A vector space over an infinite field is not the union of finitely many proper subspaces:
given a finite family `W` of subspaces indexed by `t`, none of them the whole space, some vector
lies outside all of them. No finiteness assumption on the ambient space is needed. -/
@[sga "3 V 4.2" "partial"]
public theorem exists_notMem_biUnion_of_infinite {k A : Type*} [Field k] [AddCommGroup A]
    [Module k A] [Infinite k] {ι : Type*} (t : Finset ι) (W : ι → Submodule k A)
    (h : ∀ i ∈ t, W i ≠ ⊤) : ∃ v : A, ∀ i ∈ t, v ∉ W i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
      obtain ⟨v, hv⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      by_cases hvj : v ∈ W j
      · obtain ⟨u, hu⟩ : ∃ u, u ∉ W j := by
          by_contra hc
          push Not at hc
          exact h j (Finset.mem_insert_self j s) (eq_top_iff.2 fun x _ => hc x)
        have hfin : ({0} ∪ ⋃ i ∈ (s : Set ι), {c : k | v + c • u ∈ W i}).Finite :=
          (Set.finite_singleton 0).union (s.finite_toSet.biUnion fun i hi =>
            (subsingleton_setOf_add_smul_mem (W i) (hv i hi)).finite)
        obtain ⟨c, hc⟩ := hfin.infinite_compl.nonempty
        rw [Set.mem_compl_iff, Set.mem_union] at hc
        push Not at hc
        obtain ⟨hc0, hcs⟩ := hc
        have hc0' : c ≠ 0 := fun h0 => hc0 (by simp [h0])
        refine ⟨v + c • u, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi'
        · exact fun hmem => hu (mem_of_add_smul_mem _ hc0' hvj hmem)
        · exact fun hmem => hcs (Set.mem_biUnion hi' hmem)
      · refine ⟨v, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi'
        · exact hvj
        · exact hv i hi'

/-- A bound used for counting a union of subspaces over a finite field: for `2 ≤ q` and
`n ≤ m`, the product `n * q ^ (m - n)` is strictly smaller than `q ^ m`. -/
public theorem mul_pow_sub_lt_pow {q m n : ℕ} (hq : 2 ≤ q) (hn : n ≤ m) :
    n * q ^ (m - n) < q ^ m :=
  calc n * q ^ (m - n)
      < q ^ n * q ^ (m - n) :=
        Nat.mul_lt_mul_of_lt_of_le
          (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hq n)) le_rfl (pow_pos (by omega) _)
    _ = q ^ m := by rw [← pow_add, Nat.add_sub_cancel' hn]

/-- Over a finite field, a finite-dimensional vector space is not the union of a finite family
`W` of subspaces each of codimension at least the size of the index set `t`. The proof is a
count: each `W i` has at most `(Nat.card k) ^ (finrank k A - t.card)` elements, and
`t.card < (Nat.card k) ^ t.card`, so the union is strictly smaller than the whole space. -/
public theorem exists_notMem_biUnion_of_finite {k A : Type*} [Field k] [AddCommGroup A]
    [Module k A] [FiniteDimensional k A] [Finite k] {ι : Type*} (t : Finset ι)
    (W : ι → Submodule k A)
    (hcodim : ∀ i ∈ t, t.card + Module.finrank k (W i) ≤ Module.finrank k A) :
    ∃ v : A, ∀ i ∈ t, v ∉ W i := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact ⟨0, by simp⟩
  have : Finite A := Module.finite_of_finite k
  let _ : Fintype A := Fintype.ofFinite A
  have hq : 2 ≤ Nat.card k := Finite.one_lt_card
  have hqpos : 0 < Nat.card k := by omega
  have hcn : t.card ≤ Module.finrank k A :=
    le_trans (Nat.le_add_right _ _) (hcodim i₀ hi₀)
  have hcardA : Fintype.card A = Nat.card k ^ Module.finrank k A := by
    rw [← Nat.card_eq_fintype_card]
    exact Module.natCard_eq_pow_finrank (K := k) (V := A)
  have hcardW : ∀ i, ((W i : Set A).toFinset).card = Nat.card k ^ Module.finrank k (W i) := by
    intro i
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact Module.natCard_eq_pow_finrank (K := k) (V := (W i))
  have h1 : (t.biUnion fun i => (W i : Set A).toFinset).card ≤
      ∑ i ∈ t, ((W i : Set A).toFinset).card := Finset.card_biUnion_le
  have h2 : ∀ i ∈ t, ((W i : Set A).toFinset).card ≤
      Nat.card k ^ (Module.finrank k A - t.card) := by
    intro i hi
    rw [hcardW i]
    have := hcodim i hi
    exact Nat.pow_le_pow_right hqpos (by omega)
  have h3 : ∑ i ∈ t, ((W i : Set A).toFinset).card ≤
      t.card * Nat.card k ^ (Module.finrank k A - t.card) := by
    simpa [smul_eq_mul] using Finset.sum_le_card_nsmul t _ _ h2
  have h4 := mul_pow_sub_lt_pow (q := Nat.card k) hq hcn
  have hcard : (t.biUnion fun i => (W i : Set A).toFinset).card < Fintype.card A := by omega
  obtain ⟨v, hv⟩ : ∃ v : A, v ∉ t.biUnion fun i => (W i : Set A).toFinset := by
    by_contra hcon
    push Not at hcon
    rw [Finset.eq_univ_iff_forall.2 hcon, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  refine ⟨v, fun i hi hmem => hv (Finset.mem_biUnion.2 ⟨i, hi, ?_⟩)⟩
  simpa using hmem

/-- A finite-dimensional vector space over an arbitrary field is not the union of a finite
family `W` of subspaces each of codimension at least the size `t.card` of the index set: some
vector avoids all of them.

The codimension hypothesis cannot be dropped over a finite field, where the plane over `𝔽₂` is
the union of its three lines; and `t.card ≤` codimension is the bound that makes the statement
true over every field. -/
public theorem exists_notMem_biUnion (k A : Type*) [Field k] [AddCommGroup A] [Module k A]
    [FiniteDimensional k A] {ι : Type*} (t : Finset ι) (W : ι → Submodule k A)
    (hcodim : ∀ i ∈ t, t.card + Module.finrank k (W i) ≤ Module.finrank k A) :
    ∃ v : A, ∀ i ∈ t, v ∉ W i := by
  rcases finite_or_infinite k with hk | hk
  · exact exists_notMem_biUnion_of_finite t W hcodim
  · rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
    · exact ⟨0, by simp⟩
    refine exists_notMem_biUnion_of_infinite t W fun i hi htop => ?_
    have h1 : Module.finrank k (W i) = Module.finrank k A := by rw [htop, finrank_top]
    have h2 := hcodim i hi
    have h3 : 0 < t.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
    omega

/-- A non-increasing sequence of natural numbers is eventually constant: it agrees with the
minimum of its range from the first index where that minimum is attained onwards. -/
public theorem exists_forall_eq_of_antitone (a : ℕ → ℕ) (ha : ∀ n, a (n + 1) ≤ a n) :
    ∃ J N, ∀ j, J ≤ j → a j = N := by
  obtain ⟨J, hJ⟩ : ∃ J, a J = sInf (Set.range a) := Nat.sInf_mem (Set.range_nonempty a)
  refine ⟨J, sInf (Set.range a), fun j hj => le_antisymm ?_ (Nat.sInf_le ⟨j, rfl⟩)⟩
  rw [← hJ]
  exact antitone_nat_of_succ_le ha hj

end Stacks.LinearAlgebra

end
