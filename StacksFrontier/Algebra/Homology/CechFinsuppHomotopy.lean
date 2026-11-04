module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# A contracting homotopy for Čech cochains with supported values

Let `ι` be a finite set of indices and let `E` be a set of *weights*. Consider families of
finitely supported functions `E →₀ M` indexed by the tuples `Fin (p + 1) → ι`, with the Čech
coboundary

`(δ b) x = ∑ₐ (-1)ᵃ b (x ∘ a.succAbove)`.

Suppose each weight `e` is either forbidden (outside `ok`) or comes with a set `N e ⊆ ι` of
indices it needs, and call a function `E →₀ M` *supported on `T ⊆ ι`* when every weight in its
support is allowed and needs only indices in `T`. If every allowed weight leaves out at least one
index, then the complex of families `c` with `c x` supported on the range of `x` is exact in every
positive degree. This is the combinatorial heart of the computation of the cohomology of a
quasi-coherent module by a Čech complex whose terms are spanned by monomials: on the weight-`e`
part one picks an index `k ∉ N e`, and the cone homotopy `(h c) x = c (k, x)` contracts that part.

## Main definitions

* `Stacks.CechFinsupp.cechCoboundary`: the Čech coboundary on families indexed by tuples.
* `Stacks.CechFinsupp.supported`: the functions whose weights are allowed and need only indices
  in a given set.

## Main results

* `Stacks.CechFinsupp.exists_cechCoboundary_eq`: **a supported Čech cocycle of positive degree
  is the coboundary of a supported cochain**, as soon as every allowed weight leaves out an index.

## Implementation notes

The homotopy depends on the weight, so it is defined weight by weight: the pivot of a weight is a
chosen index it does not need, and the homotopy collects, over the finitely many indices `k`, the
part of `c (Fin.cons k x)` carried by the weights whose pivot is `k`.
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.CechFinsupp

variable {ι E M : Type*} [AddCommGroup M]

/-- **The Čech coboundary** of a family indexed by the tuples of length `p + 1`: its value at a
tuple of length `p + 2` is the alternating sum of the values at the faces of that tuple. -/
def cechCoboundary {G : Type*} [AddCommGroup G] {p : ℕ} (b : (Fin (p + 1) → ι) → G) :
    (Fin (p + 2) → ι) → G :=
  fun x => ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) • b (x ∘ a.succAbove)

/-- **The functions supported on `T`**: every weight in the support is allowed and needs only
indices in `T`. -/
def supported (ok : Set E) (N : E → Set ι) (T : Set ι) : AddSubgroup (E →₀ M) where
  carrier := {f | ∀ e ∈ f.support, e ∈ ok ∧ N e ⊆ T}
  add_mem' {f g} hf hg e he := by
    classical
    rcases Finset.mem_union.1 (Finsupp.support_add he) with h | h
    · exact hf e h
    · exact hg e h
  zero_mem' e he := by simp at he
  neg_mem' {f} hf e he := hf e (by simpa using he)

/-- A function is supported on `T` if and only if every weight in its support is allowed and needs
only indices in `T`. -/
theorem mem_supported {ok : Set E} {N : E → Set ι} {T : Set ι} {f : E →₀ M} :
    f ∈ supported ok N T ↔ ∀ e ∈ f.support, e ∈ ok ∧ N e ⊆ T :=
  Iff.rfl

/-- The tuple `(k, x)` with `k` prepended, followed by the face map that skips a later position,
is `k` prepended to the corresponding face of `x`. -/
theorem cons_comp_succ_succAbove {p : ℕ} (k : ι) (x : Fin (p + 2) → ι) (a : Fin (p + 2)) :
    (Fin.cons k x : Fin (p + 3) → ι) ∘ (a.succ).succAbove =
      Fin.cons k (x ∘ a.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Fin.succ_succAbove_succ]

/-- The Čech coboundary at a tuple with an index prepended: the first face returns the original
tuple, and the remaining faces are the faces of the original tuple with the index prepended. -/
theorem cechCoboundary_cons {G : Type*} [AddCommGroup G] {p : ℕ} (c : (Fin (p + 2) → ι) → G)
    (k : ι) (x : Fin (p + 2) → ι) :
    cechCoboundary c (Fin.cons k x) =
      c x - ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) • c (Fin.cons k (x ∘ a.succAbove)) := by
  rw [cechCoboundary, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.succAbove_zero, Fin.cons_comp_succ,
    Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul, cons_comp_succ_succAbove]
  rw [one_zsmul, Finset.sum_neg_distrib, sub_eq_add_neg]

section Homotopy

variable [Fintype ι] [Nonempty ι] (ok : Set E) (N : E → Set ι)

open Classical in
/-- The pivot of a weight: an index the weight does not need, when there is one. -/
def pivot (e : E) : ι :=
  if h : ∃ k, k ∉ N e then h.choose else Classical.arbitrary ι

/-- If a weight leaves out some index, then its pivot is an index it does not need. -/
theorem pivot_not_mem {e : E} (h : ∃ k, k ∉ N e) : pivot N e ∉ N e := by
  rw [pivot, dif_pos h]
  exact h.choose_spec

open Classical in
/-- **The contracting homotopy**, weight by weight: the weight-`e` part of `(h c) x` is the
weight-`e` part of `c (k, x)`, `k` the pivot of `e`. -/
def homotopy {p : ℕ} (c : (Fin (p + 2) → ι) → (E →₀ M)) (x : Fin (p + 1) → ι) : E →₀ M :=
  ∑ k : ι, (c (Fin.cons k x)).filter (fun e => pivot N e = k)

/-- The value of `(h c) x` at a weight `e` is the value of `c (k, x)` at `e`, where `k` is the
pivot of `e`. -/
theorem homotopy_apply {p : ℕ} (c : (Fin (p + 2) → ι) → (E →₀ M)) (x : Fin (p + 1) → ι)
    (e : E) : homotopy N c x e = c (Fin.cons (pivot N e) x) e := by
  rw [homotopy, Finsupp.finset_sum_apply, Finset.sum_eq_single (pivot N e)]
  · rw [Finsupp.filter_apply, if_pos rfl]
  · intro k _ hk
    rw [Finsupp.filter_apply, if_neg (Ne.symm hk)]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {ok N}

/-- The homotopy of a supported family is supported, provided every allowed weight leaves out an
index. -/
theorem homotopy_mem_supported (hok : ∀ e ∈ ok, ∃ k, k ∉ N e) {p : ℕ}
    {c : (Fin (p + 2) → ι) → (E →₀ M)} (hc : ∀ x, c x ∈ supported ok N (Set.range x))
    (x : Fin (p + 1) → ι) : homotopy N c x ∈ supported ok N (Set.range x) := by
  rw [mem_supported]
  intro e he
  rw [Finsupp.mem_support_iff, homotopy_apply] at he
  obtain ⟨heok, hN⟩ := (mem_supported.1 (hc _)) e (Finsupp.mem_support_iff.2 he)
  refine ⟨heok, fun j hj => ?_⟩
  have hj' := hN hj
  rw [Fin.range_cons] at hj'
  rcases hj' with hj' | hj'
  · exact absurd (Set.mem_singleton_iff.1 hj' ▸ hj) (pivot_not_mem N (hok e heok))
  · exact hj'

/-- **The homotopy formula on cocycles**: the coboundary of the homotopy of a cocycle is the
cocycle. -/
theorem cechCoboundary_homotopy {p : ℕ} {c : (Fin (p + 2) → ι) → (E →₀ M)}
    (hcoc : ∀ y : Fin (p + 3) → ι, cechCoboundary c y = 0) (x : Fin (p + 2) → ι) :
    cechCoboundary (homotopy N c) x = c x := by
  ext e
  have h := congrArg (Finsupp.applyAddHom e) (hcoc (Fin.cons (pivot N e) x))
  simp only [cechCoboundary_cons, map_sub, map_sum, map_zsmul, Finsupp.applyAddHom_apply,
    map_zero] at h
  show (Finsupp.applyAddHom e) (cechCoboundary (homotopy N c) x) =
    (Finsupp.applyAddHom e) (c x)
  rw [cechCoboundary]
  simp only [map_sum, map_zsmul, Finsupp.applyAddHom_apply, homotopy_apply]
  exact (sub_eq_zero.1 h).symm

end Homotopy

/-- **Exactness in positive degrees.** If every allowed weight leaves out at least one of the
finitely many indices, a Čech cocycle of positive degree with supported values is the coboundary
of a cochain with supported values. -/
theorem exists_cechCoboundary_eq [Finite ι] {ok : Set E} {N : E → Set ι}
    (hok : ∀ e ∈ ok, ∃ k, k ∉ N e) {p : ℕ} (c : (Fin (p + 2) → ι) → (E →₀ M))
    (hc : ∀ x, c x ∈ supported ok N (Set.range x))
    (hcoc : ∀ y : Fin (p + 3) → ι, cechCoboundary c y = 0) :
    ∃ b : (Fin (p + 1) → ι) → (E →₀ M),
      (∀ x, b x ∈ supported ok N (Set.range x)) ∧ ∀ x, cechCoboundary b x = c x := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ => 0, fun _ => zero_mem _, fun x => isEmptyElim (x 0)⟩
  · exact ⟨homotopy N c, homotopy_mem_supported hok hc, cechCoboundary_homotopy hcoc⟩

end Stacks.CechFinsupp

end
