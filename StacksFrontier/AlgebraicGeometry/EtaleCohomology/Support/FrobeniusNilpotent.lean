module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The nilpotent part of a Frobenius-semilinear endomorphism

Let `k` be a field of characteristic `p` and let `V` be a finite-dimensional `k`-vector space.
A `p`-power Frobenius-semilinear endomorphism `F` of `V` has an invariant subspace `N` on which
`F` is nilpotent, such that the induced endomorphism of `V / N` is injective. On `N` the map
`F - 1` is an additive automorphism.

Splitting off this nilpotent part is the first step in the Artin–Schreier analysis of
`F - 1`: on the quotient `F` is injective, where the fibre count of
`AlgebraicGeometry.natCard_fiber_sub_id_eq` applies.

## Main results

* `AlgebraicGeometry.exists_invariant_subspace_nilpotent_quotient_injective` — the invariant
  nilpotent subspace, together with the injectivity of the induced map on the quotient and the
  additive automorphism `F - 1` of the subspace.

## Implementation notes

The subspace is the stable value of the increasing chain of iterated kernels of `F`, which
stabilizes because `V` is finite-dimensional. Injectivity of the induced map on the quotient is
expressed by saying that an element whose image under `F` lies in the subspace already lies in
it, and the automorphism of the subspace is recorded as an additive equivalence whose
underlying map is `F - 1`; the inverse is the finite telescoping sum `-∑ F^i`.

Algebraic closedness of `k` is not assumed: the stabilization argument uses only finite
dimensionality and Frobenius semilinearity.

## References

* [Stacks Project, Tag 0A3L](https://stacks.math.columbia.edu/tag/0A3L)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- An increasing chain of subspaces of a finite-dimensional space is eventually constant. -/
private lemma exists_stable_submodule_chain
    (k : Type u) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (K : ℕ → Submodule k V)
    (hle : ∀ n, K n ≤ K (n + 1)) : ∃ m, K m = K (m + 1) := by
  by_contra hn
  push Not at hn
  have hbound (n : ℕ) : n ≤ Module.finrank k (K n) := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      exact ih.trans_lt (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hle n) (hn n)))
  exact Nat.not_succ_le_self _
    ((hbound (Module.finrank k V + 1)).trans (Submodule.finrank_le _))

/-- Restrict an additive endomorphism to a subspace it preserves. -/
private def submoduleRestrictAddMonoidHom
    (k : Type u) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    (S : Submodule k V) (f : V →+ V) (hf : ∀ x, x ∈ S → f x ∈ S) :
    S →+ S :=
  AddMonoidHom.mk' (M := ↥S) (G := ↥S)
    (fun x => ⟨f x, hf x x.property⟩) fun x y => Subtype.ext (map_add f (x : V) y)

/-- The additive endomorphism `f - 1` of a subspace. -/
private def subIdAddMonoidHom
    (k : Type u) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    (S : Submodule k V) (f : S →+ S) : S →+ S :=
  AddMonoidHom.mk' (M := S) (G := S) (fun x => f x - x) (by
    intro x y
    rw [map_add]
    abel)

/-- The kernel of the `n`-fold iterate of a Frobenius-semilinear endomorphism. -/
private def frobeniusKernelSubmodule
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V]
    (F : V →ₛₗ[frobenius k p] V) (n : ℕ) : Submodule k V :=
  Nat.rec ⊥ (fun _ S => S.comap F) n

/-- A Frobenius-semilinear endomorphism of a finite-dimensional vector space admits an
invariant nilpotent subspace on which `F - 1` is invertible, and the induced map on the quotient
is injective. -/
public theorem exists_invariant_subspace_nilpotent_quotient_injective
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : V →ₛₗ[frobenius k p] V) :
    ∃ (N : Submodule k V),
      (∀ x ∈ N, F x ∈ N) ∧
      (∃ m : ℕ, ∀ x ∈ N, (F^[m]) x = 0) ∧
      (∀ x : V, F x ∈ N → x ∈ N) ∧
    ∃ e : N ≃+ N, ∀ x : N, (e x : V) = F x - x := by
  have hmem : ∀ n x, x ∈ frobeniusKernelSubmodule k p V F n ↔ (F^[n]) x = 0 := by
    intro n
    induction n with
    | zero => simp [frobeniusKernelSubmodule]
    | succ n ih =>
      intro x
      rw [show frobeniusKernelSubmodule k p V F n.succ =
        (frobeniusKernelSubmodule k p V F n).comap F by rfl,
        Submodule.mem_comap, ih, Function.iterate_succ_apply]
  have hle : ∀ n, frobeniusKernelSubmodule k p V F n ≤
      frobeniusKernelSubmodule k p V F (n + 1) := by
    intro n
    induction n with
    | zero => exact bot_le
    | succ n ih => exact Submodule.comap_mono ih
  obtain ⟨m, hm⟩ := exists_stable_submodule_chain k V (frobeniusKernelSubmodule k p V F) hle
  have hmem_succ : ∀ x, x ∈ frobeniusKernelSubmodule k p V F m ↔
      F x ∈ frobeniusKernelSubmodule k p V F m := fun x => by
    conv_lhs => rw [hm]
    exact Submodule.mem_comap
  refine ⟨frobeniusKernelSubmodule k p V F m, fun x hx => (hmem_succ x).mp hx,
    ⟨m, fun x hx => (hmem m x).mp hx⟩, fun x hx => (hmem_succ x).mpr hx, ?_⟩
  let A : ↥(frobeniusKernelSubmodule k p V F m) →+
      ↥(frobeniusKernelSubmodule k p V F m) :=
    submoduleRestrictAddMonoidHom k V (frobeniusKernelSubmodule k p V F m)
      F.toAddMonoidHom fun x hx => (hmem_succ x).mp hx
  let G : ↥(frobeniusKernelSubmodule k p V F m) →+
      ↥(frobeniusKernelSubmodule k p V F m) :=
    subIdAddMonoidHom k V (frobeniusKernelSubmodule k p V F m) A
  have hA_iter : ∀ n (x : ↥(frobeniusKernelSubmodule k p V F m)),
      ((A^[n]) x : V) = (F^[n]) x := by
    intro n
    induction n with
    | zero => exact fun _ => rfl
    | succ n ih => exact fun x => ih (A x)
  have hA : ∀ x : ↥(frobeniusKernelSubmodule k p V F m), (A^[m]) x = 0 := fun x =>
    Subtype.ext ((hA_iter m x).trans ((hmem m x).mp x.property))
  have htel : ∀ (n : ℕ) (x : ↥(frobeniusKernelSubmodule k p V F m)),
      G (-∑ i ∈ Finset.range n, (A^[i]) x) = x - (A^[n]) x := by
    intro n
    induction n with
    | zero => intro x; simp [G]
    | succ n ih =>
      intro x
      rw [Finset.sum_range_succ]
      simp only [Function.iterate_succ_apply]
      rw [neg_add, map_add, ih, map_neg]
      simp only [subIdAddMonoidHom, AddMonoidHom.mk'_apply, neg_sub, sub_add_sub_cancel,
        sub_right_inj, G]
      rw [← Function.iterate_succ_apply' (fun y => A y) n x,
        ← Function.iterate_succ_apply (fun y => A y) n x]
  have hG_injective : Function.Injective G := by
    refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    change A z - z = 0 at hz
    exact (Function.iterate_fixed (sub_eq_zero.mp hz) m).symm.trans (hA z)
  have hG_surjective : Function.Surjective G :=
    fun x => ⟨-∑ i ∈ Finset.range m, (A^[i]) x, by simp [htel, hA]⟩
  exact ⟨AddEquiv.ofBijective G ⟨hG_injective, hG_surjective⟩, fun _ => rfl⟩

end AlgebraicGeometry
