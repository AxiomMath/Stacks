module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Truncating a graded direct sum with a degree-raising action

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring and let `⨁_{n ∈ ℤ} V n` be a
`ℤ`-graded abelian group carrying an `S`-module structure whose homogeneous scalars raise
degrees: a scalar of degree `i` sends the degree-`n` summand to the degree-`i + n` summand.
For an integer `k` the elements whose components in degrees `< k` vanish then form an
`S`-submodule.

Nothing here mentions `Proj`: the degree-raising law is the hypothesis `hsmul`, and the two
instances in the repository are the twisted global sections of a sheaf and the shifted global
sections of a graded module, whose actions are
`Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections` and
`Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistedSections.gradedActionTruncation`: the degree-`≥ k` part,
  as an `S`-submodule of `⨁_{n ∈ ℤ} V n`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistedSections.component_smul_eq_zero_of_gradedAction`: scaling
  preserves the vanishing of the components in degrees `< k`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum

namespace Stacks.AlgebraicGeometry.ProjTwistedSections

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

section GradedAction

variable {V : ℤ → Type*} [∀ n, AddCommGroup (V n)] [Module S (⨁ n : ℤ, V n)]

/-- **Scaling an element of a graded direct sum whose components in degrees `< k` vanish keeps
them zero**, for any `ℕ`-graded action of `S` that raises degrees: the scalar decomposes into
homogeneous pieces, and a piece of degree `i` sends the degree-`m` summand to the degree-`i + m`
summand, where `n < k ≤ m ≤ i + m`.

Nothing here is about `Proj`: the hypothesis `hsmul` is the whole input, and the two instances of
this lemma in the repository are the twisted global sections of a sheaf and the shifted global
sections of a graded module, whose degree-raising actions are
`Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections` and
`Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections`. -/
@[ega "II 8.2.1" "partial"]
theorem component_smul_eq_zero_of_gradedAction
    (act : ∀ (i : ℕ) (n : ℤ), 𝒮 i → V n → V ((i : ℤ) + n))
    (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : V n),
      (a : S) • (DirectSum.of V n s : ⨁ m : ℤ, V m) =
        DirectSum.of V ((i : ℤ) + n) (act i n a s))
    (k : ℤ) (c : S) {x : ⨁ n : ℤ, V n}
    (hx : ∀ m : ℤ, m < k → DirectSum.component ℤ ℤ V m x = 0)
    (n : ℤ) (hn : n < k) :
    DirectSum.component ℤ ℤ V n (c • x) = 0 := by
  classical
  have hhom : ∀ (i : ℕ) (a : 𝒮 i),
      DirectSum.component ℤ ℤ V n ((a : S) • x) = 0 := by
    intro i a
    rw [← DirectSum.sum_support_of x, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk : k ≤ m := by
      by_contra hlt
      refine DFinsupp.mem_support_iff.mp hm ?_
      have h0 := hx m (not_le.mp hlt)
      rwa [← DirectSum.apply_eq_component] at h0
    refine (congrArg (fun y => DirectSum.component ℤ ℤ V n y) (hsmul i m a (x m))).trans ?_
    rw [← DirectSum.apply_eq_component,
      DirectSum.of_eq_of_ne _ _ _ (by omega : n ≠ (i : ℤ) + m)]
  rw [← DirectSum.sum_support_decompose 𝒮 c, Finset.sum_smul, map_sum]
  exact Finset.sum_eq_zero fun i _ => hhom i (DirectSum.decompose 𝒮 c i)

/-- **The degree-`≥ k` truncation of a graded direct sum carrying a degree-raising action of `S`,
as an `S`-submodule.** The two instances are the twisted global sections of a sheaf on `Proj 𝒮`
and the shifted global sections of a graded module; see
`Stacks.AlgebraicGeometry.ProjTwistedSections.component_smul_eq_zero_of_gradedAction`. -/
@[ega "II 8.12.9" "special case", ega "II 8.2.1" "special case"]
def gradedActionTruncation
    (act : ∀ (i : ℕ) (n : ℤ), 𝒮 i → V n → V ((i : ℤ) + n))
    (hsmul : ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : V n),
      (a : S) • (DirectSum.of V n s : ⨁ m : ℤ, V m) =
        DirectSum.of V ((i : ℤ) + n) (act i n a s))
    (k : ℤ) : Submodule S (⨁ n : ℤ, V n) where
  carrier := {x | ∀ n : ℤ, n < k → DirectSum.component ℤ ℤ V n x = 0}
  add_mem' {x y} hx hy n hn := by rw [map_add, hx n hn, hy n hn, add_zero]
  zero_mem' n _ := map_zero _
  smul_mem' c x hx n hn :=
    component_smul_eq_zero_of_gradedAction 𝒮 act hsmul k c hx n hn

end GradedAction

end Stacks.AlgebraicGeometry.ProjTwistedSections

end
