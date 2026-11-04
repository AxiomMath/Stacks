module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# A common eigenvector of a commuting family of endomorphisms

Over an algebraically closed field, any family of pairwise commuting endomorphisms of a nonzero
finite-dimensional vector space has a common eigenvector. If every member of the family is a
scalar, any nonzero vector will do. Otherwise some member `T` is not a scalar. It has an
eigenvalue `μ`, and the eigenspace `ker (T - μ)` is a nonzero proper subspace, stable under the
whole family because the family commutes with `T`. The family restricted to it still commutes,
so we conclude by induction on the dimension.

## Main results

* `Stacks.Drinfeld.exists_common_eigenvector` — the common eigenvector.
-/

@[expose] public noncomputable section

open Module

namespace Stacks.Drinfeld

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- **A common eigenvector.** A family of pairwise commuting endomorphisms of a nonzero
finite-dimensional vector space over an algebraically closed field has a common eigenvector. -/
public theorem exists_common_eigenvector {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] {ι : Type*} (T : ι → End F V)
    (hT : ∀ i j, Commute (T i) (T j)) : ∃ x : V, x ≠ 0 ∧ ∀ i, ∃ μ : F, T i x = μ • x := by
  induction h : finrank F V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
    by_cases hs : ∀ i, ∃ μ : F, ∀ x, T i x = μ • x
    · obtain ⟨x, hx⟩ := exists_ne (0 : V)
      exact ⟨x, hx, fun i => (hs i).imp fun μ hμ => hμ x⟩
    push Not at hs
    obtain ⟨i₀, hi₀⟩ := hs
    obtain ⟨μ, hμ⟩ := (T i₀).exists_eigenvalue
    set W := (T i₀).eigenspace μ with hW
    have hWbot : W ≠ ⊥ := hμ
    have hWtop : W ≠ ⊤ := by
      intro htop
      obtain ⟨x, hx⟩ := hi₀ μ
      have : x ∈ W := htop ▸ Submodule.mem_top
      exact hx (Module.End.mem_eigenspace_iff.1 this)
    have hc : ∀ i j x, T i (T j x) = T j (T i x) := fun i j x => congr($((hT i j).eq) x)
    have hmaps : ∀ i, ∀ x ∈ W, T i x ∈ W := by
      intro i x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hc, hx, map_smul]
    let T' : ι → End F W := fun i => (T i).restrict (hmaps i)
    have hT' : ∀ i j, Commute (T' i) (T' j) := by
      intro i j
      refine LinearMap.ext fun x => Subtype.ext ?_
      exact hc i j x
    have hlt : finrank F W < n := h ▸ Submodule.finrank_lt hWtop
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hWbot
    obtain ⟨x, hx, hxe⟩ := ih _ hlt T' hT' rfl
    refine ⟨x, fun h0 => hx (Subtype.ext h0), fun i => ?_⟩
    obtain ⟨c, hc⟩ := hxe i
    exact ⟨c, congrArg Subtype.val hc⟩

end Stacks.Drinfeld

end
