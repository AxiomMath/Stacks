module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of a module spanned by few elements

If a module `M` over a commutative ring is spanned by `r` elements, then `⋀^n M = 0` for `n > r`:
an `n`-fold wedge of combinations of `r` generators expands into wedges of `n` generators, each of
which repeats a generator.
-/

@[expose] public section

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **`⋀^n M = 0` for `n` larger than the number of generators of `M`.** -/
theorem subsingleton_of_span_eq_top {r : ℕ} (g : Fin r → M)
    (hg : Submodule.span R (Set.range g) = ⊤) {n : ℕ} (hrn : r < n) :
    Subsingleton (⋀[R]^n M) := by
  classical
  have key : ∀ v : Fin n → M, ιMulti R n v = 0 := by
    intro v
    choose c hc using fun i ↦
      (Submodule.mem_span_range_iff_exists_fun R).1 (hg ▸ Submodule.mem_top : v i ∈ _)
    obtain rfl : v = fun i ↦ ∑ j, c i j • g j := funext fun i ↦ (hc i).symm
    show (ιMulti R n).toMultilinearMap (fun i ↦ ∑ j ∈ (Finset.univ : Finset (Fin r)),
      c i j • g j) = 0
    rw [MultilinearMap.map_sum_finset]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    rw [MultilinearMap.map_smul_univ]
    obtain ⟨i, j, hne, hij⟩ := Fintype.exists_ne_map_eq_of_card_lt σ (by simpa using hrn)
    show _ • (ιMulti R n) (fun k ↦ g (σ k)) = 0
    rw [(ιMulti R n).map_eq_zero_of_eq _ (by simp [hij]) hne, smul_zero]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hmem : x ∈ (⊤ : Submodule R (⋀[R]^n M)) := Submodule.mem_top
  rw [← ιMulti_span R n M] at hmem
  refine Submodule.span_induction (p := fun z _ ↦ z = 0) ?_ rfl
    (fun _ _ _ _ h1 h2 ↦ by rw [h1, h2, add_zero]) (fun a _ _ h ↦ by rw [h, smul_zero]) hmem
  rintro _ ⟨v, rfl⟩
  exact key v

end exteriorPower

end
