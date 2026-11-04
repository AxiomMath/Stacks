module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.DualizingTraceIsomorphism

/-!
# A cyclic submodule of finite colength in a module of positive depth

Let `A` be a Noetherian normal local domain of dimension at least two and `N` a finite `A`-module
of positive depth which is not torsion. If an element `t ∈ N` generates `N` up to an ideal `I`
cutting out only the closed point — `I • N ⊆ A t` — then `a ↦ a • t` is an isomorphism `A ≅ N`.

This is how the proof of [Stacks, Tag 0EA2] concludes that the trace map `A ⟶ ω_A` is an
isomorphism: its image is the image of the restriction `Hom(Rf_*𝒪_X, ω_A) ⟶ Hom(A, ω_A)`, whose
cokernel is killed by the annihilator of `R¹f_*𝒪_X`, an ideal primary to the maximal ideal. Away
from the closed point the map is then surjective, and it is injective because `t` is not
torsion; [Stacks, Tag 0AVM] in the ring form of
`Stacks.PurityRamification.bijective_of_bijective_localized_of_one_le_depth` finishes.

## Main results

* `Stacks.PurityRamification.bijective_smul_of_smul_le_span`: the isomorphism.

## References

* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
* [Stacks Project, Tag 0AVM](https://stacks.math.columbia.edu/tag/0AVM)
-/

@[expose] public section

universe u

namespace Stacks.PurityRamification

/-- **A cyclic submodule of finite colength in a module of positive depth is everything, and is
free.** Let `A` be a Noetherian normal local domain with `dim A ≥ 2`, `N` a finite `A`-module of
positive depth containing an element `n₀` with zero annihilator, `I` an ideal contained in no
prime other than the maximal ideal, and `t ∈ N` with `I • N ⊆ A t`. Then `a ↦ a • t` is a
bijection `A → N`. -/
theorem bijective_smul_of_smul_le_span {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) N)
    (n₀ : N) (hn₀ : ∀ b : A, b • n₀ = 0 → b = 0)
    (I : Ideal A) (hI : ∀ (p : Ideal A) (_ : p.IsPrime), p ≠ IsLocalRing.maximalIdeal A → ¬ I ≤ p)
    (t : N) (ht : ∀ c ∈ I, ∀ n : N, ∃ b : A, c • n = b • t) :
    Function.Bijective (LinearMap.toSpanSingleton A N t) := by
  -- `A` is not a field, so `(0)` is a prime other than the maximal ideal
  have hbot : (⊥ : Ideal A) ≠ IsLocalRing.maximalIdeal A := by
    intro h
    have hfield : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).2 h.symm
    have h0 : ringKrullDim A = 0 := ringKrullDim_eq_zero_of_isField hfield
    rw [h0] at hdim
    exact absurd hdim (by decide)
  obtain ⟨c₀, hc₀I, hc₀⟩ : ∃ c ∈ I, c ≠ 0 := by
    by_contra h
    push Not at h
    exact hI ⊥ Ideal.isPrime_bot hbot (fun x hx => (Submodule.mem_bot A).2 (h x hx))
  -- `t` has zero annihilator
  have hinj : Function.Injective (LinearMap.toSpanSingleton A N t) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at ha
    obtain ⟨b, hb⟩ := ht c₀ hc₀I n₀
    have : (a * c₀) • n₀ = 0 := by rw [mul_smul, hb, smul_comm, ha, smul_zero]
    have hac := hn₀ _ this
    rcases mul_eq_zero.1 hac with h | h
    · exact h
    · exact absurd h hc₀
  refine bijective_of_bijective_localized_of_one_le_depth hdim _ (fun p hp hpm => ?_) hdepth
  refine ⟨LocalizedModule.map_injective _ _ hinj, fun x => ?_⟩
  induction x using LocalizedModule.induction_on with | h n s => ?_
  obtain ⟨c, hcI, hcp⟩ := Set.not_subset.1 (hI p hp hpm)
  obtain ⟨b, hb⟩ := ht c hcI n
  refine ⟨LocalizedModule.mk b (⟨c, hcp⟩ * s), ?_⟩
  rw [LocalizedModule.map_mk, LinearMap.toSpanSingleton_apply, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, mul_smul, ← hb]
  rw [smul_comm (s : A) c n]

end Stacks.PurityRamification

end
