module

public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic

/-!
# Degree-one generation, degree by degree

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring which is generated in degree one over its degree-zero
part, `Algebra.adjoin (𝒮 0) (𝒮 1) = ⊤`. Then for every `n` the homogeneous piece `𝒮 (n + 1)` is
the product `𝒮 1 · 𝒮 n`: every element of it is a finite sum `∑ aⱼ bⱼ` with `aⱼ ∈ 𝒮 1` and
`bⱼ ∈ 𝒮 n`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_sum_degreeOne_mul`: the decomposition
  described above.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **`𝒮 (n + 1) = 𝒮 1 · 𝒮 n` in a graded ring generated in degree one.** A homogeneous element
of degree `n + 1` is a finite sum `∑ aⱼ bⱼ` with `aⱼ` of degree one and `bⱼ` of degree `n`. -/
theorem exists_sum_degreeOne_mul (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) (n : ℕ)
    {x : S} (hx : x ∈ 𝒮 (n + 1)) :
    ∃ (r : ℕ) (a : Fin r → 𝒮 1) (b : Fin r → 𝒮 n), x = ∑ i, (a i : S) * (b i : S) := by
  classical
  have hxspan : x ∈ Ideal.span (𝒮 1 : Set S) := by
    rw [span_degreeOne_eq_irrelevant 𝒮 hgen]
    exact mem_irrelevant_of_mem_of_pos 𝒮 hx (Nat.succ_pos n)
  obtain ⟨r, c, g, hsum⟩ := Submodule.mem_span_set'.mp hxspan
  refine ⟨r, fun i => ⟨(g i : S), SetLike.mem_coe.mp (g i).2⟩,
    fun i => ⟨GradedRing.proj 𝒮 n (c i), proj_mem 𝒮 (c i) n⟩, ?_⟩
  rw [← proj_eq_self_of_mem 𝒮 hx, ← hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, proj_mul_eq 𝒮 (c i) (g i : S) 1 (n + 1) (SetLike.mem_coe.mp (g i).2) (by lia)]
  exact mul_comm _ _

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
