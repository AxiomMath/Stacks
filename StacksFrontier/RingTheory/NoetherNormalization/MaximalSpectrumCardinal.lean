module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.SetTheory.Cardinal.Basic
public import StacksFrontier.RingTheory.NoetherNormalization.Basic

/-!
# A finite type algebra of positive dimension has at least `#k` maximal ideals

Let `k` be a field and `T` a finite type `k`-algebra of positive Krull dimension. Then `T` has at
least as many maximal ideals as `k` has elements.

By Noether normalization (Tag 00OY, `noether_normalization_global`) there is an injective finite
`k`-algebra map `k[y₁, …, y_d] → T` with `d = dim T ≥ 1`. For `c ∈ k` the kernel `P_c` of the
evaluation at `(c, …, c)` is a maximal ideal of `k[y₁, …, y_d]`, and by lying over (Tag 00GQ) it is
the contraction of a maximal ideal `Q_c` of `T`. Since `y₁ - c ∈ P_c`, the ideals `P_c`, hence the
`Q_c`, are pairwise distinct.

## Main results

* `Algebra.FiniteType.cardinalMk_le_maximalSpectrum`: `#k ≤ #MaxSpec(T)`.

## References

* [Stacks Project, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)
* [Stacks Project, Tag 00GQ](https://stacks.math.columbia.edu/tag/00GQ)
-/

@[expose] public section

universe u

/-- **A finite type algebra of positive Krull dimension over a field `k` has at least `#k` maximal
ideals**: the maximal ideals lying over the points `(c, …, c)`, `c ∈ k`, of a Noether
normalization are pairwise distinct. -/
theorem Algebra.FiniteType.cardinalMk_le_maximalSpectrum {k T : Type u} [Field k] [CommRing T]
    [Algebra k T] [Algebra.FiniteType k T] (hT : 0 < ringKrullDim T) :
    Cardinal.mk k ≤ Cardinal.mk (MaximalSpectrum T) := by
  have : Nontrivial T := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hT
    exact absurd hT (by simp)
  obtain ⟨d, ψ, hd, hinj, hfin⟩ := noether_normalization_global (k := k) (T := T)
  have hd0 : 0 < d := by
    rw [← hd] at hT
    exact_mod_cast hT
  let := ψ.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin d) k) T := ⟨hfin.to_isIntegral⟩
  let P : k → Ideal (MvPolynomial (Fin d) k) := fun c =>
    RingHom.ker (MvPolynomial.aeval (fun _ : Fin d => c) : MvPolynomial (Fin d) k →ₐ[k] k)
  have hPmax : ∀ c, (P c).IsMaximal := fun c =>
    RingHom.ker_isMaximal_of_surjective _ fun x => ⟨MvPolynomial.C x, by simp⟩
  have hQ : ∀ c, ∃ Q : Ideal T, Q.IsMaximal ∧ Q.comap (algebraMap _ T) = P c := by
    intro c
    have := hPmax c
    refine Ideal.exists_ideal_over_maximal_of_isIntegral (P c) ?_
    intro x hx
    have : x = 0 := hinj ((RingHom.mem_ker.mp hx).trans (map_zero ψ).symm)
    simp [this]
  choose Q hQmax hQcomap using hQ
  let F : k → MaximalSpectrum T := fun c => ⟨Q c, hQmax c⟩
  have hF : Function.Injective F := by
    intro c c' h
    have h' : P c = P c' := by
      rw [← hQcomap c, ← hQcomap c']
      exact congrArg (fun m : MaximalSpectrum T => m.asIdeal.comap (algebraMap _ T)) h
    have hmem : MvPolynomial.X ⟨0, hd0⟩ - MvPolynomial.C c ∈ P c := by
      simp [P, RingHom.mem_ker]
    rw [h'] at hmem
    simp only [P, RingHom.mem_ker, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply] at hmem
    exact (sub_eq_zero.mp hmem).symm
  exact Cardinal.mk_le_of_injective hF

end
