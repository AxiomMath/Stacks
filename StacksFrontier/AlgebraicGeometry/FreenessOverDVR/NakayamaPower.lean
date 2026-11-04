module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# A map of finite modules over a local ring which is an isomorphism modulo `tʲ`

Let `R` be a local ring, `t` an element of its maximal ideal and `j ≥ 1`. A linear map
`α : M ⟶ N` of finite modules, with `N` projective, which induces an isomorphism
`M ⧸ tʲ M ≅ N ⧸ tʲ N`, is an isomorphism. Surjectivity is Nakayama's lemma for `N`; for
injectivity, a section of the now surjective `α` splits off its kernel `K` as a direct summand
of `M`, so that `K ⊆ tʲ M` forces `K ⊆ tʲ K`, and Nakayama's lemma for `K` gives `K = 0`.

The reductions modulo `tʲ` are given as surjections `p : M ⟶ M'` and `q : N ⟶ N'` whose kernels
are the multiples of `tʲ`, which is the shape in which they occur on the stalks of a sheaf of
modules and its quotient by a power of an ideal sheaf.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `bijective_of_bijective_reduction`: the statement above.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public section

universe u v w

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {R : Type u} [CommRing R] [IsLocalRing R] {t : R}
  {M N M' N' : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

/-- A multiple `tʲ • x` of an element of a submodule `S` lies in `(t) • S` when `j ≥ 1`. -/
private theorem pow_smul_mem_span_smul {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    {S : Submodule A P} {a : A} {j : ℕ} (hj : 1 ≤ j) {x : P} (hx : x ∈ S) :
    a ^ j • x ∈ Ideal.span {a} • S := by
  rw [← Nat.sub_add_cancel hj, pow_succ', mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) (S.smul_mem _ hx)

/-- **A map of finite modules over a local ring, with projective target, which is bijective
modulo `tʲ` for `t` in the maximal ideal and `j ≥ 1`, is bijective.** -/
theorem bijective_of_bijective_reduction (ht : t ∈ IsLocalRing.maximalIdeal R) {j : ℕ}
    (hj : 1 ≤ j) [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    (α : M →ₗ[R] N) (p : M →ₗ[R] M') (q : N →ₗ[R] N') (hp : Function.Surjective p)
    (hpker : ∀ m, p m = 0 ↔ ∃ v, t ^ j • v = m) (hqker : ∀ n, q n = 0 ↔ ∃ v, t ^ j • v = n)
    (ψ : M' →ₗ[R] N') (hψ : Function.Injective ψ ∧ Function.Surjective ψ)
    (hcomm : ∀ m, q (α m) = ψ (p m)) : Function.Bijective α := by
  have hjac : Ideal.span {t} ≤ Ideal.jacobson ⊥ :=
    (Ideal.span_singleton_le_iff_mem _).2 (IsLocalRing.maximalIdeal_le_jacobson ⊥ ht)
  -- Surjectivity, by Nakayama's lemma for `N`.
  have hsurj : Function.Surjective α := by
    have hle : (⊤ : Submodule R N) ≤ LinearMap.range α ⊔ Ideal.span {t} • ⊤ := by
      intro n _
      obtain ⟨m', hm'⟩ := hψ.2 (q n)
      obtain ⟨m, rfl⟩ := hp m'
      have h0 : q (n - α m) = 0 := by rw [map_sub, hcomm, hm', sub_self]
      obtain ⟨v, hv⟩ := (hqker _).1 h0
      rw [show n = α m + (n - α m) by abel]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self α m)
        (hv ▸ pow_smul_mem_span_smul hj Submodule.mem_top)
    exact LinearMap.range_eq_top.1 (top_le_iff.1
      (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac hle))
  refine ⟨?_, hsurj⟩
  -- Injectivity: a section of `α` splits off the kernel, which is then killed by Nakayama.
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property α LinearMap.id hsurj
  have hασ : ∀ n, α (σ n) = n := LinearMap.congr_fun hσ
  let ρ : M →ₗ[R] M := LinearMap.id - σ ∘ₗ α
  have hρker : ∀ m, ρ m ∈ LinearMap.ker α := fun m => by simp [ρ, hασ]
  have hK : LinearMap.ker α = LinearMap.range ρ :=
    le_antisymm (fun k hk => ⟨k, by simp [ρ, LinearMap.mem_ker.1 hk]⟩)
      fun _ ⟨m, hm⟩ => hm ▸ hρker m
  have hfg : (LinearMap.ker α).FG := by
    rw [hK, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map ρ
  have hle : LinearMap.ker α ≤ Ideal.span {t} • LinearMap.ker α := by
    intro k hk
    have hk0 : α k = 0 := LinearMap.mem_ker.1 hk
    have hpk : p k = 0 := hψ.1 ((hcomm k).symm.trans (by rw [hk0, map_zero, map_zero]))
    obtain ⟨y, rfl⟩ := (hpker k).1 hpk
    have hσ0 : t ^ j • σ (α y) = 0 := by rw [← map_smul, ← map_smul, hk0, map_zero]
    have hy : t ^ j • y = t ^ j • ρ y := by simp [ρ, smul_sub, hσ0]
    exact hy ▸ pow_smul_mem_span_smul hj (hρker y)
  exact LinearMap.ker_eq_bot.1 (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac)

end Stacks.AlgebraicGeometry.FreenessOverDVR
