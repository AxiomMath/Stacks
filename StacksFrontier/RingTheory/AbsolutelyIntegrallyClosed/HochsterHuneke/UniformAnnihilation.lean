module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Uniform annihilation of parameter colons near a free point

Let `R` be a domain, `T` a finite `R`-algebra and `x, y, z ∈ R` elements such that `z^t` is a
nonzerodivisor modulo `(x^t, y^t)` on `R` for every `t`. The colon modules
`((x^t, y^t)T : z^t) / (x^t, y^t)T` need not vanish, but they are killed by every `c ∈ R` for which
multiplication by `c` on `T` factors through a free `R`-module. If `T_Q` is free over `R_Q` at a
prime `Q`, a basis of `T_Q` chosen inside `T` gives an injective map `φ : R^n → T` whose cokernel
is killed by some `c ∉ Q`, and such a `c` kills all the colon modules at once.

## Main results

* `exists_notMem_forall_mul_mem_span_pow_pair`: if `T_Q` is free over `R_Q`, there is `c ∉ Q`
  killing every class `u` with `z^t u ∈ (x^t, y^t)T` modulo `(x^t, y^t)T`, uniformly in `t`.
-/

open Module

/-- If every element of a finite module `M` has a multiple outside the prime `Q` lying in `N`, then
a single `c ∉ Q` multiplies all of `M` into `N`. -/
theorem Submodule.exists_notMem_forall_smul_mem {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (Q : Ideal R) [Q.IsPrime] (N : Submodule R M)
    (h : ∀ u : M, ∃ d ∈ Q.primeCompl, d • u ∈ N) : ∃ c ∉ Q, ∀ u : M, c • u ∈ N := by
  have hsub : Subsingleton (LocalizedModule Q.primeCompl (M ⧸ N)) := by
    rw [LocalizedModule.subsingleton_iff]
    intro m
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨d, hd, hdu⟩ := h u
    exact ⟨d, hd, by rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]⟩
  have hQ : ⟨Q, inferInstance⟩ ∉ Module.support R (M ⧸ N) := Module.notMem_support_iff.mpr hsub
  rw [Module.mem_support_iff_of_finite] at hQ
  obtain ⟨c, hcann, hcQ⟩ := Set.not_subset.mp hQ
  refine ⟨c, hcQ, fun u => ?_⟩
  have := (Module.mem_annihilator.mp hcann) (Submodule.Quotient.mk u)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

/-- Lifts `e i ∈ T` of multiples `s i • b i` of a basis `b` of `N` over `R_Q` (with `s i ∉ Q`)
are linearly independent over the domain `R`. -/
theorem injective_linearCombination_of_smul_basis_eq {R T N ι : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup T] [Module R T] {Q : Ideal R} [Q.IsPrime] [AddCommGroup N] [Module R N]
    [Module (Localization.AtPrime Q) N] [IsScalarTower R (Localization.AtPrime Q) N]
    (f : T →ₗ[R] N) [Fintype ι] (b : Basis ι (Localization.AtPrime Q) N) {e : ι → T}
    {s : ι → Q.primeCompl} (hp : ∀ i, s i • b i = f (e i)) :
    Function.Injective (Fintype.linearCombination R e) := by
  set φ : (ι → R) →ₗ[R] T := Fintype.linearCombination R e
  have hinjR : Function.Injective (algebraMap R (Localization.AtPrime Q)) :=
    IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro r hr
  have h1 : f (φ r) = ∑ i, algebraMap R (Localization.AtPrime Q) (r i * (s i : R)) • b i := by
    rw [Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hp i, map_mul, mul_smul, algebraMap_smul, algebraMap_smul]
    rfl
  rw [hr, map_zero] at h1
  have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1.symm
  funext i
  have h3 := hinjR ((h2 i).trans (map_zero _).symm)
  exact (mul_eq_zero.mp h3).resolve_right fun h0 => (s i).2 (h0 ▸ Q.zero_mem)

/-- If `f : T → N` is a localization at `Q` and `e i ∈ T` lift multiples `s i • b i` of a basis `b`
of `N` over `R_Q` (with `s i ∉ Q`), every element of `T` has a multiple outside `Q` in the
`R`-span of the `e i`. -/
theorem exists_smul_mem_range_linearCombination_of_smul_basis_eq {R T N ι : Type*} [CommRing R]
    [AddCommGroup T] [Module R T] {Q : Ideal R} [Q.IsPrime] [AddCommGroup N] [Module R N]
    [Module (Localization.AtPrime Q) N] [IsScalarTower R (Localization.AtPrime Q) N]
    (f : T →ₗ[R] N) [IsLocalizedModule Q.primeCompl f] [Fintype ι]
    (b : Basis ι (Localization.AtPrime Q) N) {e : ι → T} {s : ι → Q.primeCompl}
    (hp : ∀ i, s i • b i = f (e i)) (u : T) :
    ∃ d ∈ Q.primeCompl, d • u ∈ LinearMap.range (Fintype.linearCombination R e) := by
  classical
  set φ : (ι → R) →ₗ[R] T := Fintype.linearCombination R e
  obtain ⟨⟨σ, hσ⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples Q.primeCompl Finset.univ (fun i => b.repr (f u) i)
  choose a ha using hint
  have hsum : f u = ∑ i, b.repr (f u) i • b i := (b.sum_repr (f u)).symm
  set S : R := ∏ i, (s i : R)
  have hS : S ∈ Q.primeCompl := Q.primeCompl.prod_mem fun i _ => (s i).2
  let r : ι → R := fun i => a i (Finset.mem_univ i) * ∏ j ∈ Finset.univ.erase i, (s j : R)
  have heq : f ((S * σ) • u) = f (φ r) := by
    rw [map_smul, hsum, Finset.smul_sum, Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hai := ha i (Finset.mem_univ i)
    have hSi : S = (s i : R) * ∏ j ∈ Finset.univ.erase i, (s j : R) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [map_smul, ← hp i]
    show (S * σ) • (b.repr (f u) i • b i) = r i • ((s i : R) • b i)
    rw [← algebraMap_smul (Localization.AtPrime Q) (S * σ), smul_smul,
      ← algebraMap_smul (Localization.AtPrime Q) (r i),
      ← algebraMap_smul (Localization.AtPrime Q) (s i : R), smul_smul]
    congr 1
    have hai' : algebraMap R (Localization.AtPrime Q) σ * b.repr (f u) i =
        algebraMap R (Localization.AtPrime Q) (a i (Finset.mem_univ i)) := by
      rw [hai]
      exact (Algebra.smul_def σ _).symm
    rw [hSi, map_mul, map_mul, mul_assoc, hai']
    simp only [r, map_mul]
    ring
  obtain ⟨w, hw⟩ := IsLocalizedModule.exists_of_eq (S := Q.primeCompl) heq
  refine ⟨w * (S * σ), Q.primeCompl.mul_mem w.2 (Q.primeCompl.mul_mem hS hσ), ?_⟩
  refine ⟨(w : R) • r, ?_⟩
  rw [map_smul]
  have hw' : (w : R) • (S * σ) • u = (w : R) • φ r := hw
  rw [← hw', smul_smul]

/-- If `φ : R^ι → T` is injective and `c` multiplies `T` into the range of `φ`, then `c` kills the
colon `((x^t, y^t)T : z^t) / (x^t, y^t)T` whenever `z^t` is regular modulo `(x^t, y^t)` on `R`. -/
theorem mul_mem_span_pow_pair_of_injective {R T ι : Type*} [CommRing R] [CommRing T]
    [Algebra R T] {φ : (ι → R) →ₗ[R] T} (hφ : Function.Injective φ) {c : R}
    (hc : ∀ u : T, c • u ∈ LinearMap.range φ) {x y z : R}
    (hreg : ∀ (t : ℕ) (r : R), z ^ t * r ∈ Ideal.span {x ^ t, y ^ t} →
      r ∈ Ideal.span {x ^ t, y ^ t}) (t : ℕ) (u : T)
    (hu : algebraMap R T z ^ t * u ∈ Ideal.span {algebraMap R T x ^ t, algebraMap R T y ^ t}) :
    algebraMap R T c * u ∈ Ideal.span {algebraMap R T x ^ t, algebraMap R T y ^ t} := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hu
  obtain ⟨ρ, hρ⟩ := hc u
  obtain ⟨ρA, hρA⟩ := hc A
  obtain ⟨ρB, hρB⟩ := hc B
  have hrel : z ^ t • ρ = x ^ t • ρA + y ^ t • ρB := by
    apply hφ
    rw [map_add, map_smul, map_smul, map_smul, hρ, hρA, hρB, smul_comm _ c u, smul_comm _ c A,
      smul_comm _ c B, ← smul_add]
    congr 1
    simp only [Algebra.smul_def, map_pow]
    linear_combination (-1 : T) * hAB
  have hcoord : ∀ i, ρ i ∈ Ideal.span {x ^ t, y ^ t} := fun i => by
    refine hreg t _ (Ideal.mem_span_pair.mpr ⟨ρA i, ρB i, ?_⟩)
    have := congrFun hrel i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    rw [this]
    ring
  choose α β hαβ using fun i => Ideal.mem_span_pair.mp (hcoord i)
  have hρ' : ρ = x ^ t • α + y ^ t • β := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hαβ i]
    ring
  refine Ideal.mem_span_pair.mpr ⟨φ α, φ β, ?_⟩
  rw [← Algebra.smul_def, ← hρ, hρ', map_add, map_smul, map_smul, Algebra.smul_def,
    Algebra.smul_def, map_pow, map_pow]
  ring

/-- **Uniform annihilation of parameter colons at a free point.** Let `R` be a domain, `T` a finite
`R`-algebra and `Q` a prime of `R` such that the localization `T_Q` of `T` is free over `R_Q`. If
`z^t` is a nonzerodivisor modulo `(x^t, y^t)` on `R` for every `t`, then there is `c ∉ Q` such that
`c u ∈ (x^t, y^t)T` whenever `z^t u ∈ (x^t, y^t)T`, for all `t` and `u` simultaneously. -/
theorem exists_notMem_forall_mul_mem_span_pow_pair {R T : Type*} [CommRing R] [IsDomain R]
    [CommRing T] [Algebra R T] [Module.Finite R T] (Q : Ideal R) [Q.IsPrime]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (Localization.AtPrime Q) N]
    [IsScalarTower R (Localization.AtPrime Q) N] (f : T →ₗ[R] N)
    [IsLocalizedModule Q.primeCompl f] [Module.Free (Localization.AtPrime Q) N]
    {x y z : R}
    (hreg : ∀ (t : ℕ) (r : R), z ^ t * r ∈ Ideal.span {x ^ t, y ^ t} →
      r ∈ Ideal.span {x ^ t, y ^ t}) :
    ∃ c ∉ Q, ∀ (t : ℕ) (u : T),
      algebraMap R T z ^ t * u ∈ Ideal.span {algebraMap R T x ^ t, algebraMap R T y ^ t} →
        algebraMap R T c * u ∈ Ideal.span {algebraMap R T x ^ t, algebraMap R T y ^ t} := by
  have : Module.Finite (Localization.AtPrime Q) N :=
    Module.Finite.of_isLocalizedModule Q.primeCompl f
  let b := Module.Free.chooseBasis (Localization.AtPrime Q) N
  choose p hp using fun i => IsLocalizedModule.surj Q.primeCompl f (b i)
  obtain ⟨c, hcQ, hc⟩ := Submodule.exists_notMem_forall_smul_mem Q _
    (exists_smul_mem_range_linearCombination_of_smul_basis_eq (e := fun i => (p i).1)
      (s := fun i => (p i).2) f b hp)
  exact ⟨c, hcQ, mul_mem_span_pow_pair_of_injective
    (injective_linearCombination_of_smul_basis_eq (e := fun i => (p i).1)
      (s := fun i => (p i).2) f b hp) hc hreg⟩
