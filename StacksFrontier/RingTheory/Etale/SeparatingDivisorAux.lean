module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Auxiliary lemmas for the étale divisor of a family of smooth curves

* `Submodule.subsingleton_residueField_tensor_quotient_span_singleton`: if `κ(P) ⊗ M` is a line
  and `1 ⊗ v ≠ 0` there, then `κ(P) ⊗ (M ⧸ ⟨v⟩) = 0`.
* `Polynomial.exists_ne_zero_aeval_smul_eq_zero`: if `S` is finite over `K[X]` through `t` and a
  finite `S`-module `N` vanishes at every minimal prime of `S`, then `N` is killed by `b(t)` for
  some nonzero `b ∈ K[X]`. A prime of `S` containing the annihilator and lying over `(0)` would
  be minimal (incomparability), and `N` does not vanish there.
* `Submodule.exists_smul_mem_sup_of_isLocalizedModule`: membership in `⟨v⟩ + f M` descends from a
  localization `M'` of `M` up to a denominator.
* `RingHom.IsIntegralElem.exists_smul_of_isLocalization`: integrality over `A[X]` descends from a
  localization `B'` of `B` at the image of a submonoid of `A`, up to a denominator.

These are the module-theoretic steps of the construction of a divisor `V(h(t))`, finite étale
over the base, on a family of smooth curves, along which the Gysin map of `R² g_!` is taken in the
reduction of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).
-/

public section

open TensorProduct Polynomial Pointwise

/-- **The fibre of `M ⧸ ⟨v⟩` vanishes where `M` has a one-dimensional fibre spanned by `v`.** -/
theorem Submodule.subsingleton_residueField_tensor_quotient_span_singleton {S M : Type*}
    [CommRing S] [AddCommGroup M] [Module S M] (P : Ideal S) [P.IsPrime] (v : M)
    (hrank : Module.finrank P.ResidueField (P.ResidueField ⊗[S] M) = 1)
    (hv : (1 : P.ResidueField) ⊗ₜ[S] v ≠ 0) :
    Subsingleton (P.ResidueField ⊗[S] (M ⧸ Submodule.span S {v})) := by
  have hsurj : Function.Surjective
      (LinearMap.lTensor P.ResidueField (Submodule.span S {v}).mkQ) :=
    LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  refine subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨w, rfl⟩ := hsurj z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 hrank w
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, LinearMap.lTensor_tmul, Submodule.mkQ_apply,
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self v),
    TensorProduct.tmul_zero]

/-- **A module vanishing at the minimal primes of a finite `K[X]`-algebra is killed by a nonzero
polynomial**: if `S` is finite over `K[X]` through `t` and the finite `S`-module `N` has
`κ(P) ⊗ N = 0` at every minimal prime `P` of `S`, then `b(t) • N = 0` for some `b ≠ 0`. -/
theorem Polynomial.exists_ne_zero_aeval_smul_eq_zero {K S N : Type*} [Field K] [CommRing S]
    [Algebra K S] [AddCommGroup N] [Module S N] [Module.Finite S N] (t : S)
    (hfin : (aeval t : K[X] →ₐ[K] S).Finite)
    (hN : ∀ (P : Ideal S) [P.IsPrime], P ∈ minimalPrimes S →
      Subsingleton (P.ResidueField ⊗[S] N)) :
    ∃ b : K[X], b ≠ 0 ∧ ∀ n : N, aeval t b • n = 0 := by
  let : Algebra K[X] S := (aeval t : K[X] →ₐ[K] S).toRingHom.toAlgebra
  have : Algebra.IsIntegral K[X] S := ⟨fun x => hfin.to_isIntegral x⟩
  by_contra! H
  have hJ : (Module.annihilator S N).comap (algebraMap K[X] S) ≤ ⊥ := by
    intro b hb
    rw [Ideal.mem_bot]
    by_contra hb0
    obtain ⟨n, hn⟩ := H b hb0
    exact hn (Module.mem_annihilator.1 hb n)
  obtain ⟨Q, hIQ, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal K[X]) _ hJ
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S) ≤ Q)
  have : P.IsPrime := hP.1.1
  have hPQ' : P = Q := by
    by_contra hne
    obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPQ hne)
    have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff hPQ ⟨hxQ, hxP⟩
      (Algebra.IsIntegral.isIntegral (R := K[X]) x)
    rw [hQc] at hlt
    exact not_lt_bot hlt
  subst hPQ'
  have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum S) ∈ Module.support S N :=
    Module.mem_support_iff_of_finite.2 hIQ
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hmem
  have := hN P hP
  exact not_subsingleton _ ‹_›

/-- **Membership in `⟨v⟩ + f • M` descends from a localization up to a denominator**: if
`φ : M ⟶ M'` is a localization at a submonoid `p` of `A`, `B'` the localization of `B` at the
image of `p`, and `φ ω ∈ ⟨φ v⟩ + f • M'`, then `s • ω ∈ ⟨v⟩ + f • M` for some `s ∈ p`. -/
theorem Submodule.exists_smul_mem_sup_of_isLocalizedModule {A B B' M M' : Type*} [CommRing A]
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
    (p : Submonoid A) [IsLocalization (Algebra.algebraMapSubmonoid B p) B']
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module B' M'] [Module B M'] [Module A M'] [IsScalarTower B B' M']
    [IsScalarTower A B M']
    (φ : M →ₗ[B] M') [IsLocalizedModule p (φ.restrictScalars A)] (v : M) (f : B) (ω : M)
    (hω : φ ω ∈ Submodule.span B' {φ v} ⊔ (algebraMap B B' f) • (⊤ : Submodule B' M')) :
    ∃ s ∈ p, s • ω ∈ Submodule.span B {v} ⊔ f • (⊤ : Submodule B M) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hω
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨η, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
  obtain ⟨⟨c', m⟩, hc⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B p) c
  obtain ⟨s₁, hs₁, hm⟩ := m.2
  obtain ⟨⟨η', s₂⟩, hη⟩ := IsLocalizedModule.surj p (φ.restrictScalars A) η
  simp only [LinearMap.coe_restrictScalars] at hη
  -- all scalars are read in `B'`
  have e1 : ∀ (b : B) (m : M'), b • m = algebraMap B B' b • m := fun b m =>
    (algebraMap_smul B' b m).symm
  set S₁ := algebraMap A B s₁
  set S₂ := algebraMap A B s₂
  have hc' : c * algebraMap B B' S₁ = algebraMap B B' c' := by rw [← hc, ← hm]
  have hη' : algebraMap B B' S₂ • η = φ η' := by
    rw [← e1, algebraMap_smul, ← hη]
    rfl
  have key : φ ((S₁ * S₂) • ω) = φ (S₂ • c' • v + S₁ • f • η') := by
    calc φ ((S₁ * S₂) • ω) = algebraMap B B' (S₁ * S₂) • φ ω := by rw [map_smul, e1]
      _ = algebraMap B B' (S₁ * S₂) • (c • φ v + algebraMap B B' f • η) := by rw [hyz]
      _ = algebraMap B B' S₂ • ((c * algebraMap B B' S₁) • φ v) +
          algebraMap B B' S₁ • (algebraMap B B' f • (algebraMap B B' S₂ • η)) := by
        simp only [smul_add, smul_smul, map_mul]
        congr 2 <;> ring
      _ = φ (S₂ • c' • v + S₁ • f • η') := by
        rw [hc', hη', map_add, map_smul, map_smul, map_smul, map_smul, e1 S₂, e1 c', e1 S₁,
          e1 f]
  obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := p) (f := φ.restrictScalars A) key
  refine ⟨u * (s₁ * s₂), p.mul_mem u.2 (p.mul_mem hs₁ s₂.2), ?_⟩
  have hsm : ((u : A) * (s₁ * s₂)) • ω = (u : A) • ((S₁ * S₂) • ω) := by
    rw [mul_smul, ← algebraMap_smul B (s₁ * (s₂ : A)) ω, map_mul]
  rw [hsm, ← Submonoid.smul_def, hu, Submonoid.smul_def]
  refine Submodule.smul_of_tower_mem _ _ (Submodule.add_mem_sup ?_ ?_)
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  · rw [smul_comm]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- **Integrality over `A[X]` descends from a localization up to a denominator**: if `B'` is the
localization of `B` at the image of a submonoid `p` of `A` and the image of `y ∈ B` in `B'` is
integral over `A[X]` (through `X ↦ t`), so is `s • y` in `B` for some `s ∈ p`. -/
theorem RingHom.IsIntegralElem.exists_smul_of_isLocalization {A B B' : Type*} [CommRing A]
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
    (p : Submonoid A) [IsLocalization (Algebra.algebraMapSubmonoid B p) B'] (t y : B)
    (hy : ((algebraMap B B').comp (aeval t : A[X] →ₐ[A] B).toRingHom).IsIntegralElem
      (algebraMap B B' y)) :
    ∃ s ∈ p, (aeval t : A[X] →ₐ[A] B).toRingHom.IsIntegralElem (s • y) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := (algebraMap A B).codomain_trivial
    exact ⟨1, p.one_mem, X, monic_X, Subsingleton.elim _ _⟩
  obtain ⟨P, hPm, hP⟩ := hy
  set g := (aeval t : A[X] →ₐ[A] B).toRingHom
  have h0 : algebraMap B B' (eval₂ g y (P * X)) = 0 := by
    rw [eval₂_mul, map_mul, hom_eval₂, hP, zero_mul]
  obtain ⟨⟨u, s, hs, rfl⟩, hu⟩ := (IsLocalization.map_eq_zero_iff
    (Algebra.algebraMapSubmonoid B p) B' _).1 h0
  refine ⟨s, hs, (P * X).scaleRoots (C s), (monic_scaleRoots_iff _).2 (hPm.mul monic_X), ?_⟩
  have hsy : s • y = g (C s) * y := by
    rw [Algebra.smul_def]
    congr 1
    simp [g]
  have hdeg : (P * X).natDegree = (P * X).natDegree - 1 + 1 := by
    rw [natDegree_mul_X hPm.ne_zero]
    omega
  rw [hsy, scaleRoots_eval₂_mul, hdeg, pow_succ, mul_assoc]
  have : g (C s) * eval₂ g y (P * X) = 0 := by
    have : g (C s) = algebraMap A B s := by simp [g]
    rw [this]
    exact hu
  rw [this, mul_zero]
