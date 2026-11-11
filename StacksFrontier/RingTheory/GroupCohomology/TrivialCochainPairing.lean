module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# A cocycle and a dual chain for the trivial cohomology of a finite group

Let `G` be a finite group and `k` a field. The complex of inhomogeneous cochains of `G` with
coefficients in an abelian group `R` on which `G` acts trivially has

`(dⁿ f)(g₀, …, gₙ) = f(g₁, …, gₙ) + ∑ⱼ (-1)^{j+1} f(g₀, …, gⱼ gⱼ₊₁, …, gₙ)`,

`AlgebraicGeometry.Stack.TrivialCochains.trivialCoboundary`. Its coefficients are integers, so it
commutes with every additive map of the coefficients.

If `Hⁿ⁺¹(G, k) ≠ 0` there is a cocycle `c` with values in `k` and a family of weights
`ℓ : Gⁿ⁺¹ → k` whose pairing `⟨ℓ, -⟩ = ∑ₜ ℓ(t) · (-)(t)` kills every coboundary and takes the
value `1` on `c`: the class of `c` is not zero, and since `k` is a field a linear form on the
cochains vanishing on the coboundaries and not on `c` exists. The weights are values in `k`, so
for every `k`-algebra `R` the same pairing `⟨ℓ, -⟩ : Cⁿ⁺¹(G, R) → R` kills the coboundaries of
`R`-valued cochains and sends `a · c` to `a`. This is the device by which the Stacks Project's
computation `Hⁿ(ℤ/pℤ, k[x]) ≅ k[x]` (Tag 07DC) is read on cochains, naturally in the ring.

## Main definitions

* `Stacks.GroupCohomology.TrivialCochains.trivialCoboundary`: the coboundary of the trivial
  action on `R`-valued cochains.
* `Stacks.GroupCohomology.TrivialCochains.pairing`: the pairing `⟨ℓ, -⟩`.

## Main results

* `Stacks.GroupCohomology.TrivialCochains.trivialCoboundary_comp`: the coboundary commutes with
  additive maps of the coefficients.
* `Stacks.GroupCohomology.TrivialCochains.exists_cocycle_pairing`: the cocycle and the weights,
  from the non-vanishing of `Hⁿ⁺¹(G, k)`.
* `Stacks.GroupCohomology.TrivialCochains.pairing_trivialCoboundary_algebraMap` and
  `Stacks.GroupCohomology.TrivialCochains.pairing_smul_algebraMap`: the two properties of the
  pairing over a `k`-algebra.

## References

* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
-/

@[expose] public section

noncomputable section

open CategoryTheory groupCohomology

universe u

namespace Stacks.GroupCohomology.TrivialCochains

variable {G : Type*} [Group G]

/-- **The coboundary of inhomogeneous cochains for the trivial action**,
`(dⁿ f)(g₀, …, gₙ) = f(g₁, …, gₙ) + ∑ⱼ (-1)^{j+1} f(g₀, …, gⱼ gⱼ₊₁, …, gₙ)`, on cochains with
values in an abelian group `R`. -/
def trivialCoboundary (R : Type*) [AddCommGroup R] (n : ℕ) :
    ((Fin n → G) → R) →+ ((Fin (n + 1) → G) → R) where
  toFun f g := f (fun i => g i.succ) +
    ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) • f (Fin.contractNth j (· * ·) g)
  map_zero' := by
    ext
    simp
  map_add' f f' := by
    ext g
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
    abel

theorem trivialCoboundary_apply (R : Type*) [AddCommGroup R] (n : ℕ) (f : (Fin n → G) → R)
    (g : Fin (n + 1) → G) :
    trivialCoboundary R n f g = f (fun i => g i.succ) +
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) • f (Fin.contractNth j (· * ·) g) :=
  rfl

/-- **The trivial coboundary commutes with additive maps of the coefficients.** -/
theorem trivialCoboundary_comp {R R' : Type*} [AddCommGroup R] [AddCommGroup R'] (φ : R →+ R')
    (n : ℕ) (f : (Fin n → G) → R) :
    trivialCoboundary R' n (φ ∘ f) = φ ∘ trivialCoboundary R n f := by
  ext g
  simp [trivialCoboundary_apply, map_add, map_sum, map_zsmul]

/-- The coboundary of Mathlib's complex of inhomogeneous cochains of the trivial representation
of `G` on `k` is the trivial coboundary. -/
theorem d_trivial_apply {k G : Type u} [CommRing k] [Group G] (n : ℕ) (f : (Fin n → G) → k)
    (g : Fin (n + 1) → G) :
    (inhomogeneousCochains.d (Rep.trivial k G k) n).hom f g = trivialCoboundary k n f g := by
  simp [inhomogeneousCochains.d_hom_apply, trivialCoboundary_apply, zsmul_eq_mul]

/-- **The pairing `⟨ℓ, f⟩ = ∑ₜ ℓ(t) · f(t)`** of weights `ℓ : Gⁿ → k` with cochains valued in a
`k`-module. -/
def pairing [Fintype G] {k : Type*} [CommRing k] {R : Type*} [AddCommGroup R] [Module k R]
    {n : ℕ} (ℓ : (Fin n → G) → k) (f : (Fin n → G) → R) : R :=
  ∑ t, ℓ t • f t

omit [Group G] in
theorem pairing_eq_dual_apply [Fintype G] [DecidableEq G] {k : Type*} [CommRing k] {n : ℕ}
    (φ : Module.Dual k ((Fin n → G) → k)) (v : (Fin n → G) → k) :
    pairing (fun t => φ (Pi.single t 1)) v = φ v := by
  conv_rhs => rw [← Finset.univ_sum_single v]
  simp only [pairing, map_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm, ← smul_eq_mul, ← map_smul]
  congr 1
  ext s
  by_cases hs : s = t <;> simp [hs]

/-- **A cocycle and weights for a non-vanishing cohomology group.** If `Hⁿ⁺¹(G, k)` is not zero
for the trivial representation of a finite group `G` on a field `k`, there are a cocycle
`c : Gⁿ⁺¹ → k` and weights `ℓ : Gⁿ⁺¹ → k` whose pairing kills every coboundary and takes the
value `1` on `c`. -/
theorem exists_cocycle_pairing {k G : Type u} [Field k] [Group G] [Fintype G]
    (n : ℕ) (hH : Nontrivial (groupCohomology (Rep.trivial k G k) (n + 1))) :
    ∃ c ℓ : (Fin (n + 1) → G) → k, trivialCoboundary k (n + 1) c = 0 ∧
      (∀ w : (Fin n → G) → k, pairing ℓ (trivialCoboundary k n w) = 0) ∧ pairing ℓ c = 1 := by
  classical
  set A := Rep.trivial k G k
  obtain ⟨x, hx⟩ := exists_ne (0 : groupCohomology A (n + 1))
  obtain ⟨y, rfl⟩ : ∃ y, (groupCohomology.π A (n + 1)).hom y = x :=
    groupCohomology_induction_on (C := fun x => ∃ y, (groupCohomology.π A (n + 1)).hom y = x) x
      fun y => ⟨y, rfl⟩
  set c : (Fin (n + 1) → G) → k := (iCocycles A (n + 1)).hom y
  have hd : ∀ (m : ℕ) (w : (Fin m → G) → k),
      ((inhomogeneousCochains A).d m (m + 1)).hom w = trivialCoboundary k m w := by
    intro m w
    ext g
    rw [inhomogeneousCochains.d_def]
    exact d_trivial_apply m w g
  have hc : trivialCoboundary k (n + 1) c = 0 := by
    rw [← hd]
    have h := congrArg (fun φ => φ.hom y) ((inhomogeneousCochains A).iCycles_d (n + 1) (n + 2))
    exact h
  let P : Submodule k ((Fin (n + 1) → G) → k) :=
    LinearMap.range ((inhomogeneousCochains A).d n (n + 1)).hom
  have hcP : c ∉ P := by
    rintro ⟨w, hw⟩
    apply hx
    have hy : y = ((inhomogeneousCochains A).toCycles n (n + 1)).hom w := by
      apply (ModuleCat.mono_iff_injective ((inhomogeneousCochains A).iCycles (n + 1))).1
        inferInstance
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.toCycles_i]
      exact hw.symm
    rw [hy, ← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    change ((inhomogeneousCochains A).toCycles n (n + 1) ≫
      (inhomogeneousCochains A).homologyπ (n + 1)).hom w = 0
    rw [HomologicalComplex.toCycles_comp_homologyπ]
    rfl
  obtain ⟨φ, hφc, hφP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hcP inferInstance
  have hpair : ∀ v, pairing (fun t => (φ c)⁻¹ * φ (Pi.single t 1)) v = (φ c)⁻¹ * φ v := by
    intro v
    rw [← pairing_eq_dual_apply φ v]
    simp only [pairing, smul_eq_mul, Finset.mul_sum, mul_assoc]
  refine ⟨c, fun t => (φ c)⁻¹ * φ (Pi.single t 1), hc, fun w => ?_, ?_⟩
  · rw [hpair, ← hd]
    have h : φ (((inhomogeneousCochains A).d n (n + 1)).hom w) ∈ P.map φ :=
      Submodule.mem_map_of_mem ⟨w, rfl⟩
    rw [hφP, Submodule.mem_bot] at h
    rw [h, mul_zero]
  · rw [hpair, inv_mul_cancel₀ hφc]

section Module

variable [Fintype G] {k : Type*} [CommRing k] {R : Type*} [AddCommGroup R] [Module k R]

omit [Group G] in
/-- The pairing of weights with a scalar cochain times a fixed element `r` is the scalar pairing
times `r`. -/
theorem pairing_smul_right {n : ℕ} (ℓ v : (Fin n → G) → k) (r : R) :
    pairing ℓ (fun t => v t • r) = pairing ℓ v • r := by
  simp only [pairing, smul_eq_mul, Finset.sum_smul, smul_smul]

omit [Group G] in
/-- The pairing is additive in the cochain. -/
theorem pairing_add {n : ℕ} (ℓ : (Fin n → G) → k) (f f' : (Fin n → G) → R) :
    pairing ℓ (f + f') = pairing ℓ f + pairing ℓ f' := by
  simp only [pairing, Pi.add_apply, smul_add, Finset.sum_add_distrib]

omit [Group G] in
/-- The pairing is additive in the cochain, for sums. -/
theorem pairing_sum {n : ℕ} {ι : Type*} (s : Finset ι) (ℓ : (Fin n → G) → k)
    (f : ι → (Fin n → G) → R) : pairing ℓ (∑ i ∈ s, f i) = ∑ i ∈ s, pairing ℓ (f i) := by
  simp only [pairing, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

omit [Group G] in
/-- The pairing commutes with additive maps that are `k`-linear. -/
theorem pairing_comp {R' : Type*} [AddCommGroup R'] [Module k R'] (φ : R →ₗ[k] R') {n : ℕ}
    (ℓ : (Fin n → G) → k) (f : (Fin n → G) → R) : pairing ℓ (φ ∘ f) = φ (pairing ℓ f) := by
  simp [pairing, map_sum, map_smul]

/-- **Weights killing the scalar coboundaries kill the coboundaries of every `k`-module.** -/
theorem pairing_trivialCoboundary_eq_zero {n : ℕ} (ℓ : (Fin (n + 1) → G) → k)
    (hℓ : ∀ w : (Fin n → G) → k, pairing ℓ (trivialCoboundary k n w) = 0)
    (w : (Fin n → G) → R) : pairing ℓ (trivialCoboundary R n w) = 0 := by
  classical
  have hw : w = ∑ s, fun t => ((Pi.single s (1 : k) : (Fin n → G) → k) t) • w s := by
    ext t
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw, map_sum, pairing_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have h := trivialCoboundary_comp ((LinearMap.toSpanSingleton k R (w s)).toAddMonoidHom) n
    ((Pi.single s (1 : k) : (Fin n → G) → k))
  have h' : (fun t => ((Pi.single s (1 : k) : (Fin n → G) → k) t) • w s) =
      (LinearMap.toSpanSingleton k R (w s)).toAddMonoidHom ∘
        (Pi.single s (1 : k) : (Fin n → G) → k) := by
    ext t
    simp
  rw [h', h]
  change pairing ℓ (fun t =>
    (trivialCoboundary k n ((Pi.single s (1 : k) : (Fin n → G) → k)) t) • w s) = 0
  rw [pairing_smul_right, hℓ, zero_smul]

omit [Fintype G] in
/-- **A scalar cocycle times an element is a cocycle.** -/
theorem trivialCoboundary_smul_right_eq_zero {n : ℕ} (c : (Fin n → G) → k)
    (hc : trivialCoboundary k n c = 0) (r : R) :
    trivialCoboundary R n (fun t => c t • r) = 0 := by
  have h := trivialCoboundary_comp ((LinearMap.toSpanSingleton k R r).toAddMonoidHom) n c
  have h' : (fun t => c t • r) = (LinearMap.toSpanSingleton k R r).toAddMonoidHom ∘ c := by
    ext t
    simp
  rw [h', h, hc]
  ext t
  simp

omit [Group G] in
/-- **The pairing sends `c · r` to `r`** when it sends `c` to `1`. -/
theorem pairing_smul_right_of_eq_one {n : ℕ} (ℓ c : (Fin n → G) → k) (hc : pairing ℓ c = 1)
    (r : R) : pairing ℓ (fun t => c t • r) = r := by
  rw [pairing_smul_right, hc, one_smul]

end Module

end Stacks.GroupCohomology.TrivialCochains

end
