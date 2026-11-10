module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Nagata's change of variable in one variable

Let `K` be a field and `R` a `K`-algebra which is finite over `K[t₀]` for some `t₀ ∈ R`. For every
`u ∈ R` and every large enough `N`, `R` is finite over `K[u - t₀ ^ N]`. Indeed `u` is integral
over `K[t₀]`: `∑_{j ≤ e} a_j(t₀) u ^ j = 0` with `a_e = 1` and `deg a_j ≤ D`. For `N > D` the
polynomial `Q(T) = ∑_j a_j(T) (S + T ^ N) ^ j` over `K[S]` is monic of degree `N e` in `T`, the
term `j = e` being `(S + T ^ N) ^ e` and the others of degree `≤ D + N (e - 1) < N e`, and
`Q(t₀) = 0` at `S = u - t₀ ^ N`. So `t₀`, hence `K[t₀]`, hence `R`, is integral over
`K[u - t₀ ^ N]`, and `R` is of finite type over it.

In characteristic `p`, taking `p ∣ N` gives `d(u - t₀ ^ N) = du`, so a finite normalization of a
smooth curve can be made separating by choosing `u` separating.

## Main definitions

* `Polynomial.nagataSubst`: the polynomial `Q`.

## Main results

* `Polynomial.eval₂_nagataSubst`, `Polynomial.monic_nagataSubst`: `Q(t₀) = 0` and `Q` is monic.
* `Polynomial.finite_aeval_sub_pow_of_finite`: the change of variable.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- The polynomial `Q(T) = ∑_j a_j(T) (S + T ^ N) ^ j` over `K[S]` attached to
`q = ∑_j a_j Y ^ j ∈ K[X][Y]`. -/
noncomputable def nagataSubst (q : K[X][X]) (N : ℕ) : K[X][X] :=
  q.eval₂ (mapRingHom (C : K →+* K[X])) (C X + X ^ N)

/-- Evaluating `Q` at `T = t₀`, `S = u - t₀ ^ N` gives `q(t₀, u)`. -/
theorem eval₂_nagataSubst (q : K[X][X]) (N : ℕ) (t₀ u : R) :
    (nagataSubst q N).eval₂ (aeval (u - t₀ ^ N) : K[X] →ₐ[K] R).toRingHom t₀ =
      q.eval₂ (aeval t₀ : K[X] →ₐ[K] R).toRingHom u := by
  set ψ : K[X][X] →+* R := eval₂RingHom (aeval (u - t₀ ^ N) : K[X] →ₐ[K] R).toRingHom t₀
  change ψ (nagataSubst q N) = _
  rw [nagataSubst, hom_eval₂]
  have hcomp : ψ.comp (mapRingHom (C : K →+* K[X])) = (aeval t₀ : K[X] →ₐ[K] R).toRingHom := by
    refine ringHom_ext (fun c => ?_) ?_ <;> simp [ψ]
  have hy : ψ (C X + X ^ N) = u := by simp [ψ]
  rw [hcomp, hy]

/-- `Q(T) = ∑_j a_j(T) (S + T ^ N) ^ j` is monic in `T` when `q` is monic in `Y` and every `a_j`
has degree less than `N`. -/
theorem monic_nagataSubst {q : K[X][X]} (hq : q.Monic) {N : ℕ}
    (hN : ∀ j, (q.coeff j).natDegree < N) : (nagataSubst q N).Monic := by
  have hN0 : N ≠ 0 := by have := hN 0; omega
  rw [nagataSubst, add_comm (C X)]
  set y : K[X][X] := X ^ N + C X
  have hy : y.Monic := monic_X_pow_add_C _ hN0
  have hydeg : y.natDegree = N := natDegree_X_pow_add_C
  set e := q.natDegree
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul]
  refine Monic.add_of_right (hy.pow e) ?_
  rw [degree_eq_natDegree (hy.pow e).ne_zero, hy.natDegree_pow, hydeg]
  refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j hj => ?_)
  have h1 : (map (C : K →+* K[X]) (q.coeff j) * y ^ j).natDegree ≤
      (q.coeff j).natDegree + j * N := by
    refine natDegree_mul_le.trans (add_le_add natDegree_map_le ?_)
    rw [hy.natDegree_pow, hydeg]
  have h2 : (j + 1) * N ≤ e * N := Nat.mul_le_mul_right N (Finset.mem_range.1 hj)
  rw [Nat.succ_mul] at h2
  have h3 := hN j
  refine degree_le_natDegree.trans_lt ?_
  exact_mod_cast (show (map (C : K →+* K[X]) (q.coeff j) * y ^ j).natDegree < e * N by omega)

/-- **Nagata's change of variable in one variable**: if `k[X] → R`, `X ↦ t₀`, is finite, then for
every `u ∈ R` there is `N₀` such that `k[X] → R`, `X ↦ u - t₀ ^ N`, is finite for every
`N ≥ N₀`. -/
theorem finite_aeval_sub_pow_of_finite {t₀ : R} (hfin : (aeval t₀ : K[X] →ₐ[K] R).Finite)
    (u : R) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (aeval (u - t₀ ^ N) : K[X] →ₐ[K] R).Finite := by
  have hint₀ : (aeval t₀ : K[X] →ₐ[K] R).toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hfin
  obtain ⟨q, hqm, hqu⟩ := hint₀ u
  refine ⟨(q.support.sup fun j => (q.coeff j).natDegree) + 1, fun N hN => ?_⟩
  have hNq : ∀ j, (q.coeff j).natDegree < N := by
    intro j
    by_cases hj : j ∈ q.support
    · exact (Nat.lt_succ_of_le
        (Finset.le_sup (f := fun j => (q.coeff j).natDegree) hj)).trans_le hN
    · rw [notMem_support_iff.1 hj, natDegree_zero]
      omega
  set s := u - t₀ ^ N
  -- `t₀` is integral over `K[s]`
  have ht : (aeval s : K[X] →ₐ[K] R).toRingHom.IsIntegralElem t₀ :=
    ⟨nagataSubst q N, monic_nagataSubst hqm hNq, by rwa [eval₂_nagataSubst]⟩
  let : Algebra K[X] R := (aeval s : K[X] →ₐ[K] R).toRingHom.toAlgebra
  have : IsScalarTower K K[X] R := IsScalarTower.of_algebraMap_eq fun c => by
    simp [RingHom.algebraMap_toAlgebra, algebraMap_eq]
  set A := integralClosure K[X] R
  have ht₀A : t₀ ∈ A := ht
  have hA : ∀ c : K[X], aeval t₀ c ∈ A := fun c =>
    (Algebra.adjoin_le (s := {t₀}) (S := A.restrictScalars K)
      (Set.singleton_subset_iff.2 ht₀A)) (aeval_mem_adjoin_singleton K t₀)
  have hint : (aeval s : K[X] →ₐ[K] R).toRingHom.IsIntegral := by
    intro r
    obtain ⟨p, hpm, hpr⟩ := hint₀ r
    let φ : K[X] →+* A := (aeval t₀ : K[X] →ₐ[K] R).toRingHom.codRestrict A.toSubsemiring hA
    exact isIntegral_trans r (⟨p.map φ, hpm.map φ, by rwa [eval₂_map]⟩ : IsIntegral A r)
  have hft : (aeval s : K[X] →ₐ[K] R).toRingHom.FiniteType := by
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap K K[X]) ?_
    have hcomp : (aeval s : K[X] →ₐ[K] R).toRingHom.comp (algebraMap K K[X]) =
        (aeval t₀ : K[X] →ₐ[K] R).toRingHom.comp (algebraMap K K[X]) := by
      ext c
      simp [algebraMap_eq]
    rw [hcomp]
    exact (RingHom.FiniteType.of_finite hfin).comp
      (RingHom.finiteType_algebraMap.2 inferInstance)
  exact RingHom.IsIntegral.to_finite hint hft

end Polynomial
