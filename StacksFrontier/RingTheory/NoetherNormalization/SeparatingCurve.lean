module

public import Mathlib.Algebra.CharP.Algebra
public import StacksFrontier.RingTheory.Derivation.SeparatingElement
public import StacksFrontier.RingTheory.NoetherNormalization
public import StacksFrontier.RingTheory.NoetherNormalization.NagataOneVariable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A separating finite Noether normalization of a curve in characteristic `p`

Let `K` be a field of characteristic `p` and `S` a finitely generated `K`-algebra of dimension
one whose differentials do not vanish at any minimal prime (for instance `S` smooth over `K` of
relative dimension one). Then there is `t ∈ S` such that `K[X] → S`, `X ↦ t`, is finite and `dt`
does not vanish at any minimal prime of `S`: `t` is a finite and separating coordinate on every
component of `Spec S`.

Noether normalization (Stacks 00OY) gives a finite `K[t₀] → S`; there is `u` whose differential
is nonzero at every minimal prime (`KaehlerDifferential.exists_forall_minimalPrimes_ne_zero`), and
`t = u - t₀ ^ N` with `N` a large multiple of `p` is finite over `K` by Nagata's change of variable
(`Polynomial.finite_aeval_sub_pow_of_finite`) and has `dt = du`, since
`d(t₀ ^ N) = N t₀ ^ (N - 1) dt₀` vanishes. This produces the divisor of a relative Noether
normalization, finite étale over the base, along which the Gysin map of `R² g_!` is taken in
the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Polynomial.exists_finite_aeval_forall_minimalPrimes_ne_zero`.
-/

@[expose] public section

open Polynomial TensorProduct

namespace Polynomial

/-- **A separating finite Noether normalization of a curve** in characteristic `p`. -/
@[sga "1 XIII 2.13" "more general"]
theorem exists_finite_aeval_forall_minimalPrimes_ne_zero (K S : Type*) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [CommRing S] [Nontrivial S] [Algebra K S] [Algebra.FiniteType K S]
    (hdim : ringKrullDim S = 1)
    (hΩ : ∀ P : PrimeSpectrum S, P.asIdeal ∈ minimalPrimes S →
      Nontrivial (P.asIdeal.ResidueField ⊗[S] Ω[S⁄K])) :
    ∃ t : S, (aeval t : K[X] →ₐ[K] S).Finite ∧ ∀ P : PrimeSpectrum S,
      P.asIdeal ∈ minimalPrimes S →
        (1 : P.asIdeal.ResidueField) ⊗ₜ[S] KaehlerDifferential.D K S t ≠ 0 := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  have : CharP S p := charP_of_injective_algebraMap (algebraMap K S).injective p
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- a finite `K[t₀] → S`
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra K S).FG)
  obtain ⟨r, y, -, -, hfin, hr⟩ :=
    exists_finite_inj_aeval_ringKrullDim_eq_of_adjoin_eq_top K s.finite_toSet hs
  have hr1 : r = 1 := by
    rw [hdim] at hr
    exact_mod_cast hr.symm
  subst hr1
  set t₀ := y 0
  have hcomp : (aeval t₀ : K[X] →ₐ[K] S) =
      (MvPolynomial.aeval y).comp (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 1) K)) := by
    refine Polynomial.algHom_ext ?_
    simp [t₀]
  have hsurj : Function.Surjective
      (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 1) K) : K[X] →ₐ[K] _) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval, eq_top_iff,
      ← MvPolynomial.adjoin_range_X, Set.range_unique]
    rfl
  have hfin₀ : (aeval t₀ : K[X] →ₐ[K] S).Finite := by
    rw [hcomp]
    exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ hsurj)
  -- a separating `u`, and `t = u - t₀ ^ N` with `p ∣ N`
  obtain ⟨u, hu⟩ := KaehlerDifferential.exists_forall_minimalPrimes_ne_zero K S p hΩ
  obtain ⟨N₀, hN₀⟩ := finite_aeval_sub_pow_of_finite hfin₀ u
  set N := p * (N₀ + 1)
  have hNle : N₀ ≤ N :=
    le_trans (Nat.le_succ N₀) (Nat.le_mul_of_pos_left _ (Fact.out : p.Prime).pos)
  refine ⟨u - t₀ ^ N, hN₀ N hNle, fun P hP => ?_⟩
  have hD : KaehlerDifferential.D K S (u - t₀ ^ N) = KaehlerDifferential.D K S u := by
    rw [map_sub, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S,
      (CharP.cast_eq_zero_iff S p N).2 (dvd_mul_right p _), zero_smul, sub_zero]
  rw [hD]
  exact hu P hP

end Polynomial
