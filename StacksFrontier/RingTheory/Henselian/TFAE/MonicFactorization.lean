module

import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.LinearAlgebra.Matrix.CommSemiring

public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Henselian.TFAE.Conditions
import all StacksFrontier.RingTheory.Henselian.TFAE.Conditions
public import StacksFrontier.RingTheory.Henselian.TFAE.Decompositions
import all StacksFrontier.RingTheory.Henselian.TFAE.Decompositions

@[expose] public section

/-!
# Characterisations of henselian local rings: lifting monic factorisations

This file continues the proof of Lemma 04GG (the statement and the plan of the proof are in the
module docstring of `StacksFrontier.RingTheory.Henselian.TFAE.Factorization`) with two ingredients
of 1 ⇒ 6:

* a coprime factorisation `f̄ = g₀h₀` of the reduction of a monic `f` into monic factors lifts to
  `R[T]` when item (8) holds (`exists_monic_mul_map_eq_of_isCoprime`): the factorisation exists
  over an étale neighbourhood of the closed point by Lemma 00UH, and the retraction of (8) brings it
  down to `R`;
* a polynomial whose reduction is monic of degree `n` cancels from a relation `f q = r v` with
  `deg r < n` and `v̄ = 1`, by Nakayama's lemma.

## Main results

* `Stacks.Henselian.Characterizations.eq_zero_of_mul_eq_mul_of_degree_lt`: if `f ∈ R[T]` has a
  unit coefficient in degree `n` and all higher coefficients in `𝔪`, and `f q = r v` with
  `deg r < n` and `v̄ = 1`, then `r = 0`.

## References

* [StacksProject 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

universe u

@[expose] public section

namespace Stacks.Henselian.Characterizations

open Polynomial IsLocalRing TensorProduct

variable (R : Type u) [CommRing R] [IsLocalRing R]
/-- **The monic case of items (4) and (6).** Let `f ∈ R[T]` be monic and let `f̄ = g₀h₀` be a
factorisation into coprime monic polynomials over `κ`. If `R` is henselian then `f = gh` in `R[T]`
with `g`, `h` monic, `ḡ = g₀` and `h̄ = h₀`.

The factorisation exists over an étale neighbourhood of the closed point by Lemma 00UH
(`Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`, Mathlib's universal
coprime factorisation ring), and item (8) retracts that neighbourhood: `τ : R' →ₐ[R] R` with
`τ⁻¹(𝔪) = Q`, and applying `Polynomial.map τ` to the factorisation over `R'` gives one over `R`.

That the two reductions are again `g₀` and `h₀` is the identity `γ ∘ μ = id`, where
`μ : κ(𝔪) → κ(Q)` is the residue field map of `R → R'` and `γ : κ(Q) → κ(𝔪)` that of `τ`: both are
`R`-algebra maps and `R → κ(𝔪)` is surjective, `𝔪` being maximal. The bridge `β : κ ≃ₐ[R] κ(𝔪)`
between `IsLocalRing.ResidueField R` and `Ideal.ResidueField (maximalIdeal R)` is the isomorphism
induced by the surjection `R → κ(𝔪)` with kernel `𝔪`. -/
@[sga "4 VIII 4.1" "(iii)"]
private theorem exists_monic_mul_map_eq_of_isCoprime (h8 : Item8 R) (f : R[X]) (hf : f.Monic)
    (g₀ h₀ : (ResidueField R)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfac : f.map (residue R) = g₀ * h₀) (hcop : IsCoprime g₀ h₀) :
    ∃ g h : R[X], g.Monic ∧ f = g * h ∧ g.map (residue R) = g₀ ∧ h.map (residue R) = h₀ := by
  classical
  have hsurjres : Function.Surjective (algebraMap R (maximalIdeal R).ResidueField) :=
    Ideal.algebraMap_residueField_surjective _
  have hkerres : RingHom.ker (algebraMap R (maximalIdeal R).ResidueField) = maximalIdeal R := by
    ext x
    simp
  let β : ResidueField R ≃ₐ[R] (maximalIdeal R).ResidueField :=
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq hkerres.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurjres)) (fun _ => rfl)
  have hβ : ∀ r : R, β (residue R r) = algebraMap R (maximalIdeal R).ResidueField r := by
    intro r
    have h := β.commutes r
    rwa [IsLocalRing.ResidueField.algebraMap_eq] at h
  have hβcomp : β.toRingHom.comp (residue R)
      = algebraMap R (maximalIdeal R).ResidueField := by
    ext r; exact hβ r
  have hmapf : f.map (algebraMap R (maximalIdeal R).ResidueField)
      = (g₀.map β.toRingHom) * (h₀.map β.toRingHom) := by
    rw [← Polynomial.map_mul, ← hfac, Polynomial.map_map, hβcomp]
  have hcop' : IsCoprime (g₀.map β.toRingHom)
      (h₀.map β.toRingHom) := by
    have h := hcop.map (Polynomial.mapRingHom β.toRingHom)
    simpa using h
  obtain ⟨R', _, _, hEt, Q, hQp, hQlo, f', g', hbij, hf'm, hg'm, hprod, -, hred1, hred2⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime
      (maximalIdeal R) f (g₀.map β.toRingHom) (h₀.map β.toRingHom)
      hf (hg₀.map _) (hh₀.map _) hmapf hcop'
  have := hQp
  have := hQlo
  have := hEt
  obtain ⟨τ, hτ, -⟩ := h8 R' hEt Q hbij
  set μ : (maximalIdeal R).ResidueField →+* Q.ResidueField :=
    (Ideal.ResidueField.mapₐ (maximalIdeal R) Q (Algebra.ofId R R')
      (Ideal.over_def Q (maximalIdeal R))).toRingHom with hμ
  set γ : Q.ResidueField →+* (maximalIdeal R).ResidueField :=
    Ideal.ResidueField.map Q (maximalIdeal R) (τ : R' →+* R) hτ.symm with hγ
  have hμa : ∀ r : R, μ (algebraMap R (maximalIdeal R).ResidueField r)
      = algebraMap R' Q.ResidueField (algebraMap R R' r) := by
    intro r
    exact Ideal.ResidueField.map_algebraMap (maximalIdeal R) Q (algebraMap R R')
      (Ideal.over_def Q (maximalIdeal R)) r
  have hγa : ∀ x : R', γ (algebraMap R' Q.ResidueField x)
      = algebraMap R (maximalIdeal R).ResidueField (τ x) :=
    fun x => Ideal.ResidueField.map_algebraMap Q (maximalIdeal R) (τ : R' →+* R) hτ.symm x
  have hcomp : γ.comp μ = RingHom.id (maximalIdeal R).ResidueField := by
    refine RingHom.ext fun x => ?_
    obtain ⟨r, rfl⟩ := hsurjres x
    rw [RingHom.comp_apply, hμa r, hγa, τ.commutes r, RingHom.id_apply]
    simp
  have key : ∀ (p : (ResidueField R)[X]) (p' : R'[X]),
      (p.map β.toRingHom).map μ = p'.map (algebraMap R' Q.ResidueField) →
      (p'.map (τ : R' →+* R)).map (residue R) = p := by
    intro p p' hp
    refine Polynomial.map_injective β.toRingHom β.injective ?_
    rw [Polynomial.map_map, hβcomp]
    calc (p'.map (τ : R' →+* R)).map (algebraMap R (maximalIdeal R).ResidueField)
        = (p'.map (algebraMap R' Q.ResidueField)).map γ := by
          rw [Polynomial.map_map, Polynomial.map_map]
          congr 1
          exact (RingHom.ext fun x => (hγa x).symm)
      _ = ((p.map β.toRingHom).map μ).map γ := by rw [hp]
      _ = p.map β.toRingHom := by
          rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  refine ⟨f'.map (τ : R' →+* R), g'.map (τ : R' →+* R), hf'm.map _, ?_, key g₀ f' hred1,
    key h₀ g' hred2⟩
  have h := congrArg (Polynomial.map (τ : R' →+* R)) hprod
  rw [Polynomial.map_map, Polynomial.map_mul, show (τ : R' →+* R).comp (algebraMap R R')
    = RingHom.id R from RingHom.ext fun r => τ.commutes r, Polynomial.map_id] at h
  exact h

/-- **Cancelling a polynomial whose reduction is monic.** Let `f ∈ R[T]` have a unit coefficient
in degree `n` and all higher coefficients in `𝔪` — the form "`f̄` is monic of degree `n`" takes
over a local ring. If `f q = r v` with `deg_T(r) < n` and `v̄ = 1`, then `r = 0` (and `q = 0`).

For `v = 1` this is the statement that `f` is a nonzerodivisor "below degree `n`": a multiple of
`f` of degree `< n` vanishes. The proof is a Nakayama argument on the finitely generated
`R`-submodule `W ⊆ R` spanned by the coefficients of `q` and of `r` together. Reading the
coefficient of `f q` in degree `n + k`, for `k` descending from `deg_T(q)`, expresses `f_n q_k` as
a combination of the `f_i q_{n+k-i}` with `i > n`, whose `f_i` lie in `𝔪`, of the `q_j` with
`j > k`, already known to lie in `𝔪W`, and of the coefficients of `r v` in degrees `≥ n`, which lie
in `𝔪W` because those of `r` vanish there and `v - 1` has coefficients in `𝔪`; so every `q_k`, and
then every `r_k`, lies in `𝔪W`. Hence `W = 𝔪W` and `W = 0`.

The tolerance for the unit factor `v` is what lets this be applied to a relation that holds only
modulo an idempotent: see `exists_monic_mul_map_eq_one`. -/
lemma eq_zero_of_mul_eq_mul_of_degree_lt {n : ℕ} {f q r v : R[X]}
    (hfu : IsUnit (f.coeff n)) (hfm : ∀ i, n < i → f.coeff i ∈ maximalIdeal R)
    (hv : v.map (residue R) = 1) (hdeg : r.degree < n) (h : f * q = r * v) :
    r = 0 := by
  classical
  set d := max q.natDegree r.natDegree with hd
  set s : Finset R :=
    ((Finset.range (d + 1)).image q.coeff) ∪ ((Finset.range (d + 1)).image r.coeff) with hs
  set W : Submodule R R := Submodule.span R (s : Set R) with hW
  have hWfg : W.FG := ⟨s, rfl⟩
  have hqW : ∀ k, q.coeff k ∈ W := by
    intro k
    rcases le_or_gt k d with hk | hk
    · exact Submodule.subset_span (by
        simp only [hs, Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
          Finset.mem_coe, Finset.mem_range]
        exact Or.inl ⟨k, by omega, rfl⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k)]
      exact W.zero_mem
  have hrW : ∀ k, r.coeff k ∈ W := by
    intro k
    rcases le_or_gt k d with hk | hk
    · exact Submodule.subset_span (by
        simp only [hs, Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
          Finset.mem_coe, Finset.mem_range]
        exact Or.inr ⟨k, by omega, rfl⟩)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : r.natDegree < k)]
      exact W.zero_mem
  set N : Submodule R R := (maximalIdeal R) • W with hN
  have hNmul : ∀ (c x : R), x ∈ N → c * x ∈ N := by
    intro c x hx
    rw [← smul_eq_mul]
    exact N.smul_mem c hx
  have huv : ∀ i, (v - 1).coeff i ∈ maximalIdeal R := by
    refine coeff_mem_maximalIdeal_of_map_eq_zero R ?_
    rw [Polynomial.map_sub, hv, Polynomial.map_one, sub_self]
  have hterm : ∀ i j : ℕ, r.coeff i * (v - 1).coeff j ∈ N := by
    intro i j
    rw [mul_comm, ← smul_eq_mul]
    exact Submodule.smul_mem_smul (huv j) (hrW i)
  have hrv : ∀ j : ℕ, n ≤ j → (r * v).coeff j ∈ N := by
    intro j hj
    have hsplit : r * v = r + r * (v - 1) := by ring
    have hr0 : r.coeff j = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg ?_)
      exact_mod_cast hj
    rw [hsplit, Polynomial.coeff_add, hr0, zero_add, Polynomial.coeff_mul]
    exact Submodule.sum_mem _ fun x _ => hterm x.1 x.2
  have key : ∀ jj k : ℕ, d < k + jj → q.coeff k ∈ N := by
    intro jj
    induction jj with
    | zero =>
        intro k hk
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < k)]
        exact N.zero_mem
    | succ j ih =>
        intro k hk
        rcases lt_or_ge d (k + j) with h1 | h1
        · exact ih k h1
        · have hdk : d = k + j := by omega
          have hcoef : (f * q).coeff (n + k) ∈ N := by
            rw [h]; exact hrv _ (by omega)
          have hmem : ((n, k) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (n + k) := by simp
          rw [Polynomial.coeff_mul,
            ← Finset.sum_erase_add _ (fun x : ℕ × ℕ => f.coeff x.1 * q.coeff x.2) hmem] at hcoef
          have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + k)).erase (n, k),
              f.coeff x.1 * q.coeff x.2 ∈ N := by
            refine Submodule.sum_mem _ fun x hx => ?_
            have hxa : x.1 + x.2 = n + k :=
              Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_of_mem_erase hx)
            have hxne : x ≠ (n, k) := Finset.ne_of_mem_erase hx
            rcases lt_trichotomy x.1 n with h2 | h2 | h2
            · exact hNmul _ _ (ih x.2 (by omega))
            · exact absurd (Prod.ext h2 (by omega)) hxne
            · rw [← smul_eq_mul]
              exact Submodule.smul_mem_smul (hfm x.1 h2) (hqW x.2)
          have hprod : f.coeff n * q.coeff k ∈ N := by
            have hsub := Submodule.sub_mem _ hcoef hrest
            simpa using hsub
          have hfin := hNmul (↑hfu.unit⁻¹ : R) _ hprod
          rwa [show (↑hfu.unit⁻¹ : R) * (f.coeff n * q.coeff k) = q.coeff k by
            rw [← mul_assoc, hfu.val_inv_mul, one_mul]] at hfin
  have hqN : ∀ k, q.coeff k ∈ N := fun k => key (d + 1) k (by omega)
  have hrN : ∀ k, r.coeff k ∈ N := by
    intro k
    have hre : r = f * q - r * (v - 1) := by
      have hsplit : r * v = r + r * (v - 1) := by ring
      rw [h, hsplit]; ring
    rw [hre, Polynomial.coeff_sub]
    refine Submodule.sub_mem _ ?_ ?_
    · rw [Polynomial.coeff_mul]
      exact Submodule.sum_mem _ fun x _ => hNmul _ _ (hqN x.2)
    · rw [Polynomial.coeff_mul]
      exact Submodule.sum_mem _ fun x _ => hterm x.1 x.2
  have hWle : W ≤ (maximalIdeal R) • W := by
    rw [hW, Submodule.span_le]
    intro x hx
    simp only [hs, Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, Finset.mem_range] at hx
    rcases hx with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
    · exact hqN k
    · exact hrN k
  have hW0 : W = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hWfg hWle
      ((IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)
  ext k
  have hk := hrW k
  rw [hW0] at hk
  simpa using hk

end Stacks.Henselian.Characterizations
