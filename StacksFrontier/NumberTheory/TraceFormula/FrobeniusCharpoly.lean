module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.MvPolynomial
public import StacksFrontier.NumberTheory.Drinfeld.Chebotarev
public import StacksFrontier.NumberTheory.TraceFormula.GeometricMonodromyFiniteness

/-!
# Characteristic polynomials of Frobenius with constant coefficients

Let `ρ : π₁(X) → GL_n(F_ℓ[[t]])` be a continuous representation of the étale fundamental group of
a smooth, proper, geometrically irreducible curve over a finite field. If the coefficients of the
characteristic polynomials of `ρ` at all Frobenius elements are algebraic over `F_ℓ`, then the
characteristic polynomial of `ρ(g)` has constant coefficients (they lie in `F_ℓ ⊆ F_ℓ[[t]]`) for
every `g ∈ π₁(X)`, and so also for every `g` in the geometric fundamental group.

Indeed `F_ℓ` is algebraically closed in `F_ℓ[[t]]`
(`PowerSeries.eq_C_constantCoeff_of_isIntegral`), the coefficients of the characteristic
polynomial are continuous functions of the matrix (through the universal characteristic
polynomial `Matrix.charpoly.univ`), the constant power series form a closed subset, and the
Frobenius elements are dense (Chebotarev, `AlgebraicGeometry.dense_frobeniusElements_compl`).

## Main results

* `PowerSeries.eq_C_constantCoeff_of_isIntegral` — an element of `F_ℓ[[t]]` integral over `F_ℓ`
  is constant.
* `Stacks.TraceFormula.continuous_charpoly_coeff` — coefficients of the characteristic polynomial
  are continuous.
* `Stacks.TraceFormula.charpoly_coeff_mem_range_C_of_frobenius` — constancy at Frobenius elements
  propagates to the whole fundamental group.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped PowerSeries.WithPiTopology

namespace PowerSeries

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- An element of `F_ℓ[[t]]` which is integral over `F_ℓ` is a constant power series: the
algebra it generates is finite, so `a ^ ℓ ^ i = a ^ ℓ ^ j` for some `i < j`; then
`b = a - a₀` satisfies `c = c ^ ℓ ^ (j - i)` for `c = b ^ ℓ ^ i`, which is divisible by every
power of `X`. -/
theorem eq_C_constantCoeff_of_isIntegral {a : PowerSeries (ZMod ℓ)}
    (ha : IsIntegral (ZMod ℓ) a) : a = C (constantCoeff a) := by
  classical
  have hℓ : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have : CharP (PowerSeries (ZMod ℓ)) ℓ :=
    charP_of_injective_algebraMap (algebraMap (ZMod ℓ) (PowerSeries (ZMod ℓ))).injective ℓ
  set S := Algebra.adjoin (ZMod ℓ) ({a} : Set (PowerSeries (ZMod ℓ)))
  have : Module.Finite (ZMod ℓ) S := Algebra.finite_adjoin_simple_of_isIntegral ha
  have : Finite S := Module.finite_of_finite (ZMod ℓ)
  let F : ℕ → S := fun j => ⟨a ^ ℓ ^ j, pow_mem (Algebra.self_mem_adjoin_singleton _ a) _⟩
  obtain ⟨i, j, hij, hF⟩ := Finite.exists_ne_map_eq_of_infinite F
  have key : ∀ {i j : ℕ}, i < j → a ^ ℓ ^ i = a ^ ℓ ^ j → a = C (constantCoeff a) := by
    intro i j hlt heq
    set c₀ := constantCoeff a
    set b := a - C c₀ with hb
    have hpow : ∀ m, b ^ ℓ ^ m = a ^ ℓ ^ m - C c₀ := fun m => by
      rw [hb, sub_pow_char_pow, ← map_pow, ZMod.pow_card_pow]
    have hc : b ^ ℓ ^ i = (b ^ ℓ ^ i) ^ ℓ ^ (j - i) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hlt.le, hpow, hpow, heq]
    have hXb : X ∣ b := by
      rw [X_dvd_iff, hb, map_sub, constantCoeff_C, sub_self]
    set c := b ^ ℓ ^ i
    have hXc : X ∣ c := dvd_pow hXb (pow_ne_zero _ (by omega))
    have hq : 2 ≤ ℓ ^ (j - i) :=
      le_trans hℓ (Nat.le_self_pow (by omega) _)
    have hall : ∀ m, X ^ m ∣ c := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have h2 : X ^ (m + 1) ∣ c * c := by
          rw [pow_succ]
          exact mul_dvd_mul ih hXc
        have h3 : c * c ∣ c ^ ℓ ^ (j - i) := by
          rw [← sq]
          exact pow_dvd_pow c hq
        rw [hc]
        exact h2.trans h3
    have hc0 : c = 0 := by
      ext m
      exact (X_pow_dvd_iff.mp (hall (m + 1))) m (Nat.lt_succ_self m)
    have hb0 : b = 0 := pow_eq_zero_iff (pow_ne_zero _ (by omega)) |>.mp hc0
    exact sub_eq_zero.mp hb0
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h (congrArg Subtype.val hF)
  · exact key h (congrArg Subtype.val hF).symm

/-- The constant power series form a closed subset of `F_ℓ[[t]]` with its coefficientwise
topology. -/
theorem isClosed_range_C : IsClosed (Set.range (C (R := ZMod ℓ))) := by
  have : Set.range (C (R := ZMod ℓ)) = ⋂ m : ℕ, {a | coeff (m + 1) a = 0} := by
    ext a
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨?_, fun h => ⟨constantCoeff a, ?_⟩⟩
    · rintro ⟨r, rfl⟩ m
      simp
    · ext m
      rcases m with _ | m
      · simp
      · simp [h m]
  rw [this]
  exact isClosed_iInter fun m => isClosed_eq (WithPiTopology.continuous_coeff _ _) continuous_const

end PowerSeries

namespace Stacks.TraceFormula

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : Type*}
  [Fintype n] [DecidableEq n]

/-- Each coefficient of the characteristic polynomial is a continuous function of the matrix: it
is the evaluation at the entries of a coefficient of the universal characteristic polynomial. -/
theorem continuous_charpoly_coeff (i : ℕ) :
    Continuous fun A : Matrix n n R => A.charpoly.coeff i := by
  have h : (fun A : Matrix n n R => A.charpoly.coeff i) = fun A =>
      MvPolynomial.eval (fun ij : n × n => A ij.1 ij.2) ((Matrix.charpoly.univ R n).coeff i) := by
    funext A
    have := Matrix.charpoly.univ_coeff_eval₂Hom (R := R) n (RingHom.id R)
      (fun ij : n × n => A ij.1 ij.2) i
    rw [MvPolynomial.coe_eval₂Hom] at this
    exact (this.trans (by congr)).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun ij =>
    (continuous_apply ij.2).comp (continuous_apply ij.1))

variable {k : Type*} [Field k] [Finite k] {X : Scheme} [ConnectedSpace X]
  {ℓ : ℕ} [Fact ℓ.Prime] {m : ℕ}

/-- **Constancy at Frobenius propagates.** For a smooth, proper, geometrically irreducible curve
over a finite field and a continuous representation `ρ : π₁(X) → GL_m(F_ℓ[[t]])`, if the
coefficients of the characteristic polynomials of `ρ` at all Frobenius elements are integral
over `F_ℓ`, then for every `g ∈ π₁(X)` the characteristic polynomial of `ρ(g)` has constant
coefficients. -/
theorem charpoly_coeff_mem_range_C_of_frobenius (f : X ⟶ Spec (.of k)) [IsCurve k f]
    [Smooth f] [IsProper f] [GeometricallyIrreducible f] (base : GeometricPoint X)
    (ρ : EtaleFundamentalGroup X base →ₜ*
      Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ)))
    (hρ : ∀ F ∈ frobeniusElements base Set.univ, ∀ i,
      IsIntegral (ZMod ℓ) ((ρ F : Matrix (Fin m) (Fin m) (PowerSeries (ZMod ℓ))).charpoly.coeff i))
    (g : EtaleFundamentalGroup X base) (i : ℕ) :
    (ρ g : Matrix (Fin m) (Fin m) (PowerSeries (ZMod ℓ))).charpoly.coeff i ∈
      Set.range (PowerSeries.C (R := ZMod ℓ)) := by
  have hdense : Dense (frobeniusElements base (∅ : Set (closedPoints X))ᶜ) :=
    dense_frobeniusElements_compl f base Set.finite_empty
  rw [Set.compl_empty] at hdense
  have hcont : Continuous fun γ : EtaleFundamentalGroup X base =>
      (ρ γ : Matrix (Fin m) (Fin m) (PowerSeries (ZMod ℓ))).charpoly.coeff i :=
    (continuous_charpoly_coeff i).comp (Units.continuous_val.comp ρ.continuous_toFun)
  refine hdense.induction (fun F hF => ⟨_, (PowerSeries.eq_C_constantCoeff_of_isIntegral
    (hρ F hF i)).symm⟩) (PowerSeries.isClosed_range_C.preimage hcont) g

end Stacks.TraceFormula

end
