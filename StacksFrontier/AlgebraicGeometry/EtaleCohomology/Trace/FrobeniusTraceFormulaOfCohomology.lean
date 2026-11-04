module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeightsFromTraceGrowth

/-!
# The Frobenius trace formula from the cohomology of a curve

The cohomology-free form `Stacks.EtaleCohomology.SatisfiesFrobeniusTraceFormula` of the trace
formula, used in the proof that the constituents of an `ι`-real representation are `ι`-pure
(Weil II 1.5.1), follows from the ℓ-adic trace formula of a curve
`∑_{deg y ∣ n} deg y · tr(τ(F_y)^{n / deg y}) = ∑_{i ≤ 2} (-1)^i tr(π^n | Hⁱ_c)`
together with `H⁰_c = 0` and `H²_c ≅ (geometric coinvariants)(-1)`, compatibly with `π`: take
for `A` the roots of the characteristic polynomial of `π` on `H²_c` and for `B` those on `H¹_c`.

## Main results

* `Stacks.EtaleCohomology.isRoot_charpoly_div_of_isRoot_charpoly_smul`.
* `Stacks.EtaleCohomology.satisfiesFrobeniusTraceFormula_of_trace_eq`.
-/

@[expose] public noncomputable section

open Polynomial Matrix

namespace Stacks.EtaleCohomology

variable {F : Type*} [Field F]

/-- The roots of the characteristic polynomial of `c • f` are `c` times those of `f`. -/
public theorem isRoot_charpoly_div_of_isRoot_charpoly_smul {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (ι : F →+* ℂ) (f : Module.End F V) {c : F} (hc : c ≠ 0)
    {a : ℂ} (ha : ((c • f).charpoly.map ι).IsRoot a) : (f.charpoly.map ι).IsRoot (a / ι c) := by
  classical
  set b := Module.finBasis F V
  set M := LinearMap.toMatrix b b f
  have hcM : LinearMap.toMatrix b b (c • f) = c • M := map_smul _ _ _
  have hmap : (c • M).map ι = ι c • M.map ι := by
    ext i j
    simp
  rw [← LinearMap.charpoly_toMatrix (c • f) b, hcM, ← Matrix.charpoly_map, hmap,
    ← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at ha
  rw [← LinearMap.charpoly_toMatrix f b, ← Matrix.charpoly_map, ← Matrix.charpoly_toLin',
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  refine ⟨?_, hv.2⟩
  calc (M.map ι) *ᵥ v = (ι c)⁻¹ • (ι c • ((M.map ι) *ᵥ v)) := by
        rw [smul_smul, inv_mul_cancel₀ ((map_ne_zero ι).mpr hc), one_smul]
    _ = (a / ι c) • v := by rw [← Matrix.smul_mulVec, hv.1, smul_smul, div_eq_inv_mul]

variable {Γ : Type*} [Group Γ] {m : ℕ} (H : Subgroup Γ) [H.Normal]

/-- **The Frobenius trace formula from the cohomology of a curve.**  Let `Hc 0`, `Hc 1`, `Hc 2`
be finite-dimensional with endomorphisms `π i`, `Hc 0 = 0`, and `Hc 2` isomorphic to the
`H`-coinvariants of `τ` with `π 2` corresponding to `q` times the Frobenius `φ`.  If
`∑_{deg y ∣ n} deg y · tr(τ(F_y)^{n / deg y}) = ∑_{i < 3} (-1)^i tr(π i ^ n)` for every `n ≥ 1`,
then `τ` satisfies the Frobenius trace formula along every `ι`. -/
public theorem satisfiesFrobeniusTraceFormula_of_trace_eq (q : ℕ) (hq : (q : F) ≠ 0)
    (ι : F →+* ℂ) (φ : Γ) {Y : Type*} (Fr : Y → Γ) (deg : Y → ℕ) (τ : Γ →* GL (Fin m) F)
    (Hc : ℕ → Type*) [∀ i, AddCommGroup (Hc i)] [∀ i, Module F (Hc i)]
    [∀ i, FiniteDimensional F (Hc i)] (π : ∀ i, Module.End F (Hc i))
    (h0 : Subsingleton (Hc 0))
    (e : Hc 2 ≃ₗ[F] Representation.Coinvariants
      ((matrixRepresentation τ).comp H.subtype : Representation F H (Fin m → F)))
    (he : ∀ v, e (π 2 v) = (q : F) • coinvariantsFrobenius H τ φ (e v))
    (htr : ∀ n : ℕ, 0 < n →
      ∑ᶠ (y : Y) (_ : deg y ∣ n), (deg y : F) * ((τ (Fr y) : Matrix (Fin m) (Fin m) F) ^
        (n / deg y)).trace =
      ∑ i ∈ Finset.range 3, (-1) ^ i * LinearMap.trace F (Hc i) (π i ^ n)) :
    SatisfiesFrobeniusTraceFormula (q : ℝ) ι H φ Fr deg τ := by
  classical
  set g := coinvariantsFrobenius H τ φ
  have hπ2 : π 2 = e.symm.conj ((q : F) • g) := by
    ext v
    apply e.injective
    simp [LinearEquiv.conj_apply, he]
  refine ⟨((π 2).charpoly.map ι).roots, ((π 1).charpoly.map ι).roots, fun a ha => ?_,
    fun n hn => ?_⟩
  · have ha' : (((q : F) • g).charpoly.map ι).IsRoot a := by
      have := (Polynomial.mem_roots ((LinearMap.charpoly_monic _).map ι).ne_zero).mp ha
      rwa [hπ2, LinearEquiv.charpoly_conj] at this
    have h := isRoot_charpoly_div_of_isRoot_charpoly_smul ι g hq ha'
    rwa [map_natCast, ← Complex.ofReal_natCast] at h
  · rw [htr n hn, map_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_mul, map_pow,
      map_neg, map_one, pow_zero, pow_one, one_mul, neg_mul]
    have hz : π 0 ^ n = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hz, map_zero, map_zero, map_trace_pow_eq_sum_roots_map_pow,
      map_trace_pow_eq_sum_roots_map_pow]
    ring

end Stacks.EtaleCohomology

end
