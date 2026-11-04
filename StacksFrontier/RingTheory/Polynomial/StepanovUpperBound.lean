module

public import StacksFrontier.RingTheory.Polynomial.CurveDerivation
public import StacksFrontier.RingTheory.Polynomial.PowerSeriesBranch
public import StacksFrontier.RingTheory.Polynomial.ResultantWeightedDegree
public import StacksFrontier.RingTheory.Polynomial.PlaneCurveIntersection
public import StacksFrontier.RingTheory.PowerSeries.OrderOfDerivative
public import StacksFrontier.RingTheory.PowerSeries.FrobeniusIndependence
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Stepanov's upper bound for the points of a plane curve

Let `K` be an algebraically closed field of characteristic `p`, `q = p ^ e`, and let `Ψ ∈ K[X][Y]`
be monic and irreducible of `Y`-degree `m` with `∂Ψ/∂Y ≠ 0`. Let `R, D ∈ K[X][Y]` describe a
(possibly twisted) Frobenius: consider the points `P = (a, b)` of `Ψ = 0` with
`∂Ψ/∂Y (P) ≠ 0`, `a ^ q = a`, `D(P) ≠ 0` and `D(P) b ^ q = R(P)`. For `R = Y` and `D = 1` these
are the smooth `𝔽_q`-points of the curve. Stepanov's method, in the form combining Bombieri's
`ρ`-th powers (`ρ = p ^ ⌊e/2⌋`) with derivatives of order `< p` along the curve, bounds the number
of such points by `q + O(√q)`, the implied constant depending only on `m`, the weight `w` of `Ψ`
and the degrees of `R` and `D`.

## Main results

* `Polynomial.Bivariate.le_order_branchEval_sum_mul_pow`: the auxiliary function vanishes to
  order `k` at each point.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- If the power series `β` has constant coefficient `b`, then the constant coefficient of
`branchEval a β g` is the value `g(a, b)`. -/
theorem constantCoeff_branchEval {a b : K} {β : PowerSeries K}
    (hβ0 : PowerSeries.constantCoeff β = b) (g : K[X][Y]) :
    PowerSeries.constantCoeff (branchEval a β g) = g.evalEval a b := by
  rw [branchEval_apply, constantCoeff_eval_map_aeval_C_add_X, hβ0]

/-- The twisted derivative `G ↦ u * G'` as a `K`-linear map. -/
noncomputable def twistedDerivative (u : PowerSeries K) : PowerSeries K →ₗ[K] PowerSeries K :=
  LinearMap.mulLeft K u ∘ₗ (PowerSeries.derivative K).toLinearMap

/-- The `j`-th iterate of `G ↦ u * G'` is the `j`-th power of `twistedDerivative u`. -/
theorem iterate_twistedDerivative (u : PowerSeries K) (j : ℕ) (G : PowerSeries K) :
    (fun G => u * PowerSeries.derivative K G)^[j] G = (twistedDerivative u ^ j) G := by
  rw [Module.End.pow_apply]; rfl

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The inverse of the `e`-fold Frobenius is a `p ^ e`-th root. -/
private theorem pow_iterateFrobeniusEquiv_symm (e : ℕ) (x : K) :
    ((iterateFrobeniusEquiv K p e).symm x) ^ p ^ e = x := by
  have := (iterateFrobeniusEquiv K p e).apply_symm_apply x
  rwa [iterateFrobeniusEquiv_def] at this

/-- **The auxiliary function vanishes to order `k`.** Let `(a₀, b₀)` be a point of `Ψ = 0` with
`∂Ψ/∂Y ≠ 0` there, and `β` the branch through it. Let `q = p ^ (a + b)`, `ρ = p ^ a`,
`σ = p ^ b`, and suppose `F i (P) = λ · W i (P) ^ q` with `λ ≠ 0`. If for every `j < k`
(`k ≤ p`, `k ρ ≤ q`) the combination `∑ (δ_Ψ ^ j v i) ^ ρ F i` vanishes at `P`, then
`∑ v i · W i ^ σ` vanishes to order at least `k` along the branch. -/
theorem le_order_branchEval_sum_mul_pow {Ψ : K[X][Y]} {a₀ b₀ : K} {β : PowerSeries K}
    (hβ0 : PowerSeries.constantCoeff β = b₀) (hβ : branchEval a₀ β Ψ = 0)
    (hP : (derivative Ψ).evalEval a₀ b₀ ≠ 0) {ι : Type*} [Fintype ι] (v W F : ι → K[X][Y])
    {a b k : ℕ} (hk : k ≤ p) (hkq : k * p ^ a ≤ p ^ (a + b)) {lam : K} (hlam : lam ≠ 0)
    (hF : ∀ i, (F i).evalEval a₀ b₀ = lam * (W i).evalEval a₀ b₀ ^ p ^ (a + b))
    (hE : ∀ j < k, (∑ i, ((curveDeriv Ψ)^[j] (v i)) ^ p ^ a * F i).evalEval a₀ b₀ = 0) :
    (k : ℕ∞) ≤ (branchEval a₀ β (∑ i, v i * W i ^ p ^ b)).order := by
  classical
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  set ι₀ := branchEval a₀ β
  set ρ := p ^ a
  set q := p ^ (a + b)
  have hρ0 : 0 < ρ := pow_pos (Fact.out : p.Prime).pos a
  have hq : q = p ^ b * ρ := by simp only [q, ρ, pow_add, mul_comm]
  have hconst : ∀ g, PowerSeries.constantCoeff (ι₀ g) = g.evalEval a₀ b₀ :=
    constantCoeff_branchEval hβ0
  set fr := iterateFrobeniusEquiv K p a
  have hfr : ∀ x : K, (fr.symm x) ^ ρ = x := pow_iterateFrobeniusEquiv_symm p a
  set c : ι → K := fun i => (W i).evalEval a₀ b₀ ^ q
  set γ : ι → K := fun i => fr.symm (c i)
  set G : PowerSeries K := ∑ i, γ i • ι₀ (v i)
  -- `(ι₀ g) ^ ρ = ∑ ι₀ (v i) ^ ρ * ι₀ (W i) ^ q`
  have h1 : (ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ = ∑ i, ι₀ (v i) ^ ρ * ι₀ (W i) ^ q := by
    rw [← map_pow, sum_pow_char_pow, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, map_mul, map_pow, map_pow, hq, mul_comm (p ^ b)]
  -- `G ^ ρ = ∑ ι₀ (v i) ^ ρ * C (c i)`
  have h3 : G ^ ρ = ∑ i, ι₀ (v i) ^ ρ * PowerSeries.C (c i) := by
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, hfr, PowerSeries.smul_eq_C_mul, mul_comm]
  -- the difference has order at least `q`
  have hdiff : (q : ℕ∞) ≤ ((ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ - G ^ ρ).order := by
    rw [h1, h3, ← Finset.sum_sub_distrib]
    refine PowerSeries.nat_le_order _ _ fun d hd => ?_
    have hdvd : (PowerSeries.X : PowerSeries K) ^ q ∣
        ∑ i, (ι₀ (v i) ^ ρ * ι₀ (W i) ^ q - ι₀ (v i) ^ ρ * PowerSeries.C (c i)) := by
      refine Finset.dvd_sum fun i _ => ?_
      rw [← mul_sub]
      refine Dvd.dvd.mul_left ?_ _
      have hX : (PowerSeries.X : PowerSeries K) ∣ ι₀ (W i) - PowerSeries.C ((W i).evalEval a₀ b₀) :=
        PowerSeries.X_dvd_iff.mpr (by simp [hconst])
      rw [show PowerSeries.C (c i) = (PowerSeries.C ((W i).evalEval a₀ b₀)) ^ q by
        simp [c, map_pow], ← sub_pow_char_pow]
      exact pow_dvd_pow_of_dvd hX q
    exact PowerSeries.X_pow_dvd_iff.mp hdvd d hd
  -- `G` vanishes to order `k`
  have hG : (k : ℕ∞) ≤ G.order := by
    refine PowerSeries.nat_le_order_of_constantCoeff_iterate_eq_zero
      (u := ι₀ (derivative Ψ)) (by rw [hconst]; exact hP) G (fun t ht htk => ?_) fun j hj => ?_
    · intro h0
      rw [CharP.cast_eq_zero_iff K p] at h0
      exact absurd (Nat.le_of_dvd ht h0) (by omega)
    · have hit : (fun G => ι₀ (derivative Ψ) * PowerSeries.derivative K G)^[j] G =
          ∑ i, γ i • ι₀ ((curveDeriv Ψ)^[j] (v i)) := by
        rw [iterate_twistedDerivative, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← iterate_twistedDerivative, ← branchEval_iterate_curveDeriv hβ]
      rw [hit, map_sum]
      simp only [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.constantCoeff_C, hconst]
      set s := ∑ i, γ i * ((curveDeriv Ψ)^[j] (v i)).evalEval a₀ b₀
      have hs : lam * s ^ ρ = 0 := by
        rw [sum_pow_char_pow, Finset.mul_sum]
        have := hE j hj
        simp only [evalEval_finsetSum, evalEval_mul, evalEval_pow, hF] at this
        rw [← this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, hfr]
        ring
      exact pow_eq_zero_iff (n := ρ) hρ0.ne' |>.mp
        ((mul_eq_zero.mp hs).resolve_left hlam)
  -- conclude
  have hGρ : ((k * ρ : ℕ) : ℕ∞) ≤ (G ^ ρ).order := by
    rw [PowerSeries.order_pow, nsmul_eq_mul, mul_comm]
    push_cast
    exact mul_le_mul_right hG _
  have hsum : ((k * ρ : ℕ) : ℕ∞) ≤ ((ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ).order := by
    have := PowerSeries.min_order_le_order_add (G ^ ρ)
      ((ι₀ (∑ i, v i * W i ^ p ^ b)) ^ ρ - G ^ ρ)
    rw [add_sub_cancel] at this
    refine le_trans (le_min hGρ (le_trans (by exact_mod_cast hkq) hdiff)) this
  rw [PowerSeries.order_pow, nsmul_eq_mul] at hsum
  generalize (ι₀ (∑ i, v i * W i ^ p ^ b)).order = o at hsum ⊢
  cases o with
  | top => exact le_top
  | coe n =>
    have : k * ρ ≤ ρ * n := by exact_mod_cast hsum
    exact_mod_cast Nat.le_of_mul_le_mul_left (by linarith) hρ0


section Auxiliary

/-- Elements of the span of monomials `Xⁱ Yʲ` with `j < m` and `i + w j ≤ n` have `Y`-degree
`< m` and weighted degree `≤ n`. -/
theorem degree_lt_and_weightedDegreeLE_of_mem_span {ι : Type*} {f : ι → ℕ × ℕ} {m w n : ℕ}
    (hf : ∀ i, (f i).2 < m ∧ (f i).1 + w * (f i).2 ≤ n) {h : K[X][Y]}
    (hh : h ∈ Submodule.span K (Set.range fun i => (monomialXY (f i) : K[X][Y]))) :
    h.degree < m ∧ WeightedDegreeLE w n h := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨?_, WeightedDegreeLE.monomialXY (hf i).2⟩
    simp only [monomialXY]
    rw [degree_C_mul_X_pow _ (pow_ne_zero _ X_ne_zero)]
    exact_mod_cast (hf i).1
  | zero => exact ⟨by simp, WeightedDegreeLE.zero⟩
  | add x y _ _ hx hy => exact ⟨(degree_add_le _ _).trans_lt (max_lt hx.1 hy.1), hx.2.add hy.2⟩
  | smul c x _ hx => exact ⟨(degree_smul_le _ _).trans_lt hx.1, hx.2.smul c⟩

/-- Monomials attached to an injective family of exponents are linearly independent. -/
theorem eq_zero_of_sum_smul_monomialXY_eq_zero' {ι : Type*} [Fintype ι] {f : ι → ℕ × ℕ}
    (hf : Function.Injective f) {c : ι → K}
    (h : ∑ i, c i • (monomialXY (f i) : K[X][Y]) = 0) (i : ι) : c i = 0 := by
  classical
  have := congrArg (fun g : K[X][Y] => (g.coeff (f i).2).coeff (f i).1) h
  simp only [finset_sum_coeff, coeff_smul, smul_eq_mul, coeff_coeff_monomialXY, Prod.mk.eta,
    mul_ite, mul_one, mul_zero, Polynomial.coeff_zero] at this
  rwa [Finset.sum_eq_single i (fun j _ hj => if_neg (hf.ne hj)) (by simp), if_pos rfl] at this

/-- A monic irreducible `Ψ ∈ K[X][Y]` with `∂Ψ/∂Y ≠ 0` over an algebraically closed field has a
point where `∂Ψ/∂Y` does not vanish. -/
theorem exists_simple_point [IsAlgClosed K] {Ψ : K[X][Y]} (hΨ : Ψ.Monic) (hirr : Irreducible Ψ)
    (hder : derivative Ψ ≠ 0) :
    ∃ a b : K, Ψ.evalEval a b = 0 ∧ (derivative Ψ).evalEval a b ≠ 0 := by
  classical
  have hdeg : Ψ.natDegree ≠ 0 := (hΨ.natDegree_pos.mpr hirr.ne_one).ne'
  have hndvd : ¬ Ψ ∣ derivative Ψ := fun h =>
    (natDegree_derivative_lt hdeg).not_ge (natDegree_le_of_dvd h hder)
  have hres := resultant_ne_zero_of_irreducible_of_not_dvd hirr hdeg hndvd
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (resultant Ψ (derivative Ψ)).roots.toFinset
  have hra : (resultant Ψ (derivative Ψ)).eval a ≠ 0 := fun h0 =>
    ha (Multiset.mem_toFinset.mpr ((mem_roots hres).mpr h0))
  have hmon : (Ψ.map (evalRingHom a)).Monic := hΨ.map _
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root (Ψ.map (evalRingHom a))
    (by rw [degree_eq_natDegree hmon.ne_zero, hΨ.natDegree_map]; exact_mod_cast hdeg)
  have hb' : Ψ.evalEval a b = 0 := by rwa [IsRoot, map_evalRingHom_eval] at hb
  refine ⟨a, b, hb', fun h1 => hra ?_⟩
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant Ψ (derivative Ψ) le_rfl le_rfl
    (Or.inl hdeg)
  have := congrArg (evalEval a b) huv
  simpa [evalEval_add, evalEval_mul, evalEval_C, hb', h1] using this.symm

/-- Along a branch of `Ψ = 0`, a polynomial `g` with `Res_Y(Ψ, g) ≠ 0` vanishes to order at most
`deg Res_Y(Ψ, g)`. -/
theorem order_branchEval_le {Ψ g : K[X][Y]} (hΨ : Ψ.Monic) {a b : K} {β : PowerSeries K}
    (hβ0 : PowerSeries.constantCoeff β = b) (hβ : branchEval a β Ψ = 0)
    (hres : resultant Ψ g ≠ 0) :
    (branchEval a β g).order ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
  have := sum_order_le_natDegree_resultant hΨ {(a, b)} (fun _ => β)
    (fun P hP => by
      rw [Finset.mem_singleton] at hP
      subst hP
      exact ⟨hβ0, by rw [← branchEval_apply]; exact hβ⟩) hres
  simpa [branchEval_apply] using this

end Auxiliary


section Construction

/-- The monomial `Xⁱ Yʲ` indexed by `(i, j) ∈ Fin (A + 1) × Fin m`. -/
noncomputable abbrev monoFin {A m : ℕ} (x : Fin (A + 1) × Fin m) : K[X][Y] :=
  monomialXY ((x.1 : ℕ), (x.2 : ℕ))

/-- The map `Fin (A + 1) × Fin m → ℕ × ℕ` taking `(i, j)` to `((i : ℕ), (j : ℕ))` is injective. -/
theorem injective_val_prod {A m : ℕ} :
    Function.Injective fun x : Fin (A + 1) × Fin m => ((x.1 : ℕ), (x.2 : ℕ)) := by
  intro x y h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The exponents of a `monoFin` monomial satisfy `i + w j ≤ A + w (m - 1)`. -/
private theorem fin_add_mul_le {A m : ℕ} (w : ℕ) (x : Fin (A + 1) × Fin m) :
    (x.1 : ℕ) + w * (x.2 : ℕ) ≤ A + w * (m - 1) := by
  have := x.1.2; have := x.2.2
  have : w * (x.2 : ℕ) ≤ w * (m - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Elements of the span of the `monoFin` monomials have `Y`-degree `< m` and weighted degree
`≤ A + w (m - 1)`. -/
private theorem degree_lt_and_weightedDegreeLE_of_mem_span_monoFin {A m : ℕ} (w : ℕ)
    {h : K[X][Y]}
    (hh : h ∈ Submodule.span K (Set.range fun x : Fin (A + 1) × Fin m => (monoFin x : K[X][Y]))) :
    h.degree < m ∧ WeightedDegreeLE w (A + w * (m - 1)) h :=
  degree_lt_and_weightedDegreeLE_of_mem_span (f := fun x : Fin (A + 1) × Fin m => (x.1.1, x.2.1))
    (fun x => ⟨x.2.2, fin_add_mul_le w x⟩) hh

/-- The polynomial `Xⁱ Rʲ D^{m-1-j}`, whose value at a twisted Frobenius point `P` is
`D(P)^{m-1} (Xⁱ Yʲ)(P)^q`. -/
noncomputable def frobModel (R D : K[X][Y]) (m : ℕ) (x : ℕ × ℕ) : K[X][Y] :=
  C (X ^ x.1) * R ^ x.2 * D ^ (m - 1 - x.2)

/-- If `R` and `D` have weighted degree at most `r`, `x.2 < m` and `x.1 ≤ A`, then
`frobModel R D m x` has weighted degree at most `A + r (m - 1)`. -/
theorem WeightedDegreeLE.frobModel {R D : K[X][Y]} {w r m : ℕ} (hR : WeightedDegreeLE w r R)
    (hD : WeightedDegreeLE w r D) {x : ℕ × ℕ} (hx : x.2 < m) {A : ℕ} (hA : x.1 ≤ A) :
    WeightedDegreeLE w (A + r * (m - 1)) (frobModel R D m x) := by
  have h1 : WeightedDegreeLE w A (Polynomial.C (X ^ x.1) : K[X][Y]) :=
    WeightedDegreeLE.C ((natDegree_X_pow_le _).trans hA)
  refine ((h1.mul (hR.pow x.2)).mul (hD.pow (m - 1 - x.2))).mono (le_of_eq ?_)
  rw [add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (by omega), mul_comm]

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- **The auxiliary polynomial.** If the number of unknowns exceeds the number of linear
conditions, there are `v ι` in the span of the monomials `Xⁱ Yʲ` (`i ≤ aV`, `j < m`), not all
zero, such that `Ψ` divides `∑ (δ_Ψ ^ j v ι) ^ ρ · Xⁱ Rʲ D^{m-1-j}` for every `j < k`. -/
theorem exists_auxiliary {Ψ R D : K[X][Y]} (hΨ : Ψ.Monic) {m w r : ℕ} (hm : Ψ.natDegree = m)
    (hm0 : 0 < m) (hΨw : WeightedDegreeLE w (w * m) Ψ) (hR : WeightedDegreeLE w r R)
    (hD : WeightedDegreeLE w r D) {a k aV aW : ℕ}
    (hcount : k * (m * (p ^ a * (aV + w * (m - 1) + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) <
      (m * (aW + 1)) * (m * (aV + 1))) :
    ∃ v : Fin (aW + 1) × Fin m → K[X][Y],
      (∀ ι, v ι ∈ Submodule.span K (Set.range fun β : Fin (aV + 1) × Fin m => monoFin β)) ∧
      (∃ ι, v ι ≠ 0) ∧
      ∀ j < k, Ψ ∣ ∑ ι, ((curveDeriv Ψ)^[j] (v ι)) ^ p ^ a *
        frobModel R D m ((ι.1 : ℕ), (ι.2 : ℕ)) := by
  classical
  set nV := aV + w * (m - 1)
  set N := p ^ a * (nV + (k - 1) * (w * m)) + (aW + r * (m - 1))
  let vec : ℕ → (Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K[X][Y] := fun j x =>
    ((curveDeriv Ψ)^[j] (monoFin x.2)) ^ p ^ a * frobModel R D m ((x.1.1 : ℕ), (x.1.2 : ℕ))
  let M : Submodule K K[X][Y] := Submodule.span K
    (((Finset.range (N + 1) ×ˢ Finset.range m).image (monomialXY (R := K)) : Finset K[X][Y]) :
      Set K[X][Y])
  let Lj : ℕ → ((Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K) →ₗ[K] K[X][Y] := fun j =>
    ((modByMonicHom Ψ).restrictScalars K) ∘ₗ ∑ x, (LinearMap.proj x).smulRight (vec j x)
  have hLj : ∀ j d, Lj j d = (∑ x, d x • vec j x) %ₘ Ψ := by
    intro j d
    simp [Lj, modByMonicHom]
  have hΨw' : WeightedDegreeLE w (w * Ψ.natDegree) Ψ := hm ▸ hΨw
  have hvec : ∀ j < k, ∀ x, WeightedDegreeLE w N (vec j x) := by
    intro j hj x
    have h1 : WeightedDegreeLE w nV (monoFin x.2 : K[X][Y]) :=
      WeightedDegreeLE.monomialXY (fin_add_mul_le w x.2)
    have h2 := (WeightedDegreeLE.iterate_curveDeriv hΨw h1 j).pow (p ^ a)
    have h3 := WeightedDegreeLE.frobModel (K := K) hR hD (m := m) (x := ((x.1.1 : ℕ), (x.1.2 : ℕ)))
      x.1.2.2 (A := aW) (by have := x.1.1.2; simp only; omega)
    refine (h2.mul h3).mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hmem : ∀ j < k, ∀ d, Lj j d ∈ M := by
    intro j hj d
    rw [hLj]
    have hsum : WeightedDegreeLE w N (∑ x, d x • vec j x) :=
      WeightedDegreeLE.sum _ fun x _ => (hvec j hj x).smul _
    have hred := WeightedDegreeLE.modByMonic hΨ hΨw' hsum
    refine mem_span_monomialXY_of_natDegree_lt ?_ hred.coeff_natDegree_le
    have hΨ1 : Ψ ≠ 1 := fun h => by rw [h, natDegree_one] at hm; omega
    exact (natDegree_modByMonic_lt _ hΨ hΨ1).trans_eq hm
  let L : ((Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K) →ₗ[K] (Fin k → M) :=
    LinearMap.pi fun j => (Lj j).codRestrict M (hmem j j.2)
  have hfin : Module.finrank K (Fin k → M) <
      Module.finrank K ((Fin (aW + 1) × Fin m) × (Fin (aV + 1) × Fin m) → K) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Fintype.card_prod]
    have hM : Module.finrank K M ≤ (N + 1) * m := by
      refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
      simp
    calc k * Module.finrank K M ≤ k * ((N + 1) * m) := Nat.mul_le_mul_left _ hM
      _ = k * (m * (N + 1)) := by ring
      _ < (m * (aW + 1)) * (m * (aV + 1)) := hcount
      _ = (aW + 1) * m * ((aV + 1) * m) := by ring
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hfin)
  have hdvd : ∀ j < k, Ψ ∣ ∑ x, d x • vec j x := by
    intro j hj
    have h0 := congrArg (fun f : Fin k → M => ((f ⟨j, hj⟩ : M) : K[X][Y]))
      (LinearMap.mem_ker.mp hd)
    have h1 : Lj j d = 0 := by simpa [L] using h0
    rw [hLj] at h1
    exact (modByMonic_eq_zero_iff_dvd hΨ).mp h1
  set fr := iterateFrobeniusEquiv K p a
  have hfr : ∀ x : K, (fr.symm x) ^ p ^ a = x := pow_iterateFrobeniusEquiv_symm p a
  let v : Fin (aW + 1) × Fin m → K[X][Y] := fun ι => ∑ β, fr.symm (d (ι, β)) • monoFin β
  refine ⟨v, fun ι => Submodule.sum_mem _ fun β _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, rfl⟩), ?_, fun j hj => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.mp hd0
    refine ⟨x.1, fun h0 => hx ?_⟩
    have := eq_zero_of_sum_smul_monomialXY_eq_zero' (K := K) injective_val_prod h0 x.2
    rwa [Prod.mk.eta, map_eq_zero_iff _ fr.symm.injective] at this
  · convert hdvd j hj using 1
    rw [show (∑ x, d x • vec j x) = ∑ ι, ∑ β, d (ι, β) • vec j (ι, β) from
      Fintype.sum_prod_type _]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [v, vec, ← Module.End.coe_pow, map_sum, map_smul, sum_pow_char_pow, smul_pow, hfr,
      Finset.sum_mul, smul_mul_assoc]


/-- **The auxiliary function is nonzero on the curve.** If the `v ι` lie in the span of the
monomials `Xⁱ Yʲ` (`i ≤ aV`, `j < m`), are not all zero, and `m (aV + w (m - 1)) < σ = p ^ b`,
then `Ψ` does not divide `∑ v ι · (Xⁱ Yʲ) ^ σ`, so their resultant is nonzero. This is
Bombieri's independence argument at a simple point of the curve. -/
theorem resultant_ne_zero_auxiliary [IsAlgClosed K] {Ψ : K[X][Y]} (hΨ : Ψ.Monic)
    (hirr : Irreducible Ψ) (hder : derivative Ψ ≠ 0) {m w : ℕ} (hm : Ψ.natDegree = m)
    (hΨw : WeightedDegreeLE w (w * m) Ψ) {b aV aW : ℕ} (hV : m * (aV + w * (m - 1)) < p ^ b)
    (v : Fin (aW + 1) × Fin m → K[X][Y])
    (hv : ∀ ι, v ι ∈ Submodule.span K (Set.range fun β : Fin (aV + 1) × Fin m => monoFin β))
    (hv0 : ∃ ι, v ι ≠ 0) :
    resultant Ψ (∑ ι, v ι * monoFin ι ^ p ^ b) ≠ 0 := by
  classical
  obtain ⟨a₀, b₀, h0, h1⟩ := exists_simple_point hΨ hirr hder
  obtain ⟨β₀, hβ₀, hβ⟩ := exists_powerSeries_root_of_simple_root hΨ h0 h1
  have hβ' : branchEval a₀ β₀ Ψ = 0 := by rw [branchEval_apply]; exact hβ
  set ι₀ := branchEval a₀ β₀
  have hdeg : Ψ.natDegree ≠ 0 := (hΨ.natDegree_pos.mpr hirr.ne_one).ne'
  have key : ∀ h : K[X][Y], h ≠ 0 → h.degree < m →
      ι₀ h ≠ 0 ∧ (ι₀ h).order ≤ ((resultant Ψ h).natDegree : ℕ∞) := by
    intro h hh hlt
    have hres : resultant Ψ h ≠ 0 := by
      refine resultant_ne_zero_of_irreducible_of_not_dvd hirr hdeg fun hd => ?_
      have h1 := natDegree_le_of_dvd hd hh
      have h2 := (natDegree_lt_iff_degree_lt hh).mpr hlt
      omega
    have hord := order_branchEval_le hΨ hβ₀ hβ' hres
    refine ⟨fun h0' => ?_, hord⟩
    rw [h0', PowerSeries.order_zero] at hord
    exact absurd hord (by simp)
  have hΨw' : ∀ i, Ψ.coeff i ≠ 0 → (Ψ.coeff i).natDegree + w * i ≤ w * Ψ.natDegree :=
    hm ▸ hΨw
  let ι₀L : K[X][Y] →ₗ[K] PowerSeries K :=
    { toFun := ι₀, map_add' := map_add ι₀, map_smul' := branchEval_smul a₀ β₀ }
  set V := Submodule.span K (Set.range fun β : Fin (aV + 1) × Fin m => (monoFin β : K[X][Y]))
  have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
  set U := V.map ι₀L
  have hspanV : ∀ h ∈ V, h.degree < m ∧ WeightedDegreeLE w (aV + w * (m - 1)) h :=
    fun h hh => degree_lt_and_weightedDegreeLE_of_mem_span_monoFin w hh
  have hU : ∀ u ∈ U, u ≠ 0 → u.order < (p ^ b : ℕ) := by
    intro u hu hu0
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hu
    have hh0 : h ≠ 0 := by rintro rfl; exact hu0 (map_zero _)
    obtain ⟨hlt, hw⟩ := hspanV h hh
    have hb : (resultant Ψ h).natDegree ≤ m * (aV + w * (m - 1)) :=
      (natDegree_resultant_le_of_weightedDegree_le hΨ hΨw' hw).trans_eq (by rw [hm])
    calc (ι₀L h).order ≤ ((resultant Ψ h).natDegree : ℕ∞) := (key h hh0 hlt).2
      _ ≤ ((m * (aV + w * (m - 1)) : ℕ) : ℕ∞) := by exact_mod_cast hb
      _ < ((p ^ b : ℕ) : ℕ∞) := by exact_mod_cast hV
  have hy : LinearIndependent K fun ι : Fin (aW + 1) × Fin m => ι₀ (monoFin ι) := by
    refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
    have hc' : ι₀ (∑ ι, c ι • monoFin ι) = 0 := by
      rw [map_sum, Finset.sum_congr rfl fun i _ => branchEval_smul a₀ β₀ (c i) (monoFin i)]
      exact hc
    by_cases hz : ∑ ι, c ι • (monoFin ι : K[X][Y]) = 0
    · exact eq_zero_of_sum_smul_monomialXY_eq_zero' injective_val_prod hz i
    · have hlt := (degree_lt_and_weightedDegreeLE_of_mem_span_monoFin w
        (h := ∑ ι, c ι • monoFin ι) (Submodule.sum_mem _ fun ι _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨ι, rfl⟩))).1
      exact absurd hc' (key _ hz hlt).1
  intro hres0
  have hdvd : Ψ ∣ ∑ ι, v ι * monoFin ι ^ p ^ b := by
    by_contra hnd
    exact resultant_ne_zero_of_irreducible_of_not_dvd hirr hdeg hnd hres0
  have hzero : ∑ ι, ι₀ (v ι) * ι₀ (monoFin ι) ^ p ^ b = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    have := congrArg ι₀ ht
    simpa [map_sum, map_mul, map_pow, hβ'] using this
  obtain ⟨ι, hι⟩ := hv0
  have := PowerSeries.eq_zero_of_sum_mul_pow_eq_zero p b U hU hy
    (u := fun ι => ι₀ (v ι)) (fun ι => Submodule.mem_map_of_mem (hv ι)) hzero ι
  exact (key _ hι (hspanV _ (hv ι)).1).1 this

/-- **Stepanov's bound, in counting form.** With the parameters `ρ = p ^ a`, `σ = p ^ b`,
`q = ρ σ`, `k ≤ p`, `k ρ ≤ q`, the degree bounds `aV`, `aW` subject to `m (aV + w (m-1)) < σ`
and to the dimension count `hcount`, every finite set `S` of twisted Frobenius points of `Ψ = 0`
at which `∂Ψ/∂Y ≠ 0` satisfies `k · #S ≤ m (aV + w (m - 1) + σ (aW + w (m - 1)))`. -/
theorem card_mul_le_of_stepanov [IsAlgClosed K] {Ψ R D : K[X][Y]} (hΨ : Ψ.Monic)
    (hirr : Irreducible Ψ) (hder : derivative Ψ ≠ 0) {m w r : ℕ} (hm : Ψ.natDegree = m)
    (hΨw : WeightedDegreeLE w (w * m) Ψ) (hR : WeightedDegreeLE w r R)
    (hD : WeightedDegreeLE w r D) {a b k aV aW : ℕ} (hk : k ≤ p)
    (hkq : k * p ^ a ≤ p ^ (a + b)) (hV : m * (aV + w * (m - 1)) < p ^ b)
    (hcount : k * (m * (p ^ a * (aV + w * (m - 1) + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) <
      (m * (aW + 1)) * (m * (aV + 1)))
    (S : Finset (K × K))
    (hS : ∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
      P.1 ^ p ^ (a + b) = P.1 ∧ D.evalEval P.1 P.2 ≠ 0 ∧
      D.evalEval P.1 P.2 * P.2 ^ p ^ (a + b) = R.evalEval P.1 P.2) :
    k * S.card ≤ m * (aV + w * (m - 1) + p ^ b * (aW + w * (m - 1))) := by
  classical
  have hdeg : Ψ.natDegree ≠ 0 := (hΨ.natDegree_pos.mpr hirr.ne_one).ne'
  have hm0 : 0 < m := by omega
  obtain ⟨v, hv, hv0, hE⟩ := exists_auxiliary p hΨ hm hm0 hΨw hR hD hcount
  obtain ⟨g, hg⟩ : ∃ g, g = ∑ ι, v ι * monoFin ι ^ p ^ b := ⟨_, rfl⟩
  have hres : resultant Ψ g ≠ 0 :=
    hg ▸ resultant_ne_zero_auxiliary p hΨ hirr hder hm hΨw hV v hv hv0
  choose! βf hβf using fun P (hP : P ∈ S) =>
    exists_powerSeries_root_of_simple_root hΨ (hS P hP).1 (hS P hP).2.1
  have hord : ∀ P ∈ S, (k : ℕ∞) ≤ (branchEval P.1 (βf P) g).order := by
    intro P hP
    obtain ⟨h0, h1, hq, hD0, hRD⟩ := hS P hP
    have hβ : branchEval P.1 (βf P) Ψ = 0 := by rw [branchEval_apply]; exact (hβf P hP).2
    rw [hg]
    refine le_order_branchEval_sum_mul_pow p (hβf P hP).1 hβ h1 v (fun ι => monoFin ι)
      (fun ι => frobModel R D m ((ι.1 : ℕ), (ι.2 : ℕ))) hk hkq
      (lam := D.evalEval P.1 P.2 ^ (m - 1)) (pow_ne_zero _ hD0) (fun ι => ?_) (fun j hj => ?_)
    · have hl : (ι.2 : ℕ) + (m - 1 - ι.2) = m - 1 := by have := ι.2.2; omega
      simp only [frobModel, monoFin, monomialXY, evalEval_mul, evalEval_pow, evalEval_C,
        eval_pow, eval_X, evalEval_X, ← hRD, mul_pow, ← pow_mul]
      have hD' : D.evalEval P.1 P.2 ^ (m - 1) =
          D.evalEval P.1 P.2 ^ (ι.2 : ℕ) * D.evalEval P.1 P.2 ^ (m - 1 - ι.2) := by
        rw [← pow_add, hl]
      rw [pow_mul' P.1, hq, mul_comm (ι.2 : ℕ) (p ^ (a + b)), hD']
      ring
    · obtain ⟨t, ht⟩ := hE j hj
      rw [ht, evalEval_mul, h0, zero_mul]
  have hsum := sum_order_le_natDegree_resultant hΨ S βf hβf hres
  simp only [← branchEval_apply] at hsum
  have hlow : (S.card • (k : ℕ∞)) ≤ ∑ P ∈ S, (branchEval P.1 (βf P) g).order :=
    Finset.card_nsmul_le_sum S _ _ hord
  have hΨw' : ∀ i, Ψ.coeff i ≠ 0 → (Ψ.coeff i).natDegree + w * i ≤ w * Ψ.natDegree :=
    hm ▸ hΨw
  have hgw : WeightedDegreeLE w (aV + w * (m - 1) + p ^ b * (aW + w * (m - 1))) g := by
    rw [hg]
    refine WeightedDegreeLE.sum _ fun ι _ => ?_
    have h1 := (degree_lt_and_weightedDegreeLE_of_mem_span_monoFin w (hv ι)).2
    have h2 : WeightedDegreeLE w (aW + w * (m - 1)) (monoFin ι : K[X][Y]) :=
      WeightedDegreeLE.monomialXY (fin_add_mul_le w ι)
    exact h1.mul (h2.pow _)
  have hdegR : (resultant Ψ g).natDegree ≤
      m * (aV + w * (m - 1) + p ^ b * (aW + w * (m - 1))) :=
    (natDegree_resultant_le_of_weightedDegree_le hΨ hΨw' hgw).trans_eq (by rw [hm])
  have h1 : ((S.card * k : ℕ) : ℕ∞) ≤ ((resultant Ψ g).natDegree : ℕ∞) := by
    refine le_trans (le_of_eq ?_) (hlow.trans hsum)
    simp [nsmul_eq_mul]
  have h2 : S.card * k ≤ (resultant Ψ g).natDegree := ENat.coe_le_coe.mp h1
  rw [mul_comm k]
  exact h2.trans hdegR

end Construction

end Polynomial.Bivariate
