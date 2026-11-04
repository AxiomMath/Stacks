module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Multiset.Fintype
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Weights from the growth of traces

The analytic core of every weight estimate in Deligne's proof of the Weil conjectures is the
passage from an estimate on traces of Frobenius to an estimate on its eigenvalues.  By the
Grothendieck–Lefschetz trace formula the alternating sum of the traces of the `n`-th power of
Frobenius on the cohomology groups is a sum over the points of degree dividing `n`, which is
estimated pointwise; to recover from this a bound on the eigenvalues in one degree one must know
that the eigenvalues in the other degrees cannot cancel those exceeding the bound.

This module proves the statement used for this: if `a` and `b` are finite families of complex
numbers, every `b k` has absolute value at most `R`, and the difference of power sums
`∑ i, a i ^ n - ∑ k, b k ^ n` is `O(R ^ n)`, then every `a i` has absolute value at most `R`.
Applied to the eigenvalues of `π_X^*` on `H^1_c` and `H^2_c` of a curve, with the bound on
`H^2_c` given by its description as coinvariants, it is the bound on `H^1_c`.

## Main results

* `Stacks.EtaleCohomology.eq_zero_of_tendsto_sum_mul_pow`: an exponential sum
  `∑ j, c j * z j ^ n` with distinct unimodular bases tends to `0` only if all its coefficients
  vanish.
* `Stacks.EtaleCohomology.norm_le_of_isBigO_sum_pow_sub_sum_pow`: the bound on the `a i` from
  the bound on the `b k` and on the difference of power sums.
* `Stacks.EtaleCohomology.norm_le_of_isBigO_multiset_sum_pow_sub`: the same for multisets.
* `Stacks.EtaleCohomology.trace_pow_eq_sum_roots_pow`: the trace of `f ^ n`, for an
  endomorphism `f` of a finite-dimensional vector space over an algebraically closed field, is
  the `n`-th power sum of the roots of its characteristic polynomial;
  `Stacks.EtaleCohomology.map_trace_pow_eq_sum_roots_map_pow` is the same read in `ℂ` along an
  embedding `ι : K →+* ℂ`, over an arbitrary field `K`.
* `Stacks.EtaleCohomology.norm_le_of_isBigO_trace_pow_sub_trace_pow`: if the complex
  eigenvalues of `g` are bounded by `R` and `ι Tr(f ^ n) - ι Tr(g ^ n) = O(R ^ n)`, the complex
  eigenvalues of `f` are bounded by `R`.
* `Stacks.EtaleCohomology.norm_map_trace_pow_le_of_norm_roots_eq_one`: the pointwise bound
  `|Tr(A ^ m)| ≤ r` for a matrix of size `r` all of whose complex eigenvalues are unimodular,
  which is how conclusion (2) of the conjecture enters the sum over points.

## Implementation notes

The non-vanishing of exponential sums is proved with a Vandermonde matrix rather than by
averaging: `n` consecutive values of the sum are the image of the vector `(c j * z j ^ n)_j`
under the transposed Vandermonde matrix of the `z j`, which is invertible since the `z j` are
distinct, so the vector tends to `0` with the sum, while its entries have constant absolute
values `‖c j‖`.

## References

* P. Deligne, *La conjecture de Weil I*, Publ. Math. IHÉS 43 (1974), §3.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Filter Topology Asymptotics Matrix

namespace Stacks.EtaleCohomology

/-- An exponential sum `∑ j, c j * z j ^ n` whose bases `z j` are distinct complex numbers of
absolute value `1` tends to `0` only if all of its coefficients vanish. -/
public theorem eq_zero_of_tendsto_sum_mul_pow {ι : Type*} [Fintype ι] {z : ι → ℂ}
    (hz : Function.Injective z) (hz1 : ∀ j, ‖z j‖ = 1) {c : ι → ℂ}
    (h : Tendsto (fun n : ℕ => ∑ j, c j * z j ^ n) atTop (𝓝 0)) : c = 0 := by
  classical
  let e := Fintype.equivFin ι
  set z' : Fin (Fintype.card ι) → ℂ := z ∘ e.symm
  set c' : Fin (Fintype.card ι) → ℂ := c ∘ e.symm
  have hsum : ∀ n : ℕ, ∑ j, c' j * z' j ^ n = ∑ j, c j * z j ^ n := fun n =>
    e.symm.sum_comp (fun j => c j * z j ^ n)
  set V := (Matrix.vandermonde z').transpose
  have hV : IsUnit V.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.2 (hz.comp e.symm.injective)).isUnit
  have hw : ∀ n : ℕ, (fun j => c' j * z' j ^ n) =
      V⁻¹ *ᵥ fun k : Fin (Fintype.card ι) => ∑ j, c' j * z' j ^ (n + k) := by
    intro n
    have hV' : V *ᵥ (fun j => c' j * z' j ^ n) =
        fun k : Fin (Fintype.card ι) => ∑ j, c' j * z' j ^ (n + k) := by
      ext k
      simp only [V, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
        pow_add]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [← hV', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hV, Matrix.one_mulVec]
  have hlim : Tendsto (fun n : ℕ =>
      V⁻¹ *ᵥ fun k : Fin (Fintype.card ι) => ∑ j, c' j * z' j ^ (n + k)) atTop
      (𝓝 (V⁻¹ *ᵥ 0)) := by
    refine ((Matrix.mulVecLin V⁻¹).continuous_of_finiteDimensional.tendsto _).comp ?_
    refine tendsto_pi_nhds.2 fun k => ?_
    simpa only [Function.comp_def, ← hsum, Pi.zero_apply] using
      h.comp (tendsto_add_atTop_nat (k : ℕ))
  rw [Matrix.mulVec_zero] at hlim
  funext i
  have hj : Tendsto (fun n : ℕ => c' (e i) * z' (e i) ^ n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← hw, Pi.zero_apply] using
      ((continuous_apply (e i)).tendsto _).comp hlim
  have hnorm : ∀ n : ℕ, ‖c' (e i) * z' (e i) ^ n‖ = ‖c i‖ := fun n => by
    simp [c', z', norm_pow, hz1]
  exact norm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [hnorm, norm_zero] using hj.norm))

/-- A power sum `∑ i ∈ s, w i ^ n` of complex numbers of absolute value `1` tends to `0` only if
the index set `s` is empty. -/
public theorem eq_empty_of_tendsto_sum_pow {ι : Type*} {s : Finset ι} {w : ι → ℂ}
    (hw : ∀ i ∈ s, ‖w i‖ = 1) (h : Tendsto (fun n : ℕ => ∑ i ∈ s, w i ^ n) atTop (𝓝 0)) :
    s = ∅ := by
  classical
  set S := s.image w
  set c : S → ℂ := fun u => ((s.filter fun i => w i = u).card : ℂ)
  have hgroup : ∀ n : ℕ, ∑ i ∈ s, w i ^ n = ∑ u : S, c u * (u : ℂ) ^ n := by
    intro n
    rw [Finset.sum_comp (fun u : ℂ => u ^ n) w, ← Finset.sum_coe_sort S]
    simp only [nsmul_eq_mul, c]
  have hunit : ∀ u : S, ‖(u : ℂ)‖ = 1 := by
    rintro ⟨u, hu⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
    exact hw j hj
  have hc := eq_zero_of_tendsto_sum_mul_pow (z := fun u : S => (u : ℂ)) Subtype.val_injective
    hunit (c := c) (h.congr hgroup)
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  have hcu := congrFun hc ⟨_, Finset.mem_image_of_mem w hi⟩
  simp only [c, Pi.zero_apply, Nat.cast_eq_zero, Finset.card_eq_zero] at hcu
  exact Finset.filter_eq_empty_iff.1 hcu hi rfl

/-- If every `x i` with `i ∈ s` has absolute value less than `M`, then
`∑ i ∈ s, (x i / M) ^ n` tends to `0`. -/
public theorem tendsto_sum_div_pow_of_norm_lt {ι : Type*} {s : Finset ι} {x : ι → ℂ} {M : ℝ}
    (hM0 : 0 < M) (hx : ∀ i ∈ s, ‖x i‖ < M) :
    Tendsto (fun n : ℕ => ∑ i ∈ s, (x i / M) ^ n) atTop (𝓝 0) := by
  rw [← Finset.sum_const_zero (s := s)]
  refine tendsto_finsetSum _ fun i hi => tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, div_lt_one hM0]
  exact hx i hi

/-- **No cancellation beyond the bound.**  Let `a` and `b` be finite families of complex
numbers and `0 ≤ R`.  If every `b k` has absolute value at most `R` and the difference of power
sums `∑ i, a i ^ n - ∑ k, b k ^ n` is `O(R ^ n)`, then every `a i` has absolute value at most
`R`. -/
public theorem norm_le_of_isBigO_sum_pow_sub_sum_pow {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → ℂ} {b : κ → ℂ} {R : ℝ} (hR : 0 ≤ R) (hb : ∀ k, ‖b k‖ ≤ R)
    (h : (fun n : ℕ => ∑ i, a i ^ n - ∑ k, b k ^ n) =O[atTop] fun n => R ^ n) (i : ι) :
    ‖a i‖ ≤ R := by
  classical
  by_contra! hi
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
  set M := Finset.univ.sup' hne fun i => ‖a i‖
  have hRM : R < M := hi.trans_le (Finset.le_sup' (fun i => ‖a i‖) (Finset.mem_univ i))
  have hM0 : 0 < M := hR.trans_lt hRM
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' hne fun i => ‖a i‖
  set top := Finset.univ.filter fun i => ‖a i‖ = M
  have hdiv : ∀ n : ℕ, (∑ i, a i ^ n - ∑ k, b k ^ n) / (M : ℂ) ^ n =
      (∑ i ∈ top, (a i / M) ^ n + ∑ i ∈ Finset.univ.filter (fun i => ¬ ‖a i‖ = M),
        (a i / M) ^ n) - ∑ k, (b k / M) ^ n := by
    intro n
    rw [Finset.sum_filter_add_sum_filter_not, sub_div, Finset.sum_div, Finset.sum_div]
    simp only [div_pow]
  have hD : Tendsto (fun n : ℕ => (∑ i, a i ^ n - ∑ k, b k ^ n) / (M : ℂ) ^ n) atTop (𝓝 0) := by
    refine IsLittleO.tendsto_div_nhds_zero (h.trans_isLittleO ?_)
    refine (isLittleO_pow_pow_of_lt_left hR hRM).trans_isBigO ?_
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    simp [norm_pow, Real.norm_eq_abs, abs_of_pos hM0]
  have hrest : Tendsto (fun n : ℕ => ∑ i ∈ Finset.univ.filter (fun i => ¬ ‖a i‖ = M),
      (a i / M) ^ n) atTop (𝓝 0) :=
    tendsto_sum_div_pow_of_norm_lt hM0 fun j hj =>
      lt_of_le_of_ne (Finset.le_sup' (fun i => ‖a i‖) (Finset.mem_univ j))
        (Finset.mem_filter.1 hj).2
  have hbs : Tendsto (fun n : ℕ => ∑ k, (b k / M) ^ n) atTop (𝓝 0) :=
    tendsto_sum_div_pow_of_norm_lt hM0 fun k _ => (hb k).trans_lt hRM
  have htop : Tendsto (fun n : ℕ => ∑ i ∈ top, (a i / M) ^ n) atTop (𝓝 0) := by
    have := (hD.add hbs).sub hrest
    simp only [hdiv, add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    ring
  have hunit : ∀ j ∈ top, ‖a j / M‖ = 1 := fun j hj => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0,
      (Finset.mem_filter.1 hj).2, div_self hM0.ne']
  have hi₀top : i₀ ∈ top := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi₀.symm⟩
  rw [eq_empty_of_tendsto_sum_pow (w := fun i => a i / M) hunit htop] at hi₀top
  exact Finset.notMem_empty _ hi₀top

/-! ### Traces of powers -/

section TracePow

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- On the generalized eigenspace of `f` for `μ`, the trace of `f ^ n` is `μ ^ n` times the
dimension. -/
public theorem trace_pow_restrict_maxGenEigenspace (f : Module.End K V) (μ : K) (n : ℕ)
    (h : Set.MapsTo (f ^ n) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ)) :
    LinearMap.trace K _ ((f ^ n).restrict h) =
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ n := by
  have hf := f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  rw [← Module.End.pow_restrict n hf]
  have hnil := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_eq_comp,
      LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl (f.restrict hf)).pow_left n) hnil,
      ih ((f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right n) μ))]
    ring

/-- The trace of `f ^ n`, for an endomorphism `f` of a finite-dimensional vector space over an
algebraically closed field, is the `n`-th power sum of the roots of the characteristic
polynomial of `f`, counted with multiplicity. -/
public theorem trace_pow_eq_sum_roots_pow [IsAlgClosed K] (f : Module.End K V) (n : ℕ) :
    LinearMap.trace K V (f ^ n) = (f.charpoly.roots.map (· ^ n)).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top
  have hfin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hmaps : ∀ μ, Set.MapsTo (f ^ n) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right n) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds hfin hmaps, Finset.sum_multiset_map_count]
  have hset : hfin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Multiset.mem_toFinset, ← Multiset.count_pos,
      Polynomial.count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, Nat.pos_iff_ne_zero,
      Ne, Ne, Submodule.finrank_eq_zero]
  rw [hset]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [trace_pow_restrict_maxGenEigenspace, LinearMap.finrank_maxGenEigenspace_eq,
    Polynomial.count_roots, nsmul_eq_mul]

end TracePow

/-! ### Eigenvalues of an endomorphism read in `ℂ` -/

/-- The no-cancellation bound for multisets: if every element of `B` has absolute value at most
`R ≥ 0` and the difference of the `n`-th power sums of `A` and of `B` is `O(R ^ n)`, then every
element of `A` has absolute value at most `R`. -/
public theorem norm_le_of_isBigO_multiset_sum_pow_sub {A B : Multiset ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hB : ∀ b ∈ B, ‖b‖ ≤ R)
    (h : (fun n : ℕ => (A.map (· ^ n)).sum - (B.map (· ^ n)).sum) =O[atTop] fun n => R ^ n) :
    ∀ a ∈ A, ‖a‖ ≤ R := by
  classical
  have hsum : ∀ (C : Multiset ℂ) (n : ℕ), (C.map (· ^ n)).sum = ∑ x : C, (x : ℂ) ^ n :=
    fun C n => by
      rw [Finset.sum_eq_multiset_sum]
      exact (congrArg Multiset.sum (Multiset.map_univ C (· ^ n))).symm
  intro a ha
  exact norm_le_of_isBigO_sum_pow_sub_sum_pow (a := fun x : A => (x : ℂ))
    (b := fun y : B => (y : ℂ)) hR (fun y => hB _ Multiset.coe_mem)
    (by simpa only [hsum] using h) (A.mkToType a ⟨0, Multiset.count_pos.2 ha⟩)

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Read along an embedding `ι : K →+* ℂ`, the trace of `f ^ n` is the `n`-th power sum of the
roots in `ℂ` of the characteristic polynomial of `f`, that is of the complex eigenvalues of `f`
counted with multiplicity. -/
public theorem map_trace_pow_eq_sum_roots_map_pow (ι : K →+* ℂ) (f : Module.End K V) (n : ℕ) :
    ι (LinearMap.trace K V (f ^ n)) = ((f.charpoly.map ι).roots.map (· ^ n)).sum := by
  classical
  let b := Module.Free.chooseBasis K V
  set A := LinearMap.toMatrix b b f
  have hA : (A.map ι).charpoly = f.charpoly.map ι := by
    rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.toMatrix_pow, AddMonoidHom.map_trace,
    ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, ← Matrix.trace_toLin'_eq,
    Matrix.toLin'_pow, trace_pow_eq_sum_roots_pow, Matrix.charpoly_toLin', hA]

/-- **Weights from the growth of traces.**  Let `f` and `g` be endomorphisms of
finite-dimensional vector spaces over `K`, read in `ℂ` along `ι : K →+* ℂ`, and let `0 ≤ R`.  If
every complex eigenvalue of `g` has absolute value at most `R`, and
`ι (Tr (f ^ n)) - ι (Tr (g ^ n))` is `O(R ^ n)`, then every complex eigenvalue of `f` has
absolute value at most `R`.

This is how a bound on the eigenvalues of Frobenius on `H^1_c` of a curve is extracted from the
trace formula: `f` is the action on `H^1_c`, `g` the action on `H^0_c ⊕ H^2_c`, and the
difference of traces is a sum over the points of the curve. -/
public theorem norm_le_of_isBigO_trace_pow_sub_trace_pow (ι : K →+* ℂ) {f : Module.End K V}
    {g : Module.End K W} {R : ℝ} (hR : 0 ≤ R) (hg : ∀ β ∈ (g.charpoly.map ι).roots, ‖β‖ ≤ R)
    (h : (fun n : ℕ => ι (LinearMap.trace K V (f ^ n)) - ι (LinearMap.trace K W (g ^ n)))
      =O[atTop] fun n => R ^ n) :
    ∀ α ∈ (f.charpoly.map ι).roots, ‖α‖ ≤ R := by
  refine norm_le_of_isBigO_multiset_sum_pow_sub hR hg ?_
  simpa only [map_trace_pow_eq_sum_roots_map_pow] using h

/-- **The pointwise trace bound in weight `0`.**  If every complex eigenvalue of a square matrix
`A` of size `r`, read along `ι`, has absolute value `1` -- conclusion (2) of the conjecture
preceding [Stacks, Tag 03VH] for `A = ρ(F_x)` -- then `|ι Tr(A ^ m)| ≤ r` for every `m`. -/
public theorem norm_map_trace_pow_le_of_norm_roots_eq_one {n : Type*} [Fintype n]
    [DecidableEq n] (ι : K →+* ℂ) (A : Matrix n n K)
    (hA : ∀ z : ℂ, (A.charpoly.map ι).IsRoot z → ‖z‖ = 1) (m : ℕ) :
    ‖ι (A ^ m).trace‖ ≤ Fintype.card n := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, map_trace_pow_eq_sum_roots_map_pow,
    Matrix.charpoly_toLin']
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  calc ((A.charpoly.map ι).roots.map ((‖·‖) ∘ (· ^ m))).sum
      ≤ ((A.charpoly.map ι).roots.map fun _ => (1 : ℝ)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun z hz => by
          simp [hA z ((Polynomial.mem_roots'.1 hz).2)]
    _ = Multiset.card (A.charpoly.map ι).roots := by simp
    _ ≤ Fintype.card n := by
        have := Polynomial.card_roots' (A.charpoly.map ι)
        rw [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim] at this
        exact_mod_cast this

end Stacks.EtaleCohomology

end
