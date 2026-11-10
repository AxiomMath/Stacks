module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.KroneckerEigenvalueBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopDegreeWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTraceFormulaOfCohomology

/-!
# The weak bound on the weights of `H¹_c` of a mixed lisse sheaf on a curve

Let `σ : π₁(U, x̄) → GL_m(E)` be mixed of real weights `≤ w'` along `ι' : E → ℂ` at the
Frobenius elements of the closed points of a smooth curve `U` over `k`, `#k = q`.  If
`H⁰_c(U_k̄, ℱ) = 0`, the roots of the `E`-linear `π^*` on `H²_c` are bounded by
`q ^ ((w' + 2) / 2)`, and the number of points of `U` over `k_N` is `O(q ^ N)`, then the
`E`-linear trace formula (`Stacks.EtaleCohomology.CurveLinearTraceFormulaInput`) bounds the roots
of `π^*` on `H¹_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)` along `ι'` by `q ^ ((w' + 2) / 2)` (no cancellation:
`Stacks.EtaleCohomology.norm_le_of_isBigO_trace_pow_sub_trace_pow`). This is the global estimate
behind the weak bound on the local invariants in Weil II 1.8.

## Main results

* `Stacks.EtaleCohomology.norm_map_finsum_trace_pow_le`: the pointwise bound on the sum over
  points.
* `norm_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_one_linear`: the roots of `π^*`
  on `H¹_c` along `ι'` are bounded by `q ^ ((w' + 2) / 2)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Filter Asymptotics

universe u

namespace Stacks.EtaleCohomology

/-- A real power raised to a natural power, when the exponents multiply to `b`. -/
private theorem rpow_pow_eq_rpow {q a b : ℝ} (hq : 0 ≤ q) (n : ℕ) (h : a * n = b) :
    (q ^ a) ^ n = q ^ b := by
  rw [← Real.rpow_mul_natCast hq, h]

/-- **The sum over points, bounded pointwise.**  If every eigenvalue of `M y`, read along `ι`, has
absolute value at most `q₀ ^ (deg y · w' / 2)`, then for a finite set `S` of points of degrees
dividing `N`,
`|ι ∑_{y ∈ S} deg y · tr (M y) ^ (N / deg y)| ≤ m q₀ ^ (N w' / 2) ∑_{y ∈ S} deg y`. -/
public theorem norm_map_finsum_trace_pow_le {E : Type*} [Field E] (ι : E →+* ℂ) {Y : Type*}
    {m : ℕ} (M : Y → Matrix (Fin m) (Fin m) E) (deg : Y → ℕ) {q₀ w' : ℝ} (hq₀ : 0 < q₀)
    (hM : ∀ (y : Y) (z : ℂ), ((M y).charpoly.map ι).IsRoot z → ‖z‖ ≤ q₀ ^ ((deg y : ℝ) * w' / 2))
    {S : Set Y} (hS : S.Finite) {N : ℕ} (hdvd : ∀ y ∈ S, deg y ∣ N) (hpos : ∀ y ∈ S, 0 < deg y) :
    ‖ι (∑ᶠ y ∈ S, (deg y : E) * ((M y) ^ (N / deg y)).trace)‖ ≤
      m * q₀ ^ ((N : ℝ) * w' / 2) * ∑ᶠ y ∈ S, (deg y : ℝ) := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS, map_sum,
    Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy => ?_)
  rw [Set.Finite.mem_toFinset] at hy
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  have h := norm_map_trace_pow_le_of_forall_isRoot ι (M y) (Real.rpow_nonneg hq₀.le _) (hM y)
    (N / deg y)
  have hexp : (q₀ ^ ((deg y : ℝ) * w' / 2)) ^ (N / deg y) = q₀ ^ ((N : ℝ) * w' / 2) := by
    refine rpow_pow_eq_rpow hq₀.le _ ?_
    obtain ⟨c, hc⟩ := hdvd y hy
    rw [hc, Nat.mul_div_cancel_left _ (hpos y hy)]
    push_cast
    ring
  rw [hexp] at h
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)

/-- **The sum over points, bounded by the point count.**  Under the hypotheses of
`norm_map_finsum_trace_pow_le`, if the points of degree dividing `N` have total degree at most
`C q₀ ^ N`, the sum is bounded by `m C (q₀ ^ ((w' + 2) / 2)) ^ N`. -/
public theorem norm_map_finsum_trace_pow_le_mul_pow {E : Type*} [Field E] (ι : E →+* ℂ)
    {Y : Type*} {m : ℕ} (M : Y → Matrix (Fin m) (Fin m) E) (deg : Y → ℕ) {q₀ w' C : ℝ}
    (hq₀ : 0 < q₀)
    (hM : ∀ (y : Y) (z : ℂ), ((M y).charpoly.map ι).IsRoot z → ‖z‖ ≤ q₀ ^ ((deg y : ℝ) * w' / 2))
    (hdeg : ∀ y, 0 < deg y) {N : ℕ} (hS : {y | deg y ∣ N}.Finite)
    (hpt : ∑ᶠ (y : Y) (_ : deg y ∣ N), (deg y : ℝ) ≤ C * q₀ ^ N) :
    ‖ι (∑ᶠ (y : Y) (_ : deg y ∣ N), (deg y : E) * ((M y) ^ (N / deg y)).trace)‖ ≤
      m * C * (q₀ ^ ((w' + 2) / 2)) ^ N := by
  have hRN : (q₀ ^ ((w' + 2) / 2)) ^ N = q₀ ^ ((N : ℝ) * w' / 2) * q₀ ^ N := by
    rw [rpow_pow_eq_rpow hq₀.le N (b := N * w' / 2 + N) (by ring), Real.rpow_add hq₀,
      Real.rpow_natCast]
  calc _ ≤ m * q₀ ^ ((N : ℝ) * w' / 2) * ∑ᶠ (y : Y) (_ : deg y ∣ N), (deg y : ℝ) :=
        norm_map_finsum_trace_pow_le ι M deg hq₀ hM hS (fun y hy => hy) (fun y _ => hdeg y)
    _ ≤ m * q₀ ^ ((N : ℝ) * w' / 2) * (C * q₀ ^ N) :=
        mul_le_mul_of_nonneg_left hpt (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hq₀.le _))
    _ = m * C * (q₀ ^ ((w' + 2) / 2)) ^ N := by
      rw [hRN]
      ring

section Coinvariants

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} [ConnectedSpace X] [CompactSpace X]
  [Nonempty X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : GeometricPoint X)

/-- **The weights of Frobenius on the geometric coinvariants, for real weights and coefficients in
a field `E`.**  If `σ` is mixed of real weights `≤ w'` along `ι'` at the Frobenius elements and
`φ` lies over the inverse of the Frobenius of `k`, every root along `ι'` of the characteristic
polynomial of `φ` on the geometric coinvariants of `σ` has absolute value at most
`q ^ (w' / 2)`. -/
public theorem norm_le_of_isRoot_coinvariantsFrobenius_of_mixed (p n : ℕ) [Fact p.Prime]
    [CharP k p] (hcard : Fintype.card k = p ^ n) {E : Type*} [Field E] {m : ℕ}
    (σ : EtaleFundamentalGroup X x →* GL (Fin m) E) (ι' : E →+* ℂ) {w' : ℝ}
    (hmix : ∀ (y : closedPoints X) (z : ℂ),
      ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ ≤ ((p ^ n : ℕ) : ℝ) ^ ((residueDegree f y.1 : ℝ) * w' / 2))
    (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹)
    {z : ℂ} (hz : ((LinearMap.charpoly (coinvariantsFrobenius
      (etaleFundamentalGroupMap f x).toMonoidHom.ker σ φ)).map ι').IsRoot z) :
    ‖z‖ ≤ ((p ^ n : ℕ) : ℝ) ^ (w' / 2) := by
  classical
  obtain ⟨y0, -, hy0⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  set y : closedPoints X := ⟨y0, hy0⟩
  have := finite_residueField f y.1 y.2
  have hmem := AlgebraicGeometry.inv_pow_mul_geometricFrobeniusFamily_mem_ker p n hcard f x y φ hφ
  have hroot := isRoot_charpoly_pow_of_isRoot_coinvariantsFrobenius _ ι' σ φ hmem hz
  have hn := hmix y _ hroot
  have hq : (0 : ℝ) ≤ ((p ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [norm_pow] at hn
  refine (pow_le_pow_iff_left₀ (norm_nonneg z) (Real.rpow_nonneg hq _)
    (residueDegree_pos f y.1 y.2).ne').mp ?_
  exact hn.trans_eq (rpow_pow_eq_rpow hq _ (by ring)).symm

end Coinvariants

section Cohomology

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
  (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]
  [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
  (x : GeometricPoint U.1)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ))

/-- **The weak bound on `H¹_c` of a curve, `E`-linearly.**  Let `σ` be mixed of real weights
`≤ w'` along `ι'` at the Frobenius elements of the closed points of `U`, with
`H⁰_c(U_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ) = 0`, `H¹_c` and `H²_c` finite dimensional, the roots of `π^*` on
`H²_c` along `ι'` at most `q ^ ((w' + 2) / 2)`, and `#U(k_N) = O(q ^ N)`.  Given the `E`-linear
trace formula, the roots of `π^*` on `H¹_c` along `ι'` are at most `q ^ ((w' + 2) / 2)`. -/
public theorem norm_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_one_linear
    (htf : CurveLinearTraceFormulaInput.{u}) (hℓp : ℓ ≠ p) (ι' : E →+* ℂ) (w' : ℝ)
    (hmix : ∀ (y : closedPoints U.1) (z : ℂ),
      ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ ≤ ((p ^ n : ℕ) : ℝ) ^ ((residueDegree f y.1 : ℝ) * w' / 2))
    (h0 : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 0))
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1)]
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2)]
    (h2 :
      letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j
        kbar 2 E
      haveI := (restrictScalarsRepCoefficientSheaf
          B U x b σ hσ).rationalCohomologyModule_isScalarTower
        f j kbar 2 E (algebraMap_conjIntegralSubring_algebraMap _ _)
      haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f
          j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2) :=
        Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
      ∀ z : ℂ, (((restrictScalarsRepCoefficientSheaf
          B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
        f j kbar 2 E p n hcard).charpoly.map ι').IsRoot z →
        ‖z‖ ≤ ((p ^ n : ℕ) : ℝ) ^ ((w' + 2) / 2))
    {C : ℝ} (hpt : ∀ N : ℕ, 0 < N →
      (∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : ℝ)) ≤
        C * ((p ^ n : ℕ) : ℝ) ^ N) :
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI := (restrictScalarsRepCoefficientSheaf
        B U x b σ hσ).rationalCohomologyModule_isScalarTower
      f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    ∀ z : ℂ, (((restrictScalarsRepCoefficientSheaf
        B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
        f j kbar 1 E p n hcard).charpoly.map ι').IsRoot z →
      ‖z‖ ≤ ((p ^ n : ℕ) : ℝ) ^ ((w' + 2) / 2) := by
  set F := restrictScalarsRepCoefficientSheaf B U x b σ hσ
  let M0 := F.rationalCohomologyModule f j kbar 0 E
  let M1 := F.rationalCohomologyModule f j kbar 1 E
  let M2 := F.rationalCohomologyModule f j kbar 2 E
  have := F.rationalCohomologyModule_isScalarTower f j kbar 1 E
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have := F.rationalCohomologyModule_isScalarTower f j kbar 2 E
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar F.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar F.toLAdicSheaf 2) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  set q₀ : ℝ := ((p ^ n : ℕ) : ℝ) with hq₀
  have hq₀pos : 0 < q₀ := by
    rw [hq₀]
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos n
  set R : ℝ := q₀ ^ ((w' + 2) / 2)
  have hRpos : 0 ≤ R := Real.rpow_nonneg hq₀pos.le _
  set F1 := F.rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard
  set F2 := F.rationalGeometricCompactlySupportedFrobenius f j kbar 2 E p n hcard
  have htr0 : ∀ N : ℕ, LinearMap.trace E _
      ((F.rationalGeometricCompactlySupportedFrobenius f j kbar 0 E p n hcard) ^ N) = 0 := by
    intro N
    have : (F.rationalGeometricCompactlySupportedFrobenius f j kbar 0 E p n hcard) ^ N = 0 :=
      LinearMap.ext fun v => h0.elim _ _
    rw [this, map_zero]
  have key : ∀ N : ℕ, 0 < N →
      ι' (LinearMap.trace E _ (F1 ^ N)) - ι' (LinearMap.trace E _ (F2 ^ N)) =
      -ι' (∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : E) *
        (((σ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace) := by
    intro N hN
    have htfN :
        (∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : E) *
        (((σ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace) =
        (-1 : E) ^ 0 * LinearMap.trace E _
          ((F.rationalGeometricCompactlySupportedFrobenius f j kbar 0 E p n hcard) ^ N) +
        (-1 : E) ^ 1 * LinearMap.trace E _ (F1 ^ N) +
        (-1 : E) ^ 2 * LinearMap.trace E _ (F2 ^ N) := by
      have := htf B U ℓ k f j kbar p n hcard hℓp x E b σ hσ N hN
      rwa [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at this
    rw [htfN, htr0, mul_zero, zero_add, pow_one, pow_two, neg_one_mul, neg_one_mul, neg_neg,
      one_mul, map_add, map_neg]
    ring
  have hg : ∀ β ∈ (F2.charpoly.map ι').roots, ‖β‖ ≤ R := fun β hβ =>
    h2 β (Polynomial.mem_roots'.1 hβ).2
  have hbig : (fun N : ℕ => ι' (LinearMap.trace E _ (F1 ^ N)) - ι' (LinearMap.trace E _ (F2 ^ N)))
      =O[atTop] fun N => R ^ N := by
    refine IsBigO.of_bound (m * C) ((eventually_gt_atTop 0).mono fun N hN => ?_)
    rw [key N hN, norm_neg, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hRpos N)]
    exact norm_map_finsum_trace_pow_le_mul_pow ι' (fun y : closedPoints U.1 =>
      ((σ (geometricFrobeniusFamily f x y) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E))
      (fun y => residueDegree f y.1) hq₀pos hmix (fun y => residueDegree_pos f y.1 y.2)
      ((finite_setOf_closedPoints_residueDegree_le f N).subset fun y hy => Nat.le_of_dvd hN hy)
      (hpt N hN)
  intro z hz
  exact norm_le_of_isBigO_trace_pow_sub_trace_pow ι' hRpos hg hbig z
    ((Polynomial.mem_roots ((LinearMap.charpoly_monic F1).map ι').ne_zero).2 hz)

omit [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f] [IsAlgClosure k kbar]
  [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
  [FiniteDimensional ℚ_[ℓ] E] in
/-- **The weights of `H²_c` are `≤ w' + 2`, `E`-linearly, for real weights**, given an
`E`-linear identification of `H²_c` with the geometric coinvariants carrying `π^*` to `q · φ`. -/
public theorem norm_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_two_linear
    [CompactSpace U.1] [Nonempty U.1] (ι' : E →+* ℂ) {w' : ℝ}
    (hmix : ∀ (y : closedPoints U.1) (z : ℂ),
      ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ ≤ ((p ^ n : ℕ) : ℝ) ^ ((residueDegree f y.1 : ℝ) * w' / 2))
    (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2)] :
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 2 E
    haveI := (restrictScalarsRepCoefficientSheaf
        B U x b σ hσ).rationalCohomologyModule_isScalarTower
      f j kbar 2 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    ∀ (e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2 ≃ₗ[E]
        Representation.Coinvariants ((matrixRepresentation σ).comp
          (etaleFundamentalGroupMap f x).toMonoidHom.ker.subtype)),
      (∀ v, e ((restrictScalarsRepCoefficientSheaf
          B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
          f j kbar 2 E p n hcard v) = ((p ^ n : ℕ) : E) •
            coinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker σ φ (e v)) →
      ∀ z : ℂ, (((restrictScalarsRepCoefficientSheaf
          B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
        f j kbar 2 E p n hcard).charpoly.map ι').IsRoot z →
        ‖z‖ ≤ ((p ^ n : ℕ) : ℝ) ^ ((w' + 2) / 2) := by
  classical
  let := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 2 E
  have := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar 2 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  intro e he z hz
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  set g := coinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker σ φ
  have : FiniteDimensional E (Representation.Coinvariants ((matrixRepresentation σ).comp
      (etaleFundamentalGroupMap f x).toMonoidHom.ker.subtype)) := e.finiteDimensional
  have hπ : (restrictScalarsRepCoefficientSheaf
      B U x b σ hσ).rationalGeometricCompactlySupportedFrobenius
      f j kbar 2 E p n hcard = e.symm.conj (((p ^ n : ℕ) : E) • g) := by
    ext v
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
      LinearMap.smul_apply, he]
  have hq0 : ((p ^ n : ℕ) : E) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  rw [hπ, LinearEquiv.charpoly_conj] at hz
  have hz' := isRoot_charpoly_div_of_isRoot_charpoly_smul ι' g hq0 hz
  have hn := norm_le_of_isRoot_coinvariantsFrobenius_of_mixed f x p n hcard σ ι' hmix φ hφ hz'
  have hqpos : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)
  have hιq : ι' ((p ^ n : ℕ) : E) = (((p ^ n : ℕ) : ℝ) : ℂ) := by
    rw [map_natCast, Complex.ofReal_natCast]
  rw [hιq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos,
    div_le_iff₀ hqpos] at hn
  refine hn.trans_eq ?_
  rw [add_div, Real.rpow_add hqpos, div_self two_ne_zero, Real.rpow_one]

end Cohomology

end Stacks.EtaleCohomology

end
