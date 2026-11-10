module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixInertiaCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StrongMixPermutationTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.KroneckerEigenvalueBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepContinuity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TensorPowerTrick

/-!
# Weil II 1.8.4 from the weak estimate on the inertia invariants

Let `G` be a compact group, `φ : Gal(L/K) → G` continuous, `Fr` an arithmetic Frobenius at a place
`P` with residue field of order `q`, and `ρ : G → GL_r(E)` pure of weight `w` along `ι' : E → ℂ`
at a family of Frobenius elements `Frob y` of degrees `deg y` over `q₀`.  Weil II 1.8.4 needs the
eigenvalues of `φ(Fr⁻¹) ^ f` on the vectors of `ρ ⊗ ρ` (and `ρ^∨ ⊗ ρ^∨`) fixed by the elements of
`φ(I)` in an open subgroup `O ∋ φ(Fr) ^ f` to be bounded by `q ^ (w f)` (and `q ^ (-w f)`).  This
file derives these bounds from the *weak estimate*: for every representation `τ` of `G` mixed of
weights `≤ w'`, the eigenvalues of `τ(φ Fr⁻¹)` on the `φ(I)`-invariants are bounded by
`q ^ ((w' + 2) / 2)`.  The invariants of `φ(I) ∩ O` in `W` become `φ(I)`-invariants of the
permutation twist `W ⊗ E[G/O]`, which is mixed of the same weights; the loss of `q` disappears
after passing to tensor powers `W^{⊗ k}`.

## Main definitions

* `Stacks.EtaleCohomology.IsFrobeniusMixedLE`: the eigenvalues of `τ(Frob y)` along `ι'` are
  bounded by `q₀ ^ (deg y · w / 2)`.

## Main results

* `Stacks.EtaleCohomology.norm_le_of_forall_norm_trace_pow_le`: eigenvalues from traces of powers.
* `Stacks.EtaleCohomology.norm_le_rpow_mul_of_weakBound`: the bound on an open subgroup of inertia.
* `Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_weakBound`: Weil II 1.8.4 from the weak
  estimate.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.8.4 and its proof.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Matrix Filter Asymptotics
open scoped Pointwise

namespace Stacks.EtaleCohomology

section Eigenvalues

variable {K : Type*} [Field K] (ι : K →+* ℂ)

/-- **Eigenvalues from the growth of traces.**  If `|ι Tr(A ^ j)| ≤ C R ^ j` for all `j`, every
eigenvalue of `A` read along `ι` has absolute value at most `R`. -/
public theorem norm_le_of_forall_norm_trace_pow_le {a : ℕ} (A : Matrix (Fin a) (Fin a) K) {R C : ℝ}
    (hR : 0 ≤ R) (h : ∀ j : ℕ, ‖ι (A ^ j).trace‖ ≤ C * R ^ j) (z : ℂ)
    (hz : (A.charpoly.map ι).IsRoot z) : ‖z‖ ≤ R := by
  have hbig : (fun n : ℕ => ((A.charpoly.map ι).roots.map (· ^ n)).sum - (0 : Multiset ℂ).sum)
      =O[atTop] fun n => R ^ n := by
    refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
    rw [Multiset.sum_zero, sub_zero, ← Matrix.charpoly_toLin', ← map_trace_pow_eq_sum_roots_map_pow,
      ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hR n)]
    exact h n
  refine norm_le_of_isBigO_multiset_sum_pow_sub (B := 0) hR (by simp) hbig z ?_
  exact (Polynomial.mem_roots ((Matrix.charpoly_monic A).map ι).ne_zero).2 hz

/-- The eigenvalues of the identity matrix are `1`. -/
public theorem norm_le_one_of_isRoot_charpoly_one {a : ℕ} (z : ℂ)
    (hz : (((1 : Matrix (Fin a) (Fin a) K)).charpoly.map ι).IsRoot z) : ‖z‖ ≤ 1 := by
  refine norm_le_of_forall_norm_trace_pow_le ι 1 zero_le_one (C := a) (fun j => ?_) z hz
  rw [one_pow, one_pow, mul_one, Matrix.trace_one, Fintype.card_fin, map_natCast,
    Complex.norm_natCast]

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [DecidableEq X] {n : ℕ} (e : Fin n ≃ X)

/-- **The eigenvalues of a permutation matrix have absolute value at most `1`**: the trace of a
power of a permutation matrix is a number of fixed points. -/
public theorem norm_le_one_of_isRoot_charpoly_permMatrix (g : G) (z : ℂ)
    (hz : ((permMatrix e K g).charpoly.map ι).IsRoot z) : ‖z‖ ≤ 1 := by
  classical
  refine norm_le_of_forall_norm_trace_pow_le ι _ zero_le_one (C := n) (fun j => ?_) z hz
  have hpow : permMatrix e K g ^ j = permMatrix e K (g ^ j) := by
    rw [← permMatrixRepresentation_val, ← permMatrixRepresentation_val, ← Units.val_pow_eq_pow_val,
      map_pow]
  rw [hpow, one_pow, mul_one, Matrix.trace, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖ι ((permMatrix e K (g ^ j)).diag i)‖ ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by
          simp only [Matrix.diag, permMatrix, Matrix.of_apply]
          split_ifs <;> simp
    _ = n := by simp

end Eigenvalues

section Mixed

variable {G Y : Type*} [Group G] (Frob : Y → G) (deg : Y → ℕ) (q₀ : ℝ) {E : Type*} [Field E]
  (ι' : E →+* ℂ)

/-- **Pointwise mixedness of weights `≤ w` of a representation**: every eigenvalue of
`τ(Frob y)` read along `ι'` has absolute value at most `q₀ ^ (deg y · w / 2)`. -/
public def IsFrobeniusMixedLE {N : ℕ} (τ : G →* GL (Fin N) E) (w : ℝ) : Prop :=
  ∀ (y : Y) (z : ℂ), (((τ (Frob y) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).charpoly.map
    ι').IsRoot z → ‖z‖ ≤ q₀ ^ ((deg y : ℝ) * w / 2)

variable {Frob deg q₀ ι'}

/-- Weights add in tensor products. -/
public theorem IsFrobeniusMixedLE.kronecker (hq₀ : 0 < q₀) {a b : ℕ} {τ : G →* GL (Fin a) E}
    {τ' : G →* GL (Fin b) E} {w w' : ℝ} (h : IsFrobeniusMixedLE Frob deg q₀ ι' τ w)
    (h' : IsFrobeniusMixedLE Frob deg q₀ ι' τ' w') :
    IsFrobeniusMixedLE Frob deg q₀ ι' (kroneckerRepresentation τ τ') (w + w') := by
  intro y z hz
  have := norm_le_mul_of_isRoot_charpoly_kroneckerMonoidHom ι' _ _
    (Real.rpow_nonneg hq₀.le _) (Real.rpow_nonneg hq₀.le _) (h y) (h' y) z hz
  rwa [← Real.rpow_add hq₀, ← add_div, ← mul_add] at this

/-- The trivial one-dimensional representation `τ^{⊗ 0}` has weight `0`. -/
public theorem isFrobeniusMixedLE_tensorPowerRepresentation_zero {a : ℕ} (τ : G →* GL (Fin a) E) :
    IsFrobeniusMixedLE Frob deg q₀ ι' (tensorPowerRepresentation τ 0) 0 := by
  intro y z hz
  rw [mul_zero, zero_div, Real.rpow_zero]
  exact norm_le_one_of_isRoot_charpoly_one ι' z hz

/-- Weights multiply under tensor powers. -/
public theorem IsFrobeniusMixedLE.tensorPower (hq₀ : 0 < q₀) {a : ℕ} {τ : G →* GL (Fin a) E}
    {w : ℝ} (h : IsFrobeniusMixedLE Frob deg q₀ ι' τ w) (k : ℕ) :
    IsFrobeniusMixedLE Frob deg q₀ ι' (tensorPowerRepresentation τ k) (k * w) := by
  induction k with
  | zero => simpa using isFrobeniusMixedLE_tensorPowerRepresentation_zero τ
  | succ k ih =>
    have := ih.kronecker hq₀ h
    rwa [show (k : ℝ) * w + w = ((k + 1 : ℕ) : ℝ) * w by push_cast; ring] at this

/-- Permutation representations have weight `0`. -/
public theorem isFrobeniusMixedLE_permMatrixRepresentation {X : Type*} [MulAction G X]
    [DecidableEq X] {n : ℕ} (e : Fin n ≃ X) :
    IsFrobeniusMixedLE Frob deg q₀ ι' (permMatrixRepresentation e E) 0 := by
  intro y z hz
  rw [mul_zero, zero_div, Real.rpow_zero]
  exact norm_le_one_of_isRoot_charpoly_permMatrix ι' e _ z hz

/-- **Purity passes to the contragredient with the opposite weight.** -/
public theorem isFrobeniusMixedLE_contragredient (hq₀ : 0 < q₀) {a : ℕ} {τ : G →* GL (Fin a) E}
    {w : ℝ} (h : ∀ (y : Y) (z : ℂ), (((τ (Frob y) : GL (Fin a) E) :
      Matrix (Fin a) (Fin a) E).charpoly.map ι').IsRoot z → ‖z‖ = q₀ ^ ((deg y : ℝ) * w / 2)) :
    IsFrobeniusMixedLE Frob deg q₀ ι' (contragredient τ) (-w) := by
  intro y z hz
  set u : GL (Fin a) ℂ := Units.map (ι'.mapMatrix : Matrix (Fin a) (Fin a) E →+*
    Matrix (Fin a) (Fin a) ℂ).toMonoidHom (τ (Frob y)) with hu
  have hinv : ((u⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
      (((τ (Frob y))⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map ι' := by
    rw [hu, ← map_inv]
    rfl
  have hz' : z ∈ spectrum ℂ ((u⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) := by
    rw [hinv, Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
    rwa [contragredient_val, Matrix.charpoly_transpose] at hz
  have hzinv : z⁻¹ ∈ spectrum ℂ ((u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) := by
    rw [← spectrum.inv₀_mem_inv_iff, inv_inv]
    exact hz'
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hzinv
  have := h y z⁻¹ (by
    rw [← Matrix.charpoly_map]
    exact hzinv)
  rw [norm_inv] at this
  rw [← inv_inv ‖z‖, this, ← Real.rpow_neg hq₀.le]
  ring_nf
  exact le_rfl

end Mixed

section Maps

variable {G : Type*} [Group G] {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- Kronecker products of representations commute with a change of coefficients. -/
theorem kroneckerRepresentation_mapRepresentation {a b : ℕ} (ρ : G →* GL (Fin a) R)
    (ρ' : G →* GL (Fin b) R) :
    kroneckerRepresentation (mapRepresentation f ρ) (mapRepresentation f ρ') =
      mapRepresentation f (kroneckerRepresentation ρ ρ') :=
  MonoidHom.ext fun g => Units.ext (kroneckerRepresentation_mapRepresentation_val f ρ ρ' g)

/-- Tensor powers commute with a change of coefficients. -/
public theorem tensorPowerRepresentation_mapRepresentation {a : ℕ} (τ : G →* GL (Fin a) R)
    (k : ℕ) : tensorPowerRepresentation (mapRepresentation f τ) k =
      mapRepresentation f (tensorPowerRepresentation τ k) := by
  induction k with
  | zero =>
    refine MonoidHom.ext fun g => Units.ext ?_
    change (1 : Matrix (Fin (a ^ 0)) (Fin (a ^ 0)) S) =
      (1 : Matrix (Fin (a ^ 0)) (Fin (a ^ 0)) R).map f
    rw [Matrix.map_one _ (map_zero f) (map_one f)]
  | succ k ih =>
    change kroneckerRepresentation (tensorPowerRepresentation (mapRepresentation f τ) k)
      (mapRepresentation f τ) = mapRepresentation f
        (kroneckerRepresentation (tensorPowerRepresentation τ k) τ)
    rw [ih, kroneckerRepresentation_mapRepresentation]

/-- Permutation representations commute with a change of coefficients. -/
public theorem permMatrixRepresentation_mapRepresentation {X : Type*} [MulAction G X]
    [DecidableEq X] {n : ℕ} (e : Fin n ≃ X) :
    mapRepresentation f (permMatrixRepresentation (G := G) e R) =
      permMatrixRepresentation (G := G) e S := by
  refine MonoidHom.ext fun g => Units.ext ?_
  ext i j
  simp only [mapRepresentation_val, permMatrixRepresentation_val, permMatrix, Matrix.map_apply,
    Matrix.of_apply]
  split_ifs <;> simp

end Maps

section Continuity

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace F]
  [IsTopologicalRing F]

/-- `Res_b τ^{⊗ k}` is continuous when `Res_b τ` is. -/
public theorem continuous_restrictScalarsRep_tensorPowerRepresentation {a : ℕ}
    {τ : G →* GL (Fin a) E} (hτ : Continuous (restrictScalarsRep b τ)) (k : ℕ) :
    Continuous (restrictScalarsRep b (tensorPowerRepresentation τ k)) := by
  induction k with
  | zero =>
    have : restrictScalarsRep b (tensorPowerRepresentation τ 0) = 1 :=
      MonoidHom.ext fun g => by
        change Units.map (restrictScalarsMonoidHom b _) ((1 : G →* GL (Fin (a ^ 0)) E) g) = 1
        rw [MonoidHom.one_apply, map_one]
    rw [this]
    exact continuous_const
  | succ k ih => exact continuous_restrictScalarsRep_kroneckerRepresentation b ih hτ

omit [IsTopologicalRing F] in
/-- **`Res_b E[G/O]` is continuous** for an open subgroup `O`: the permutation matrices are
locally constant. -/
public theorem continuous_restrictScalarsRep_permMatrixRepresentation (O : Subgroup G)
    (hO : IsOpen (O : Set G)) [DecidableEq (G ⧸ O)] {n : ℕ} (e : Fin n ≃ G ⧸ O) :
    Continuous (restrictScalarsRep b (permMatrixRepresentation (G := G) e E)) := by
  have := QuotientGroup.discreteTopology hO
  refine continuous_restrictScalarsRep b _ (IsLocallyConstant.continuous ?_)
  have hact : IsLocallyConstant fun g : G => fun j : Fin n => g • e j := by
    refine (IsLocallyConstant.iff_continuous _).2 (continuous_pi fun j => ?_)
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e j)
    have : (fun g : G => g • e j) = fun g => ((g * x : G) : G ⧸ O) := by
      funext g
      rw [← hx]
      rfl
    rw [this]
    exact QuotientGroup.continuous_mk.comp
      ((continuous_id.mul continuous_const : Continuous fun g : G => g * x))
  convert hact.comp fun s : Fin n → G ⧸ O =>
    restrictScalarsMatrix b (Matrix.of fun i j => if e i = s j then (1 : E) else 0) using 1
  funext g
  rfl

end Continuity

section Reduction

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [IsSepClosure K L] [Algebra A L] [IsScalarTower A K L]
  (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [IsDomain A] [IsDiscreteValuationRing A] [P.IsMaximal]
  [Finite (IsLocalRing.ResidueField A)] in
/-- An element of the decomposition group normalizes the inertia group. -/
public theorem mem_normalizer_inertia (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    Fr ∈ Subgroup.normalizer (P.inertia Gal(L/K) : Set Gal(L/K)) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  have h := Ideal.inertia_smul (M := Gal(L/K)) Fr P
  rw [MulAction.mem_stabilizer_iff.1 hFrD] at h
  intro σ
  constructor
  · intro hσ
    rw [h]
    exact ⟨σ, hσ, rfl⟩
  · intro hσ
    rw [h] at hσ
    obtain ⟨τ, hτ, hτσ⟩ := hσ
    have : τ = σ := by
      simpa [MulAut.conj_apply] using hτσ
    rwa [← this]

omit [IsDomain A] [IsDiscreteValuationRing A] [P.IsMaximal]
  [Finite (IsLocalRing.ResidueField A)] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] in
/-- The image of an element of the decomposition group normalizes the image of the inertia
group. -/
public theorem map_inv_mem_normalizer_map_inertia (φ : Gal(L/K) →* G) (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    φ Fr⁻¹ ∈ Subgroup.normalizer (((P.inertia Gal(L/K)).map φ : Subgroup G) : Set G) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  have hN := mem_normalizer_inertia A K L P Fr hFrD
  rw [map_inv]
  refine Subgroup.inv_mem _ ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨Fr * σ * Fr⁻¹, (Subgroup.mem_normalizer_iff.1 hN σ).1 hσ, by simp [map_mul, map_inv]⟩
  · rintro ⟨σ, hσ, hσh⟩
    refine ⟨Fr⁻¹ * σ * Fr, (Subgroup.mem_normalizer_iff''.1 hN σ).1 hσ, ?_⟩
    simp only [map_mul, map_inv, hσh]
    group

variable {Y : Type*} (Frob : Y → G) (deg : Y → ℕ) (q₀ : ℝ)

/-- **The weak estimate**: for every representation `τ` of `G` whose restriction of scalars is
continuous and which is mixed of weights `≤ w'` at the `Frob y`, the eigenvalues of `τ(φ Fr⁻¹)`,
read along `ι'`, on the vectors fixed by `τ(φ I)` are bounded by `q ^ ((w' + 2) / 2)`, `q` the
order of the residue field of `A`.  (This is the global input of Weil II 1.8.4: the local
invariants inject into `H¹_c` of the open curve, whose weights are `≤ w' + 2`.) -/
public def WeakInertiaBound {ℓ : ℕ} [Fact ℓ.Prime] (φ : Gal(L/K) →* G) (Fr : Gal(L/K))
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)
    (ι' : E →+* ℂ) : Prop :=
  letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  ∀ (N : ℕ) (τ : G →* GL (Fin N) E), Continuous (restrictScalarsRep b τ) → ∀ w' : ℝ,
    IsFrobeniusMixedLE Frob deg q₀ ι' τ w' → ∀ Y : Fin N → ℂ, Y ≠ 0 →
    (∀ σ ∈ P.inertia Gal(L/K),
      ((τ (φ σ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map ι' *ᵥ Y = Y) →
    ∀ μ : ℂ, ((τ (φ Fr⁻¹) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map ι' *ᵥ Y = μ • Y →
      ‖μ‖ ≤ (Nat.card (IsLocalRing.ResidueField A) : ℝ) ^ ((w' + 2) / 2)

variable {Frob deg q₀} {ℓ : ℕ} [Fact ℓ.Prime]

omit [P.IsMaximal] in
/-- **The bound on the invariants of an open subgroup of inertia, from the weak estimate.**  Let
`W` be mixed of weights `≤ v`, `O` an open subgroup of `G`, `f > 0` with `φ(Fr) ^ f ∈ O`, and `Y`
a nonzero vector fixed by `W(φ σ)` for the `σ ∈ I` with `φ σ ∈ O`.  If `W(φ Fr⁻¹) ^ f Y = c Y`,
then `|c| ≤ (q ^ (v / 2)) ^ f`.  Proof: `Y^{⊗ k}` twisted by the permutation module `E[G/O]` is
`φ(I)`-invariant in `W^{⊗ k} ⊗ E[G/O]`, mixed of weights `≤ k v`, with `c ^ k` an eigenvalue of
`φ(Fr⁻¹) ^ f`; the weak estimate gives `|c| ^ k ≤ q ^ f ((q ^ (v / 2)) ^ f) ^ k` for all
`k > 0`. -/
public theorem norm_le_rpow_pow_of_weakInertiaBound (φ : Gal(L/K) →* G) {E : Type*} [Field E]
    [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ι' : E →+* ℂ) (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P) (hq₀ : 0 < q₀)
    (hweak : WeakInertiaBound A K L P Frob deg q₀ φ Fr E b ι') {a : ℕ} (W : G →* GL (Fin a) E)
    (hW : Continuous (restrictScalarsRep b W)) {v : ℝ}
    (hWmix : IsFrobeniusMixedLE Frob deg q₀ ι' W v) (O : Subgroup G) (hO : IsOpen (O : Set G))
    (f : ℕ) (hf : 0 < f) (hFrO : φ Fr ^ f ∈ O) (Y : Fin a → ℂ) (hY : Y ≠ 0)
    (hYfix : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ σ ∈ P.inertia Gal(L/K), φ σ ∈ O →
        ((W (φ σ) : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map ι' *ᵥ Y = Y)
    (c : ℂ)
    (hc : ((W (φ Fr⁻¹) ^ f : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map ι' *ᵥ Y = c • Y) :
    ‖c‖ ≤ ((Nat.card (IsLocalRing.ResidueField A) : ℝ) ^ (v / 2)) ^ f := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField A) : ℝ) with hq_def
  have hq : 0 < q := by rw [hq_def]; exact_mod_cast Nat.card_pos
  have : Finite (G ⧸ O) := Subgroup.quotient_finite_of_isOpen O hO
  let e : Fin (Nat.card (G ⧸ O)) ≃ G ⧸ O := (Finite.equivFin _).symm
  set I : Subgroup G := (P.inertia Gal(L/K)).map φ with hI
  have hN := mem_normalizer_inertia A K L P Fr hFrD
  have hFrN : φ Fr⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
    map_inv_mem_normalizer_map_inertia A K L P φ Fr hFrD
  set x₀ : G ⧸ O := ((1 : G) : G ⧸ O)
  have key : ∀ k : ℕ, 0 < k → ‖c‖ ^ k ≤ q ^ (f : ℝ) * ((q ^ (v / 2)) ^ f) ^ k := by
    intro k hk
    set ψ := tensorPowerRepresentation (mapRepresentation ι' W) k with hψ
    have hψval : ∀ g, ((ψ g : GL (Fin (a ^ k)) ℂ) : Matrix (Fin (a ^ k)) (Fin (a ^ k)) ℂ) *ᵥ
        kroneckerPowVec Y k = kroneckerPowVec
          (((W g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map ι' *ᵥ Y) k := fun g => by
      rw [hψ, tensorPowerRepresentation_mulVec_kroneckerPowVec]
      rfl
    have hfix : ∀ h ∈ I, h • x₀ = x₀ → ((ψ h : GL (Fin (a ^ k)) ℂ) :
        Matrix (Fin (a ^ k)) (Fin (a ^ k)) ℂ) *ᵥ kroneckerPowVec Y k = kroneckerPowVec Y k := by
      rintro h ⟨σ, hσ, rfl⟩ hx
      have h1 : (φ σ * 1)⁻¹ * 1 ∈ O :=
        QuotientGroup.eq.1 (by rwa [MulAction.Quotient.smul_mk] at hx)
      have hσO : φ σ ∈ O := by simpa using h1
      rw [hψval, hYfix σ hσ hσO]
    set F : G := φ Fr⁻¹ ^ f with hF
    have hFx : F • x₀ = x₀ := by
      rw [MulAction.Quotient.smul_mk]
      refine QuotientGroup.eq.2 ?_
      simpa [smul_eq_mul, hF, map_inv, inv_pow] using hFrO
    have hFN : F ∈ Subgroup.normalizer (I : Set G) := Subgroup.pow_mem _ hFrN f
    have hFY : ((ψ F : GL (Fin (a ^ k)) ℂ) : Matrix (Fin (a ^ k)) (Fin (a ^ k)) ℂ) *ᵥ
        kroneckerPowVec Y k = c ^ k • kroneckerPowVec Y k := by
      rw [hψval, hF, map_pow, hc, kroneckerPowVec_smul]
    obtain ⟨ξ, hξ0, hξI, hξF⟩ := exists_permutationTwist_vector e ψ I x₀ (kroneckerPowVec Y k)
      (kroneckerPowVec_ne_zero hY k) hfix
    have hξFr := hξF F (c ^ k) hFx hFN hFY
    set χ := kroneckerRepresentation ψ (permMatrixRepresentation (G := G) e ℂ) with hχ
    set τ := kroneckerRepresentation (tensorPowerRepresentation W k)
      (permMatrixRepresentation (G := G) e E) with hτ
    have hτmap : ∀ g, ((τ g : GL (Fin (a ^ k * Nat.card (G ⧸ O))) E) :
        Matrix (Fin (a ^ k * Nat.card (G ⧸ O))) (Fin (a ^ k * Nat.card (G ⧸ O))) E).map ι' =
        ((χ g : GL (Fin (a ^ k * Nat.card (G ⧸ O))) ℂ) :
          Matrix (Fin (a ^ k * Nat.card (G ⧸ O))) (Fin (a ^ k * Nat.card (G ⧸ O))) ℂ) := by
      intro g
      rw [hχ, hψ, tensorPowerRepresentation_mapRepresentation,
        ← permMatrixRepresentation_mapRepresentation ι' e,
        kroneckerRepresentation_mapRepresentation]
      rfl
    set A' := ((χ (φ Fr⁻¹) : GL (Fin (a ^ k * Nat.card (G ⧸ O))) ℂ) :
      Matrix (Fin (a ^ k * Nat.card (G ⧸ O))) (Fin (a ^ k * Nat.card (G ⧸ O))) ℂ) with hA'
    let Z : Submodule ℂ (Fin (a ^ k * Nat.card (G ⧸ O)) → ℂ) :=
      { carrier := {z | ∀ σ ∈ P.inertia Gal(L/K),
          ((χ (φ σ) : GL (Fin (a ^ k * Nat.card (G ⧸ O))) ℂ) :
            Matrix (Fin (a ^ k * Nat.card (G ⧸ O))) (Fin (a ^ k * Nat.card (G ⧸ O))) ℂ) *ᵥ z = z}
        add_mem' := fun hx hy σ hσ => by
          simp only [Set.mem_ofPred_eq] at hx hy ⊢
          rw [Matrix.mulVec_add, hx σ hσ, hy σ hσ]
        zero_mem' := fun σ _ => Matrix.mulVec_zero _
        smul_mem' := fun t z hz σ hσ => by
          simp only [Set.mem_ofPred_eq] at hz ⊢
          rw [Matrix.mulVec_smul, hz σ hσ] }
    have hZ : ∀ z ∈ Z, A' *ᵥ z ∈ Z := by
      intro z hz σ hσ
      have hσ' : Fr * σ * Fr⁻¹ ∈ P.inertia Gal(L/K) := (Subgroup.mem_normalizer_iff.1 hN σ).1 hσ
      rw [hA', Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul,
        show φ σ * φ Fr⁻¹ = φ Fr⁻¹ * φ (Fr * σ * Fr⁻¹) by simp only [map_mul, map_inv]; group,
        map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hz _ hσ']
    have hξZ : ξ ∈ Z := fun σ hσ => hξI (φ σ) ⟨σ, hσ, rfl⟩
    have hpow : (A' ^ f) *ᵥ ξ = c ^ k • ξ := by
      rw [hA', ← Units.val_pow_eq_pow_val, ← map_pow]
      exact hξFr
    obtain ⟨η, hηZ, hη0, μ, hAη, hμ⟩ :=
      exists_mulVec_eq_smul_pow_eq_of_pow_mulVec_eq_smul A' Z hZ hξZ hξ0 hf hpow
    have hτc : Continuous (restrictScalarsRep b τ) :=
      continuous_restrictScalarsRep_kroneckerRepresentation b
        (continuous_restrictScalarsRep_tensorPowerRepresentation b hW k)
        (continuous_restrictScalarsRep_permMatrixRepresentation b O hO e)
    have hτmix : IsFrobeniusMixedLE Frob deg q₀ ι' τ (k * v) := by
      simpa using (hWmix.tensorPower hq₀ k).kronecker hq₀
        (isFrobeniusMixedLE_permMatrixRepresentation (Frob := Frob) (deg := deg) (q₀ := q₀)
          (ι' := ι') e)
    have hμle := hweak _ τ hτc (k * v) hτmix η hη0 (fun σ hσ => by rw [hτmap]; exact hηZ σ hσ) μ
      (by rw [hτmap]; exact hAη)
    have hexp : (q ^ ((k * v + 2) / 2)) ^ f = q ^ (f : ℝ) * ((q ^ (v / 2)) ^ f) ^ k := by
      simp only [← Real.rpow_mul_natCast hq.le]
      rw [← Real.rpow_add hq]
      congr 1
      ring
    calc ‖c‖ ^ k = ‖μ‖ ^ f := by rw [← norm_pow, ← norm_pow, hμ]
      _ ≤ (q ^ ((k * v + 2) / 2)) ^ f := pow_le_pow_left₀ (norm_nonneg μ) hμle f
      _ = _ := hexp
  exact le_of_forall_pow_le (pow_nonneg (Real.rpow_nonneg hq.le _) f) key

/-- **Weil II, Théorème 1.8.4, from the weak estimate.**  Let `ρ : G → GL_r(E)`, with `Res_b ρ`
continuous, be pure of the integer weight `w` along `ι'` at the Frobenius elements `Frob y`
(eigenvalues of absolute value `q₀ ^ (deg y · w / 2)`).  Under the weak estimate, every eigenvalue
`α` of `ρ(φ Fr⁻¹)` on the `φ(I)`-invariants satisfies `|α|² q ^ i = q ^ w` for some `i ∈ ℕ`: the
local invariants are mixed of integer weights `≤ w`. -/
public theorem exists_norm_sq_mul_pow_eq_of_weakInertiaBound
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A)) (φ : Gal(L/K) →* G) (hφ : Continuous φ)
    {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {r : ℕ}
    (ρ : G →* GL (Fin r) E) (hρ : Continuous (restrictScalarsRep b ρ)) (ι' : E →+* ℂ)
    (Fr : Gal(L/K))
    (hFrD : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L/K) P)
    (hFr : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    (hq₀ : 0 < q₀) (w : ℤ)
    (hpure : ∀ (y : Y) (z : ℂ), (((ρ (Frob y) : GL (Fin r) E) :
      Matrix (Fin r) (Fin r) E).charpoly.map ι').IsRoot z → ‖z‖ = q₀ ^ ((deg y : ℝ) * w / 2))
    (hweak : WeakInertiaBound A K L P Frob deg q₀ φ Fr E b ι')
    {v : Fin r → ℂ} (hv0 : v ≠ 0)
    (hvI : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ σ ∈ P.inertia Gal(L/K),
        ((ρ (φ σ) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map ι' *ᵥ v = v)
    {α : ℂ} (hα : ((ρ (φ Fr⁻¹) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map ι' *ᵥ v = α • v) :
    ∃ i : ℕ, ‖α‖ ^ 2 * (Nat.card (IsLocalRing.ResidueField A) : ℝ) ^ i =
      (Nat.card (IsLocalRing.ResidueField A) : ℝ) ^ (w : ℝ) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  set q : ℝ := (Nat.card (IsLocalRing.ResidueField A) : ℝ) with hq_def
  have hq : 0 < q := by rw [hq_def]; exact_mod_cast Nat.card_pos
  have hmix : IsFrobeniusMixedLE Frob deg q₀ ι' ρ w := fun y z hz => (hpure y z hz).le
  have hmix' : IsFrobeniusMixedLE Frob deg q₀ ι' (contragredient ρ) (-w) :=
    isFrobeniusMixedLE_contragredient hq₀ hpure
  have hρ₂ := continuous_restrictScalarsRep_kroneckerRepresentation b hρ hρ
  have hρ' := continuous_restrictScalarsRep_contragredient b hρ
  have hρ₃ := continuous_restrictScalarsRep_kroneckerRepresentation b hρ' hρ'
  refine exists_norm_sq_mul_pow_eq_of_forall_isOpen_restrictScalars A K L P hℓ φ hφ b ρ hρ hρ₂ hρ₃
    ι' (Q := q ^ (w : ℝ)) (Q' := q ^ (-(w : ℝ))) (Real.rpow_nonneg hq.le _)
    (Real.rpow_nonneg hq.le _) (by rw [← Real.rpow_add hq, add_neg_cancel, Real.rpow_zero]) Fr hFrD
    hFr ?_ ?_ hv0 hvI hα
  all_goals
    intro O hO f hf hFrO Y hY hYfix c hc
    have := norm_le_rpow_pow_of_weakInertiaBound A K L P φ b ι' Fr hFrD hq₀ hweak _ (by assumption)
      (by apply IsFrobeniusMixedLE.kronecker hq₀ <;> assumption)
      O hO f hf hFrO Y hY hYfix c hc
    rwa [show ∀ s : ℝ, (s + s) / 2 = s from fun s => by ring] at this

end Reduction

end Stacks.EtaleCohomology

end
