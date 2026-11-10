module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import StacksFrontier.RingTheory.GradedCompletion.PowerSeries
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.MvPolynomial.MonicSequenceRegular
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology
public import StacksFrontier.RingTheory.MvPowerSeries.PolynomialTruncation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a graded algebra to a power series ring

Let `k` be a field, `P = k[X₁, …, Xₙ]` and `R = k⟦X₁, …, Xₙ⟧`, the completion of `P` at the ideal
of the variables. Let `Γ` be an `ℕ`-graded `k`-algebra which is a finite `P`-module through an
algebra map sending every variable into degree one. This file shows that `S = R ⊗_P Γ` embeds in
`Γ⟦T⟧` through `r ⊗ γ ↦ r(x₁T, …, xₙT) · ∑_d γ_d T^d`, where `xᵢ` is the image of `Xᵢ` in `Γ`. The
image consists of series whose coefficient of `T^d` is homogeneous of degree `d`. Consequently

* `S` is a domain when `Γ` is (and it is a finite `R`-module, by base change);
* an Artin–Schreier type equation `γ = h^p - h` with `γ = α/β`, `α, β ∈ Γ_d`, solvable in the
  fraction field of `S` is already solvable with `h = α'/β'`, `α', β' ∈ Γ_{d'}`: compare lowest
  degree coefficients in `Γ⟦T⟧`.

The injectivity of `S → Γ⟦T⟧` is the Krull intersection theorem for the finite `R`-module `S`,
together with the fact that an element of `Γ` with no components below degree `N + D` lies in
`(X)^N Γ` (`Stacks.GradedCompletion.mem_pow_smul_top_of_decompose_eq_zero`).

The file also records the properties of `R` itself used together with this: it is a Noetherian
henselian local ring, flat over `P`, on which the variables form a weakly regular sequence, and
its residue field is `k`.

## Main results

* `MvPowerSeries.instHenselianLocalRing`, `MvPowerSeries.isSepClosed_residueField`,
  `MvPowerSeries.flat_mvPolynomial`, `MvPowerSeries.isWeaklyRegular_ofFn_X`,
  `MvPowerSeries.isRegular_ofFn_X`.
* `Stacks.GradedCompletion.completionMap_injective`: `R ⊗_P Γ → Γ⟦T⟧` is injective.
* `Stacks.GradedCompletion.isDomain_tensorProduct`: `R ⊗_P Γ` is a domain if `Γ` is.
* `Stacks.GradedCompletion.exists_homogeneous_of_fractionRing`: the persistence statement.
-/

@[expose] public section

open DirectSum IsLocalRing Polynomial RingTheory.Sequence TensorProduct

/-! ### The power series ring -/

namespace MvPowerSeries

variable (k : Type*) [Field k] (n : ℕ)

/-- A power series ring in finitely many variables over a field is henselian. -/
instance instHenselianLocalRing : HenselianLocalRing (MvPowerSeries (Fin n) k) := by
  have : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  have := isAdicComplete_maximalIdeal n k this
  exact henselianLocalRing_of_isAdicComplete_maximalIdeal _

/-- The residue field of `k⟦X₁, …, Xₙ⟧` is separably closed when `k` is. -/
theorem isSepClosed_residueField [IsSepClosed k] :
    IsSepClosed (ResidueField (MvPowerSeries (Fin n) k)) := by
  have hsurj : Function.Surjective
      (constantCoeff : MvPowerSeries (Fin n) k →+* k) := fun c => ⟨C c, by simp⟩
  exact IsSepClosed.of_ringEquiv
    ((Ideal.quotEquivOfEq (ker_eq_maximalIdeal _ hsurj).symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj))

/-- The image of a polynomial in the power series ring is the polynomial itself. -/
theorem algebraMap_mvPolynomial_apply (q : MvPolynomial (Fin n) k) :
    algebraMap (MvPolynomial (Fin n) k) (MvPowerSeries (Fin n) k) q = q := by
  rw [algebraMap_apply', Algebra.algebraMap_self, map_id, RingHom.id_apply]

/-- A polynomial ring over a coefficient ring of `k` maps to `k⟦X₁, …, Xₙ⟧` variable to
variable. -/
theorem algebraMap_mvPolynomial_X {A : Type*} [CommRing A] [Algebra A k] (i : Fin n) :
    algebraMap (MvPolynomial (Fin n) A) (MvPowerSeries (Fin n) k) (MvPolynomial.X i) = X i := by
  rw [algebraMap_apply', MvPolynomial.coe_X, map_X]

/-- `k⟦X₁, …, Xₙ⟧` is flat over `k[X₁, …, Xₙ]`: it is the adic completion of a Noetherian ring
at the ideal of the variables. -/
instance flat_mvPolynomial :
    Module.Flat (MvPolynomial (Fin n) k) (MvPowerSeries (Fin n) k) :=
  Module.Flat.of_linearEquiv (R := MvPolynomial (Fin n) k)
    (M := AdicCompletion (MvPolynomial.idealOfVars (Fin n) k) (MvPolynomial (Fin n) k))
    (toAdicCompletionAlgEquiv (Fin n) k).toLinearEquiv

/-- The variables form a weakly regular sequence in `k⟦X₁, …, Xₙ⟧`. -/
@[ega "0 17.1.4" "(iii)", sga "3 VIIB 5.5.2" "partial"]
theorem isWeaklyRegular_ofFn_X :
    IsWeaklyRegular (MvPowerSeries (Fin n) k)
      (List.ofFn (X : Fin n → MvPowerSeries (Fin n) k)) := by
  have h := (MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic n (fun _ => (Polynomial.X : k[X]))
    fun _ => Polynomial.monic_X).map_algebraMap_of_flat (T := MvPowerSeries (Fin n) k)
  simpa [List.map_ofFn, Function.comp_def, algebraMap_mvPolynomial_apply] using h

/-- The ideal generated by the variables of `k⟦X₁, …, Xₙ⟧` is proper. -/
private theorem span_range_X_ne_top :
    Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) k)) ≠ ⊤ := by
  rw [← maximalIdeal_eq_span_range_X k n]
  exact (maximalIdeal.isMaximal _).ne_top

/-- The variables form a regular sequence in `k⟦X₁, …, Xₙ⟧`. -/
@[ega "0 17.1.4" "(iii)", sga "3 VIIB 5.5.2" "partial"]
theorem isRegular_ofFn_X :
    IsRegular (MvPowerSeries (Fin n) k) (List.ofFn (X : Fin n → MvPowerSeries (Fin n) k)) := by
  refine ⟨isWeaklyRegular_ofFn_X k n, fun htop => span_range_X_ne_top k n ?_⟩
  have hspan : Ideal.ofList (List.ofFn (X : Fin n → MvPowerSeries (Fin n) k)) =
      Ideal.span (Set.range X) := by
    simp [Ideal.ofList, List.mem_ofFn, Set.range]
  rw [← hspan, ← Ideal.mul_top (Ideal.ofList _), ← smul_eq_mul, ← htop]

end MvPowerSeries

/-! ### The embedding of `R ⊗_P Γ` into `Γ⟦T⟧` -/

namespace Stacks.GradedCompletion

variable {k Γ : Type*} [Field k] [CommRing Γ] [Algebra k Γ] (𝒜 : ℕ → Submodule k Γ)
  [GradedAlgebra 𝒜] {n : ℕ} [Algebra (MvPolynomial (Fin n) k) Γ]
  [IsScalarTower k (MvPolynomial (Fin n) k) Γ]

/-- The substitution `Xᵢ ↦ xᵢ T`, `k⟦X₁, …, Xₙ⟧ → Γ⟦T⟧`, where `xᵢ` is the image of `Xᵢ`. -/
noncomputable def seriesSubst : MvPowerSeries (Fin n) k →ₐ[k] PowerSeries Γ :=
  MvPowerSeries.substAlgHom (R := k) (a := fun i =>
      (PowerSeries.C (algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i)) * PowerSeries.X :
        PowerSeries Γ))
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      change PowerSeries.constantCoeff _ = 0
      simp)

omit [GradedAlgebra 𝒜] [IsScalarTower k (MvPolynomial (Fin n) k) Γ] in
/-- The substitution sends the variable `Xᵢ` to `xᵢ T`. -/
theorem seriesSubst_X (i : Fin n) :
    seriesSubst (Γ := Γ) (MvPowerSeries.X (R := k) i) =
      PowerSeries.C (algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i)) * PowerSeries.X :=
  MvPowerSeries.substAlgHom_X _ i

variable {𝒜}

/-- On polynomials, the substitution agrees with `γ ↦ ∑_d γ_d T^d` after mapping to `Γ`. -/
theorem seriesSubst_coe (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    (q : MvPolynomial (Fin n) k) :
    seriesSubst (Γ := Γ) (q : MvPowerSeries (Fin n) k) =
      toPowerSeries 𝒜 (algebraMap (MvPolynomial (Fin n) k) Γ q) := by
  rw [seriesSubst, MvPowerSeries.substAlgHom_coe]
  change MvPolynomial.aeval _ q =
    ((toPowerSeries 𝒜).comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) Γ)) q
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [MvPolynomial.aeval_X, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', toPowerSeries_of_mem 𝒜
    (hX i)]
  ext m
  simp [PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]

/-- The ideal of the variables of `k⟦X₁, …, Xₙ⟧`. -/
local notation "𝔍" => Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k))

omit [GradedAlgebra 𝒜] [IsScalarTower k (MvPolynomial (Fin n) k) Γ] in
/-- The substitution sends the `N`-th power of the ideal of variables into `T^N Γ⟦T⟧`. -/
theorem X_pow_dvd_seriesSubst {N : ℕ} {r : MvPowerSeries (Fin n) k} (hr : r ∈ 𝔍 ^ N) :
    PowerSeries.X ^ N ∣ seriesSubst (Γ := Γ) r := by
  have hmap : Ideal.map (seriesSubst (Γ := Γ)) 𝔍 ≤ Ideal.span {PowerSeries.X} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, seriesSubst_X, Ideal.mem_span_singleton]
    exact dvd_mul_left _ _
  have : seriesSubst (Γ := Γ) r ∈ Ideal.span {(PowerSeries.X : PowerSeries Γ) ^ N} := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hmap N (Ideal.map_pow (seriesSubst (Γ := Γ)) 𝔍 N ▸
      Ideal.mem_map_of_mem _ hr)
  exact Ideal.mem_span_singleton.mp this

/-- The coefficient of `T^d` in the substitution is homogeneous of degree `d`. -/
theorem seriesSubst_mem_homogeneousSeries
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    (r : MvPowerSeries (Fin n) k) : seriesSubst (Γ := Γ) r ∈ homogeneousSeries 𝒜 := by
  intro d
  obtain ⟨q, hq⟩ :=
    Stacks.MvPowerSeries.RegularParameters.exists_polynomial_sub_mem_pow_span_range_X (d + 1) r
  obtain ⟨g, hg⟩ := X_pow_dvd_seriesSubst (Γ := Γ) hq
  rw [map_sub, sub_eq_iff_eq_add, seriesSubst_coe hX] at hg
  rw [hg, map_add, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), zero_add,
    coeff_toPowerSeries]
  exact (decompose 𝒜 _ d).2

variable (𝒜) in
/-- The `k`-algebra map `R ⊗_P Γ → Γ⟦T⟧`, `r ⊗ γ ↦ r(x₁T, …, xₙT) · ∑_d γ_d T^d`. -/
noncomputable def completionMap
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1) :
    MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ →+* PowerSeries Γ :=
  letI : Algebra (MvPolynomial (Fin n) k) (PowerSeries Γ) :=
    ((toPowerSeries 𝒜).toRingHom.comp (algebraMap (MvPolynomial (Fin n) k) Γ)).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k) (PowerSeries Γ) :=
    ⟨fun a b c => by rw [smul_eq_mul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      mul_assoc]⟩
  (Algebra.TensorProduct.lift
    ({ (seriesSubst (Γ := Γ)).toRingHom with
      commutes' := fun q => by
        change seriesSubst (Γ := Γ) _ = toPowerSeries 𝒜 _
        rw [MvPowerSeries.algebraMap_mvPolynomial_apply, seriesSubst_coe hX] } :
      MvPowerSeries (Fin n) k →ₐ[MvPolynomial (Fin n) k] PowerSeries Γ)
    ({ (toPowerSeries 𝒜).toRingHom with commutes' := fun _ => rfl } :
      Γ →ₐ[MvPolynomial (Fin n) k] PowerSeries Γ)
    fun _ _ => Commute.all _ _).toRingHom

/-- The map `R ⊗_P Γ → Γ⟦T⟧` sends `r ⊗ γ` to `r(x₁T, …, xₙT) · ∑_d γ_d T^d`. -/
@[simp]
theorem completionMap_tmul
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    (r : MvPowerSeries (Fin n) k) (γ : Γ) :
    completionMap 𝒜 hX (r ⊗ₜ γ) = seriesSubst r * toPowerSeries 𝒜 γ := by
  simp only [completionMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rfl

/-- The image of `R ⊗_P Γ → Γ⟦T⟧` consists of series with homogeneous coefficients. -/
theorem completionMap_mem_homogeneousSeries
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    (s : MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ) :
    completionMap 𝒜 hX s ∈ homogeneousSeries 𝒜 := by
  induction s using TensorProduct.inductionOn with
  | tmul r γ =>
    rw [completionMap_tmul]
    exact mul_mem (seriesSubst_mem_homogeneousSeries hX r) (toPowerSeries_mem_homogeneousSeries 𝒜 γ)
  | add s t hs ht =>
    rw [map_add]
    exact add_mem hs ht

/-- **`R ⊗_P Γ` embeds in `Γ⟦T⟧`.** Let `Γ` be a graded `k`-algebra which is a finite module over
`P = k[X₁, …, Xₙ]` through an algebra map sending each variable into degree one, and
`R = k⟦X₁, …, Xₙ⟧`. Then `r ⊗ γ ↦ r(x₁T, …, xₙT) · ∑_d γ_d T^d` is injective on `R ⊗_P Γ`. -/
theorem completionMap_injective [Module.Finite (MvPolynomial (Fin n) k) Γ]
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1) :
    Function.Injective (completionMap 𝒜 hX) := by
  set S := MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ
  set φ := completionMap 𝒜 hX
  -- the ideal of variables of `P` maps onto that of `R`
  have hmapI : Ideal.map (algebraMap (MvPolynomial (Fin n) k) (MvPowerSeries (Fin n) k))
      (MvPolynomial.idealOfVars (Fin n) k) = 𝔍 := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [MvPowerSeries.algebraMap_mvPolynomial_apply]
  -- `𝔍^N S` maps into `T^N Γ⟦T⟧`
  have hdvd : ∀ N, ∀ s ∈ (𝔍 ^ N • ⊤ : Submodule (MvPowerSeries (Fin n) k) S),
      PowerSeries.X ^ N ∣ φ s := by
    intro N s hs
    refine Submodule.smul_induction_on hs (fun r hr m _ => ?_) (fun x y hx hy => ?_)
    · rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, completionMap_tmul, map_one, mul_one]
      exact (X_pow_dvd_seriesSubst hr).mul_right _
    · rw [map_add]; exact dvd_add hx hy
  -- `(X)^N Γ` maps into `𝔍^N S`
  have hgen : ∀ N, ∀ γ ∈ (MvPolynomial.idealOfVars (Fin n) k ^ N • ⊤ :
      Submodule (MvPolynomial (Fin n) k) Γ),
      (1 : MvPowerSeries (Fin n) k) ⊗ₜ γ ∈ (𝔍 ^ N • ⊤ : Submodule (MvPowerSeries (Fin n) k) S) := by
    intro N γ hγ
    refine Submodule.smul_induction_on hγ (fun q hq γ' _ => ?_) (fun x y hx hy => ?_)
    · rw [TensorProduct.tmul_smul, ← algebraMap_smul (MvPowerSeries (Fin n) k) q]
      refine Submodule.smul_mem_smul ?_ trivial
      rw [← hmapI, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hq
    · rw [TensorProduct.tmul_add]; exact add_mem hx hy
  -- every element of `S` is congruent to an element of `Γ` modulo `𝔍^N S`
  have happrox : ∀ N (s : S), ∃ γ : Γ, s - (1 : MvPowerSeries (Fin n) k) ⊗ₜ γ ∈
      (𝔍 ^ N • ⊤ : Submodule (MvPowerSeries (Fin n) k) S) := by
    intro N s
    induction s using TensorProduct.inductionOn with
    | tmul r γ =>
      obtain ⟨q, hq⟩ :=
        Stacks.MvPowerSeries.RegularParameters.exists_polynomial_sub_mem_pow_span_range_X N r
      refine ⟨q • γ, ?_⟩
      have : r ⊗ₜ[MvPolynomial (Fin n) k] γ - (1 : MvPowerSeries (Fin n) k) ⊗ₜ (q • γ) =
          (r - q) • ((1 : MvPowerSeries (Fin n) k) ⊗ₜ[MvPolynomial (Fin n) k] γ) := by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          Algebra.smul_def, mul_one, MvPowerSeries.algebraMap_mvPolynomial_apply, smul_eq_mul,
          mul_one, TensorProduct.sub_tmul]
      rw [this]
      exact Submodule.smul_mem_smul hq trivial
    | add s t hs ht =>
      obtain ⟨γ, hγ⟩ := hs
      obtain ⟨δ, hδ⟩ := ht
      refine ⟨γ + δ, ?_⟩
      rw [TensorProduct.tmul_add]
      convert add_mem hγ hδ using 1
      abel
  obtain ⟨D, hD⟩ := mem_pow_smul_top_of_decompose_eq_zero 𝒜 hX
  have hall : ∀ s, φ s = 0 → ∀ N, s ∈ (𝔍 ^ N • ⊤ : Submodule (MvPowerSeries (Fin n) k) S) := by
    intro s hs N
    obtain ⟨γ, hγ⟩ := happrox (N + D) s
    have h1 : PowerSeries.X ^ (N + D) ∣ toPowerSeries 𝒜 γ := by
      have := hdvd _ _ hγ
      rw [map_sub, hs, zero_sub, completionMap_tmul, map_one, one_mul, dvd_neg] at this
      exact this
    have h2 := hgen N γ (hD N γ ((X_pow_dvd_toPowerSeries_iff 𝒜).mp h1))
    have h3 : s - (1 : MvPowerSeries (Fin n) k) ⊗ₜ γ ∈
        (𝔍 ^ N • ⊤ : Submodule (MvPowerSeries (Fin n) k) S) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) hγ
    simpa using add_mem h3 h2
  rw [injective_iff_map_eq_zero]
  intro s hs
  have := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := S) 𝔍
    (MvPowerSeries.span_range_X_ne_top k n)
  rw [← Submodule.mem_bot (MvPowerSeries (Fin n) k), ← this, Submodule.mem_iInf]
  exact hall s hs

/-- **`R ⊗_P Γ` is a domain** when `Γ` is a domain which is a finite `P`-module through an algebra
map sending each variable into degree one. It is a finite `R`-module by base change. -/
theorem isDomain_tensorProduct [IsDomain Γ] [Module.Finite (MvPolynomial (Fin n) k) Γ]
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1) :
    IsDomain (MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ) :=
  Function.Injective.isDomain (completionMap 𝒜 hX) (completionMap_injective hX)

/-- In a field, `(a / b) ^ (q + 1) - a / b = (a ^ (q + 1) - a * b ^ q) / b ^ (q + 1)`. -/
private theorem div_pow_succ_sub_div {K : Type*} [Field K] {a b : K} (hb : b ≠ 0) (q : ℕ) :
    (a / b) ^ (q + 1) - a / b = (a ^ (q + 1) - a * b ^ q) / b ^ (q + 1) := by
  rw [eq_div_iff (pow_ne_zero _ hb), sub_mul, ← mul_pow, div_mul_cancel₀ _ hb, pow_succ' b q,
    ← mul_assoc, div_mul_cancel₀ _ hb]

/-- **Persistence of Artin–Schreier type equations.** Let `Γ` be a graded domain which is a finite
`P`-module through an algebra map sending each variable into degree one, let `p ≥ 2`, and let
`α, β ∈ Γ_d` with `β ≠ 0`. If `α/β = h^p - h` for some `h` in the fraction field of
`S = R ⊗_P Γ`, then there are `α', β' ∈ Γ_{d'}` with `β' ≠ 0` and
`β (α'^p - α' β'^{p-1}) = α β'^p`, that is, `α/β = h₀^p - h₀` with `h₀ = α'/β'`. -/
theorem exists_homogeneous_of_fractionRing [IsDomain Γ]
    [Module.Finite (MvPolynomial (Fin n) k) Γ]
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    {p : ℕ} (hp : 2 ≤ p) {d : ℕ} {α β : Γ} (hα : α ∈ 𝒜 d) (hβ : β ∈ 𝒜 d) (hβ0 : β ≠ 0)
    (h : FractionRing (MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ))
    (hh : algebraMap _ (FractionRing _)
        ((1 : MvPowerSeries (Fin n) k) ⊗ₜ[MvPolynomial (Fin n) k] α) =
      algebraMap _ (FractionRing _) ((1 : MvPowerSeries (Fin n) k) ⊗ₜ[MvPolynomial (Fin n) k] β) *
        (h ^ p - h)) :
    ∃ (d' : ℕ) (α' β' : Γ), α' ∈ 𝒜 d' ∧ β' ∈ 𝒜 d' ∧ β' ≠ 0 ∧
      β * (α' ^ p - α' * β' ^ (p - 1)) = α * β' ^ p := by
  have := isDomain_tensorProduct hX
  set S := MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ
  obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := S) h
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hw : algebraMap S (FractionRing S) v ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have heqS : (1 : MvPowerSeries (Fin n) k) ⊗ₜ[MvPolynomial (Fin n) k] α * v ^ (q + 1) =
      (1 : MvPowerSeries (Fin n) k) ⊗ₜ[MvPolynomial (Fin n) k] β * (u ^ (q + 1) - u * v ^ q) := by
    apply IsFractionRing.injective S (FractionRing S)
    simp only [map_mul, map_sub, map_pow]
    rw [hh, div_pow_succ_sub_div hw, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hw)]
  have hmono : ∀ a : Γ, PowerSeries.monomial d a = PowerSeries.C a * PowerSeries.X ^ d := by
    intro a
    ext m
    simp [PowerSeries.coeff_monomial]
  have hφ := congrArg (completionMap 𝒜 hX) heqS
  simp only [map_mul, map_sub, map_pow, completionMap_tmul, map_one, one_mul,
    toPowerSeries_of_mem 𝒜 hα, toPowerSeries_of_mem 𝒜 hβ, hmono] at hφ
  set U := completionMap 𝒜 hX u
  set V := completionMap 𝒜 hX v
  have hV : V ≠ 0 := fun h0 =>
    hv0 (completionMap_injective hX (h0.trans (map_zero (completionMap 𝒜 hX)).symm))
  have key : PowerSeries.C β * (U ^ (q + 1) - U * V ^ (q + 1 - 1)) =
      PowerSeries.C α * V ^ (q + 1) := by
    rw [Nat.add_sub_cancel]
    apply mul_left_cancel₀ (pow_ne_zero d (PowerSeries.X_ne_zero (R := Γ)))
    linear_combination (-1 : PowerSeries Γ) * hφ
  exact exists_homogeneous_of_series_equation 𝒜 hp hβ0
    (completionMap_mem_homogeneousSeries hX u) (completionMap_mem_homogeneousSeries hX v) hV key

/-- **Persistence of Artin–Schreier type equations**, in the fraction field of `Γ`: under the
hypotheses of `exists_homogeneous_of_fractionRing`, `α/β = h₀^p - h₀` in `Frac Γ` with
`h₀ = α'/β'` a quotient of two homogeneous elements of the same degree. -/
theorem exists_div_eq_pow_sub_of_fractionRing [IsDomain Γ]
    [Module.Finite (MvPolynomial (Fin n) k) Γ]
    (hX : ∀ i, algebraMap (MvPolynomial (Fin n) k) Γ (MvPolynomial.X i) ∈ 𝒜 1)
    {p : ℕ} (hp : 2 ≤ p) {d : ℕ} {α β : Γ} (hα : α ∈ 𝒜 d) (hβ : β ∈ 𝒜 d) (hβ0 : β ≠ 0)
    (h : FractionRing (MvPowerSeries (Fin n) k ⊗[MvPolynomial (Fin n) k] Γ))
    (hh : algebraMap _ (FractionRing _)
        ((1 : MvPowerSeries (Fin n) k) ⊗ₜ[MvPolynomial (Fin n) k] α) =
      algebraMap _ (FractionRing _) ((1 : MvPowerSeries (Fin n) k) ⊗ₜ[MvPolynomial (Fin n) k] β) *
        (h ^ p - h)) :
    ∃ (d' : ℕ) (α' β' : Γ), α' ∈ 𝒜 d' ∧ β' ∈ 𝒜 d' ∧ β' ≠ 0 ∧
      algebraMap Γ (FractionRing Γ) α / algebraMap Γ (FractionRing Γ) β =
        (algebraMap Γ (FractionRing Γ) α' / algebraMap Γ (FractionRing Γ) β') ^ p -
          algebraMap Γ (FractionRing Γ) α' / algebraMap Γ (FractionRing Γ) β' := by
  obtain ⟨d', α', β', hα', hβ', hβ'0, heq⟩ :=
    exists_homogeneous_of_fractionRing hX hp hα hβ hβ0 h hh
  refine ⟨d', α', β', hα', hβ', hβ'0, ?_⟩
  have hb : algebraMap Γ (FractionRing Γ) β ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ (FractionRing Γ))).mpr hβ0
  have hb' : algebraMap Γ (FractionRing Γ) β' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Γ (FractionRing Γ))).mpr hβ'0
  have heq' := congrArg (algebraMap Γ (FractionRing Γ)) heq
  simp only [map_mul, map_sub, map_pow] at heq'
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel] at heq'
  set a := algebraMap Γ (FractionRing Γ) α
  set b := algebraMap Γ (FractionRing Γ) β
  set a' := algebraMap Γ (FractionRing Γ) α'
  set b' := algebraMap Γ (FractionRing Γ) β'
  rw [div_pow_succ_sub_div hb', div_eq_div_iff hb (pow_ne_zero _ hb')]
  linear_combination (-1 : FractionRing Γ) * heq'

end Stacks.GradedCompletion
