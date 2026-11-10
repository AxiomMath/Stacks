module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public import StacksFrontier.RingTheory.CohenRing
public import StacksFrontier.RingTheory.RegularLocalRing.SystemOfParameters

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# A formal inverse function theorem for multivariate power series

For `A = K[[x_1, …, x_n]]` over a field `K`, or over a Cohen ring `Λ`, this file shows that a
tuple `y_1, …, y_n` of power series in the maximal ideal whose Jacobian (the matrix of linear
coefficients) is invertible admits a right inverse under substitution. It deduces that the
substitution map `K[[Y_1, …, Y_n]] → A`, `Y_i ↦ y_i`, is bijective when the `y_i` form a regular
system of parameters (Engine 1), and the analogous statement over a Cohen ring (Engine 2).
-/

open IsLocalRing MvPowerSeries

namespace Stacks.MvPowerSeries.RegularParameters

/-! ## Shared infrastructure lemmas (field and Cohen-ring coefficients) -/

/-- A power series lies in the maximal ideal iff its constant coefficient does. -/
private theorem mem_maximalIdeal_iff_constantCoeff_mem {K : Type*} [CommRing K] [IsLocalRing K]
    {n : ℕ} (f : MvPowerSeries (Fin n) K) :
    f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ↔
      MvPowerSeries.constantCoeff f ∈ maximalIdeal K := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- An element of the maximal ideal of `MvPowerSeries (Fin n) K`, for `K` a field, has zero
constant coefficient: that maximal ideal is the kernel of `constantCoeff`. -/
theorem constantCoeff_eq_zero_of_mem_maximalIdeal {K : Type*} [Field K] {n : ℕ}
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    MvPowerSeries.constantCoeff f = (0 : K) := by
  rw [mem_maximalIdeal_iff_constantCoeff_mem, IsLocalRing.maximalIdeal_eq_bot] at hf
  exact hf

/-- Any family `y : Fin n → m_A` of elements of the maximal ideal of
`A = K[[x_1, …, x_n]]` is substitutable, hence defines the comparison map
`K[[Y]] →ₐ[K] A`, `X i ↦ y i`. -/
theorem hasSubst_of_mem_maximalIdeal {K : Type*} [Field K] {n : ℕ}
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K)) :
    MvPowerSeries.HasSubst (fun i => (y i : MvPowerSeries (Fin n) K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
    constantCoeff_eq_zero_of_mem_maximalIdeal (y i).2

/-- The degree-1 coefficient of a product `g * h` splits as the two boundary terms
`constantCoeff g * coeff₁ h + coeff₁ g * constantCoeff h`. -/
theorem coeff_single_one_mul {Λ : Type*} [CommRing Λ] {n : ℕ} (i : Fin n)
    (g h : MvPowerSeries (Fin n) Λ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (g * h) =
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) h +
        MvPowerSeries.coeff (Finsupp.single i 1) g * MvPowerSeries.constantCoeff h := by
  rw [MvPowerSeries.coeff_mul]
  have hmem1 :
    ((0 : Fin n →₀ ℕ), Finsupp.single i 1) ∈
      Finset.HasAntidiagonal.antidiagonal (Finsupp.single i 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; simp
  have hmem2 :
    (Finsupp.single i 1, (0 : Fin n →₀ ℕ)) ∈
      Finset.HasAntidiagonal.antidiagonal (Finsupp.single i 1) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]; simp
  have hne12 :
    ((0 : Fin n →₀ ℕ), Finsupp.single i 1) ∉
      ({(Finsupp.single i 1, (0 : Fin n →₀ ℕ))} : Finset _) := by
    rw [Finset.mem_singleton, Prod.ext_iff]
    rintro ⟨hc, _⟩
    apply_fun (fun f => f i) at hc
    simp at hc
  rw [← Finset.sum_subset (Finset.insert_subset hmem1 (Finset.singleton_subset_iff.mpr hmem2))]
  · rw [Finset.sum_insert hne12, Finset.sum_singleton,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro b hb hbni
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
    rw [Finset.mem_insert, Finset.mem_singleton] at hbni
    push Not at hbni
    exfalso
    rcases eq_or_ne b.1 0 with h1 | h1
    · apply hbni.1
      exact Prod.ext h1 (by rwa [h1, zero_add] at hb)
    · apply hbni.2
      have hsum : b.1 + b.2 = Finsupp.single i 1 := hb
      have hb1i : b.1 i = 1 := by
        obtain ⟨k, hk⟩ := Finsupp.ne_iff.mp h1
        rw [Finsupp.coe_zero, Pi.zero_apply] at hk
        have heqk : b.1 k + b.2 k = (Finsupp.single i 1) k := by rw [← Finsupp.add_apply, hsum]
        have hki : k = i := by
          by_contra hne
          rw [Finsupp.single_apply, ite_eq_right (fun hh => hne hh.symm)] at heqk
          omega
        subst hki
        rw [Finsupp.single_eq_same] at heqk
        omega
      have hb2 : b.2 = 0 := by
        ext j
        have hj : b.1 j + b.2 j = (Finsupp.single i 1) j := by rw [← Finsupp.add_apply, hsum]
        rw [Finsupp.coe_zero, Pi.zero_apply]
        by_cases hji : j = i
        · subst hji; rw [Finsupp.single_eq_same] at hj; omega
        · rw [Finsupp.single_apply, ite_eq_right (fun hh => hji hh.symm)] at hj; omega
      exact Prod.ext (by rwa [hb2, add_zero] at hsum) hb2

/-- The **linear substitution** associated to a matrix `M`: `linearSubst M i = ∑ⱼ Mᵢⱼ xⱼ`,
i.e. the substitution family sending `X i ↦ ∑ⱼ Mᵢⱼ Xⱼ`. -/
noncomputable def linearSubst {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : Fin n → MvPowerSeries (Fin n) K := fun i =>
  ∑ j, MvPowerSeries.C (M i j) * MvPowerSeries.X j

/-- The `i`-th member of the linear substitution family associated to `M` is `∑ⱼ Mᵢⱼ xⱼ`. -/
theorem linearSubst_apply {K : Type*} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (i : Fin n) : linearSubst M i = ∑ j, MvPowerSeries.C (M i j) * MvPowerSeries.X j :=
  rfl

/-- The coefficient of `x_i` in the variable `x_j` is `1` if `i = j` and `0` otherwise. -/
private theorem coeff_single_one_X {K : Type*} [CommRing K] {n : ℕ} (i j : Fin n) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : MvPowerSeries (Fin n) K) =
      if i = j then 1 else 0 := by
  simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

/-- A linear substitution has zero constant coefficients. -/
private theorem constantCoeff_linearSubst {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    MvPowerSeries.constantCoeff (linearSubst M i) = 0 := by
  rw [linearSubst_apply, map_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

/-- The degree-1 coefficients of a linear substitution read off the matrix entries:
the coefficient of `x_i` in `linearSubst M j` is `M j i`. -/
theorem coeff_single_one_linearSubst {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (j i : Fin n) :
    MvPowerSeries.coeff (Finsupp.single i 1) (linearSubst M j) = M j i := by
  simp [linearSubst_apply, coeff_single_one_X]

/-- A linear substitution has zero constant coefficients, hence `HasSubst`. -/
theorem hasSubst_linearSubst {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : MvPowerSeries.HasSubst (linearSubst M) := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_linearSubst M)

/-- **Linear inversion.** Composition of linear substitutions corresponds to matrix
multiplication: if `N * M = 1` then `subst (linearSubst M) (linearSubst N i) = X i`, i.e. the
inverse-linear substitution `linearSubst N` undoes `linearSubst M`. -/
theorem subst_linearSubst_linearSubst {K : Type*} [CommRing K] {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) K) (h : N * M = 1) (i : Fin n) :
    MvPowerSeries.subst (linearSubst M) (linearSubst N i) = MvPowerSeries.X i := by
  rw [← MvPowerSeries.substAlgHom_apply (hasSubst_linearSubst M), linearSubst_apply, map_sum]
  have step :
    ∀ j : Fin n,
      (MvPowerSeries.substAlgHom (hasSubst_linearSubst M))
          (MvPowerSeries.C (N i j) * MvPowerSeries.X j) =
        MvPowerSeries.C (N i j) * linearSubst M j := by
    intro j
    rw [map_mul, MvPowerSeries.substAlgHom_X]
    congr 1
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
  simp_rw [step, linearSubst_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hkey :
    ∀ k : Fin n,
      (∑ j, MvPowerSeries.C (N i j) * (MvPowerSeries.C (M j k) * MvPowerSeries.X k)) =
        MvPowerSeries.C ((N * M) i k) * MvPowerSeries.X k := by
    intro k
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, mul_assoc]
  simp_rw [hkey, h]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro k _ hk
    rw [Matrix.one_apply_ne (Ne.symm hk), map_zero, zero_mul]
  · exact fun hi => absurd (Finset.mem_univ i) hi

/-- The **Jacobian matrix** of a family `y` of elements of the maximal ideal of
`K[[x_1, …, x_n]]`: its `(i, j)` entry is the coefficient of `x_j` in `y i`, so it is the
matrix of linear parts of `y`. -/
noncomputable def jacobian {K : Type*} [CommRing K] [IsLocalRing K] {n : ℕ}
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K)) : Matrix (Fin n) (Fin n) K :=
  Matrix.of (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (y i : MvPowerSeries (Fin n) K))

/-- The `(i, j)` entry of the Jacobian of `y` is the coefficient of `x_j` in `y i`. -/
@[simp]
theorem jacobian_apply {K : Type*} [CommRing K] [IsLocalRing K] {n : ℕ}
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K)) (i j : Fin n) :
    jacobian y i j = MvPowerSeries.coeff (Finsupp.single j 1) (y i : MvPowerSeries (Fin n) K) :=
  rfl

/-- A power series and the constant polynomial of its constant coefficient have the same residue
in the local ring of power series. -/
private theorem residue_eq_residue_C_constantCoeff {K : Type*} [CommRing K] [IsLocalRing K]
    {n : ℕ} (a : MvPowerSeries (Fin n) K) :
    residue (MvPowerSeries (Fin n) K) a =
      residue (MvPowerSeries (Fin n) K) (MvPowerSeries.C (a := MvPowerSeries.constantCoeff a)) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    mem_maximalIdeal_iff_constantCoeff_mem]
  simp

/-- If a linear map `f : V →ₗ[κ] κ^k` sends a family `v` to the standard basis and `w` spans `V`,
then the matrix with rows `f (w j)` has unit determinant. -/
private theorem isUnit_det_of_span_eq_top {κ V : Type*} [Field κ] [AddCommGroup V] [Module κ V]
    {k : ℕ} (f : V →ₗ[κ] (Fin k → κ)) (v w : Fin k → V) (hv : ∀ j, f (v j) = Pi.single j 1)
    (hw : Submodule.span κ (Set.range w) = ⊤) : IsUnit (Matrix.of fun j => f (w j)).det := by
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun κ (Fin k)).span_eq,
      Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨v j, by rw [hv j, Pi.basisFun_apply]⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_row_iff_isUnit]
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp)
  change ⊤ ≤ Submodule.span κ (Set.range fun j => f (w j))
  rw [show (Set.range fun j => f (w j)) = f '' Set.range w by rw [← Set.range_comp]; rfl,
    ← Submodule.map_span, hw, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

/-- **Jacobian invertibility from RSOP.** If `y` is a regular system of parameters of
`A = K[[x_1,…,x_n]]`, then its Jacobian matrix `M i j = coeff (single j 1) (y i)` is
invertible over `K`. -/
theorem isUnit_det_jacobian_of_rsop {K : Type*} [Field K] {n : ℕ}
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K)) (hy : IsRegularSystemOfParameters y) :
    IsUnit (jacobian y).det := by
  classical
  obtain ⟨-, hspan⟩ := hy
  -- abbreviations as `let`-bindings (NOT `set`, to avoid renaming the binder `y`).
  let A := MvPowerSeries (Fin n) K
  let κ := ResidueField A
  let m := maximalIdeal A
  -- The coefficient-extraction-into-κ ring hom φ : K →+* κ, φ = residue ∘ C.
  set φ : K →+* κ := (IsLocalRing.residue A).comp (MvPowerSeries.C (σ := Fin n) (R := K)) with hφ
  -- helper_07nm facts (re-derived inline, using only earlier-declared lemmas).
  have aux_cc0 : ∀ (f : A), f ∈ m → MvPowerSeries.constantCoeff f = 0 := fun f hf =>
    constantCoeff_eq_zero_of_mem_maximalIdeal hf
  have aux_coeff_smul :
    ∀ (i : Fin n) (a f : A),
      MvPowerSeries.constantCoeff f = 0 →
        MvPowerSeries.coeff (Finsupp.single i 1) (a * f) =
          MvPowerSeries.constantCoeff a * MvPowerSeries.coeff (Finsupp.single i 1) f := by
    intro i a f hf
    rw [coeff_single_one_mul, hf, mul_zero, add_zero]
  -- The linear-part functional Λ₀ : m → (Fin n → κ).
  let Λ₀ : m →ₗ[A] (Fin n → κ) :=
    { toFun := fun f => fun i =>
        residue A (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single i 1) (f : A)))
      map_add' := by
        intro f g; funext i
        simp only [Submodule.coe_add, map_add, Pi.add_apply]
      map_smul' := by
        intro a f; funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        have hf : MvPowerSeries.constantCoeff (f : A) = 0 := aux_cc0 _ f.2
        rw [show ((a • f : m) : A) = a * f from rfl, aux_coeff_smul i a f hf, map_mul, map_mul,
          Algebra.smul_def, ← residue_eq_residue_C_constantCoeff a]
        rfl }
  have Λ₀_apply :
    ∀ (f : m) (i : Fin n),
      Λ₀ f i =
        residue A (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single i 1) (f : A))) :=
    fun f i => rfl
  have Λ₀_kill : m • (⊤ : Submodule A m) ≤ LinearMap.ker Λ₀ := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [LinearMap.mem_ker]
    funext i
    rw [Λ₀_apply, show ((r • x : m) : A) = r * x from rfl,
      coeff_single_one_mul, aux_cc0 _ hr, aux_cc0 _ x.2]
    simp
  let ΛA : CotangentSpace A →ₗ[A] (Fin n → κ) := Submodule.liftQ _ Λ₀ Λ₀_kill
  let Λκ : CotangentSpace A →ₗ[κ] (Fin n → κ) :=
    LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective ΛA
  have Λκ_toCotangent : ∀ (x : m), Λκ (m.toCotangent x) = Λ₀ x := fun _ => rfl
  have hXmem : ∀ j : Fin n, (MvPowerSeries.X j : A) ∈ m := fun j =>
    (mem_maximalIdeal_iff_constantCoeff_mem _).mpr (by simp)
  set v : Fin n → CotangentSpace A := fun j => m.toCotangent ⟨MvPowerSeries.X j, hXmem j⟩ with hv
  have hΛv : ∀ j, Λκ (v j) = (Pi.single j 1 : Fin n → κ) := by
    intro j
    rw [hv, Λκ_toCotangent]
    funext i
    rw [Λ₀_apply]
    change
      residue A
          (MvPowerSeries.C (a :=
            MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : A))) =
        _
    rw [coeff_single_one_X, Pi.single_apply]
    split_ifs <;> simp
  -- The RSOP family in the cotangent space, which spans it (RSOP hypothesis `hspan`).
  set w : Fin n → CotangentSpace A := fun i => m.toCotangent (y i) with hw
  -- Row i of (jacobian y).map φ equals Λκ (w i).
  have hrow : ∀ i, Λκ (w i) = (fun j => φ (jacobian y i j)) := by
    intro i
    rw [hw, Λκ_toCotangent]
    funext j
    rw [Λ₀_apply]
    rfl
  set M' : Matrix (Fin n) (Fin n) κ := (jacobian y).map φ with hM'
  have hM'unit : IsUnit M'.det := by
    have hMrows : (Matrix.of fun i => Λκ (w i)) = M' := by
      ext i j; rw [Matrix.of_apply, hrow i]; rfl
    rw [← hMrows]
    exact isUnit_det_of_span_eq_top Λκ v w hΛv hspan
  -- φ-mapped det is φ of det; φ injective ⇒ IsUnit (jacobian y).det.
  have hdetmap : M'.det = φ (jacobian y).det := by
    rw [hM', RingHom.map_det]; rfl
  rw [hdetmap] at hM'unit
  -- IsUnit (φ x) with φ injective ring hom from a field ⇒ IsUnit x.
  exact isUnit_iff_ne_zero.mpr fun hz => not_isUnit_zero (by rwa [hz, map_zero] at hM'unit)

/-- If `subst a (b i) = X i` for all `i`, then `subst a` is a left inverse of `subst b`. -/
private theorem subst_subst_of_subst_eq_X {R : Type*} [CommRing R] {n : ℕ}
    {a b : Fin n → MvPowerSeries (Fin n) R} (ha : MvPowerSeries.HasSubst a)
    (hb : MvPowerSeries.HasSubst b) (hkey : ∀ i, MvPowerSeries.subst a (b i) = MvPowerSeries.X i)
    (g : MvPowerSeries (Fin n) R) : MvPowerSeries.subst a (MvPowerSeries.subst b g) = g := by
  rw [MvPowerSeries.subst_comp_subst_apply hb ha, funext hkey]
  exact congrFun MvPowerSeries.subst_self g

/-- If every `a j` has zero constant coefficient, the order of `∏ s, (a s) ^ (d s)` is at least
`degree d`. -/
private theorem degree_le_order_prod_of_constantCoeff_eq_zero {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → MvPowerSeries (Fin n) K) (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (d : Fin n →₀ ℕ) : ((Finsupp.degree d : ℕ) : ℕ∞) ≤ (d.prod fun s e => a s ^ e).order := by
  rw [Finsupp.prod, Finsupp.degree_apply, Nat.cast_sum]
  refine (Finset.sum_le_sum fun j _ => ?_).trans (MvPowerSeries.le_order_prod _ _)
  exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (ha j)

/-- **Construction core (combinatorial heart of the formal IFT).** Given that the Jacobian
matrix `M` of `y` is invertible, there is a family `b` with zero constant coefficient and
`subst y (b i) = X i`.

DECOMPOSES into precise sub-lemmas: Jacobian
invertibility from the RSOP cotangent-basis hypothesis; linear-substitution = matrix action
and inversion (`subst_comp_subst`+`subst_self`, `MN=NM=1`); lowest-degree behavior of
`subst y` on homogeneous parts (`coeff_subst` + `∏ yⱼ^{eⱼ} ∈ m_A^{|e|}`); filtration
locality of `subst y`; the successive-approximation recursion + coefficientwise limit. -/
theorem exists_right_inverse_of_jacobian_isUnit {K : Type*} [CommRing K] [IsDomain K]
    [IsLocalRing K] {n : ℕ} (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K))
    (hy0 : ∀ j, MvPowerSeries.constantCoeff (y j : MvPowerSeries (Fin n) K) = (0 : K))
    (hM : IsUnit (jacobian y).det) :
    ∃ b : Fin n → MvPowerSeries (Fin n) K,
      (∀ i, MvPowerSeries.constantCoeff (b i) = (0 : K)) ∧
        (∀ i,
          MvPowerSeries.subst (fun j => (y j : MvPowerSeries (Fin n) K)) (b i) =
            MvPowerSeries.X i) := by
  classical
  -- ===================================================================
  -- Notation and basic data.
  -- ===================================================================
  set yf : Fin n → MvPowerSeries (Fin n) K := fun j => (y j : MvPowerSeries (Fin n) K)
  have hy0 : ∀ j, MvPowerSeries.constantCoeff (yf j) = 0 := hy0
  have hsuby : MvPowerSeries.HasSubst yf := MvPowerSeries.hasSubst_of_constantCoeff_zero hy0
  -- The Jacobian matrix and its inverse.
  set M : Matrix (Fin n) (Fin n) K := jacobian y
  have hMentry : ∀ j i, M j i = MvPowerSeries.coeff (Finsupp.single i 1) (yf j) := fun j i => rfl
  obtain ⟨Nmat, hNM, hMN⟩ : ∃ Nmat : Matrix (Fin n) (Fin n) K, Nmat * M = 1 ∧ M * Nmat = 1 :=
    ⟨M⁻¹, Matrix.nonsing_inv_mul M hM, Matrix.mul_nonsing_inv M hM⟩
  set ℓ : Fin n → MvPowerSeries (Fin n) K := linearSubst M with hℓdef
  set ℓ' : Fin n → MvPowerSeries (Fin n) K := linearSubst Nmat with hℓ'def
  have hsubl : MvPowerSeries.HasSubst ℓ := hasSubst_linearSubst M
  have hsubl' : MvPowerSeries.HasSubst ℓ' := hasSubst_linearSubst Nmat
  -- ===================================================================
  -- Local order infrastructure.
  -- ===================================================================
  have order_prod_sub :
    ∀ {ι : Type} (f g : ι → MvPowerSeries (Fin n) K) (w : ι → ℕ∞) (s : Finset ι),
      (∀ j ∈ s, w j ≤ (f j).order) →
        (∀ j ∈ s, w j ≤ (g j).order) →
        (∀ j ∈ s, w j + 1 ≤ (f j - g j).order) →
        (∑ j ∈ s, w j) + 1 ≤ (∏ j ∈ s, f j - ∏ j ∈ s, g j).order := by
    intro ι f g w s hf hg hfg
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha
      ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hsplit :
        f a * (∏ j ∈ s, f j) - g a * (∏ j ∈ s, g j) =
          f a * ((∏ j ∈ s, f j) - (∏ j ∈ s, g j)) + (f a - g a) * (∏ j ∈ s, g j) := by
        ring
      rw [hsplit]
      refine le_trans ?_ (MvPowerSeries.min_order_le_add)
      rw [le_min_iff]
      refine ⟨?_, ?_⟩
      · rw [MvPowerSeries.order_mul]
        calc
          w a + (∑ j ∈ s, w j) + 1 = w a + ((∑ j ∈ s, w j) + 1) := by ring
          _ ≤ (f a).order + ((∏ j ∈ s, f j) - (∏ j ∈ s, g j)).order :=
            add_le_add (hf a (Finset.mem_insert_self a s))
              (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
                (fun j hj => hg j (Finset.mem_insert_of_mem hj))
                (fun j hj => hfg j (Finset.mem_insert_of_mem hj)))
      · rw [MvPowerSeries.order_mul]
        calc
          w a + (∑ j ∈ s, w j) + 1 = (w a + 1) + (∑ j ∈ s, w j) := by ring
          _ ≤ (f a - g a).order + (∏ j ∈ s, g j).order :=
            add_le_add (hfg a (Finset.mem_insert_self a s))
              ((Finset.sum_le_sum fun j hj => hg j (Finset.mem_insert_of_mem hj)).trans
                (MvPowerSeries.le_order_prod _ _))
  have order_pow_sub :
    ∀ (a c : MvPowerSeries (Fin n) K) (k : ℕ),
      1 ≤ a.order → 1 ≤ c.order → 2 ≤ (a - c).order → ((k : ℕ∞) + 1) ≤ (a ^ k - c ^ k).order := by
    intro a c k ha hc hac
    simpa using
      order_prod_sub (fun _ => a) (fun _ => c) (fun _ => 1) (Finset.range k) (fun _ _ => ha)
        (fun _ _ => hc) (fun _ _ => by simpa [one_add_one_eq_two] using hac)
  -- order facts about yf and ℓ.
  have hy1 : ∀ j, 1 ≤ (yf j).order := fun j =>
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hy0 j)
  have hl0 : ∀ j, MvPowerSeries.constantCoeff (ℓ j) = 0 := constantCoeff_linearSubst M
  have hl1 : ∀ j, 1 ≤ (ℓ j).order := fun j =>
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hl0 j)
  have hyl : ∀ j, 2 ≤ (yf j - ℓ j).order := by
    intro j
    apply MvPowerSeries.nat_le_order
    intro d hd
    rw [map_sub]
    interval_cases h : (Finsupp.degree d)
    · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h
      subst hd0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0 j, hl0 j, sub_zero]
    · obtain ⟨i, rfl⟩ : ∃ i, d = Finsupp.single i 1 := by
        apply (Finsupp.sum_eq_one_iff d).mp; rw [Finsupp.sum, ← Finsupp.degree_apply]; exact h
      rw [hℓdef, coeff_single_one_linearSubst, hMentry j i, sub_self]
  -- ===================================================================
  -- The product-order estimate and the locality of subst yf.
  -- ===================================================================
  have order_prod_y_sub_ell :
    ∀ (e : Fin n →₀ ℕ),
      ((Finsupp.degree e : ℕ) : ℕ∞) + 1 ≤
        ((e.prod fun s k => yf s ^ k) - (e.prod fun s k => ℓ s ^ k)).order := by
    intro e
    rw [Finsupp.prod, Finsupp.prod, Finsupp.degree_apply, Nat.cast_sum]
    exact
      order_prod_sub (fun j => yf j ^ e j) (fun j => ℓ j ^ e j) (fun j => (e j : ℕ∞)) e.support
        (fun j _ => MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (hy0 j))
        (fun j _ => MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (hl0 j))
        (fun j _ => order_pow_sub (yf j) (ℓ j) (e j) (hy1 j) (hl1 j) (hyl j))
  have le_order_prod := degree_le_order_prod_of_constantCoeff_eq_zero yf hy0
  have hloc :
    ∀ (h : MvPowerSeries (Fin n) K) (d : Fin n →₀ ℕ),
      ((Finsupp.degree d : ℕ) : ℕ∞) < h.order →
        MvPowerSeries.coeff d (MvPowerSeries.subst yf h) = 0 := by
    intro h d hord
    rw [MvPowerSeries.coeff_subst hsuby]
    apply finsum_eq_zero_of_forall_eq_zero
    intro e
    by_cases he : MvPowerSeries.coeff e h = 0
    · rw [he, zero_smul]
    · have hle : h.order ≤ ((Finsupp.degree e : ℕ) : ℕ∞) := MvPowerSeries.order_le he
      have hdlt : ((Finsupp.degree d : ℕ) : ℕ∞) < (e.prod fun s k => yf s ^ k).order :=
        lt_of_lt_of_le (lt_of_lt_of_le hord hle) (le_order_prod e)
      rw [MvPowerSeries.coeff_of_lt_order hdlt, smul_zero]
  -- ===================================================================
  -- Homogeneity bookkeeping.
  -- ===================================================================
  -- `IsHomog p f`: f has no coefficients in degrees other than p.
  let IsHomog : ℕ → MvPowerSeries (Fin n) K → Prop := fun p f =>
    ∀ d, Finsupp.degree d ≠ p → MvPowerSeries.coeff d f = 0
  have isHomog_one : IsHomog 0 (1 : MvPowerSeries (Fin n) K) := by
    intro d hd; rw [MvPowerSeries.coeff_one, ite_eq_right]
    intro hc; apply hd; subst hc; simp [Finsupp.degree_apply]
  have isHomog_mul :
    ∀ {p q : ℕ} {f g : MvPowerSeries (Fin n) K},
      IsHomog p f → IsHomog q g → IsHomog (p + q) (f * g) := by
    intro p q f g hf hg d hd
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
    by_cases h1 : Finsupp.degree b.1 = p
    · by_cases h2 : Finsupp.degree b.2 = q
      · exfalso; apply hd; rw [← hb, map_add, h1, h2]
      · rw [hg b.2 h2, mul_zero]
    · rw [hf b.1 h1, zero_mul]
  have isHomog_prod :
    ∀ (w : Fin n → ℕ) (g : Fin n → MvPowerSeries (Fin n) K) (s : Finset (Fin n)),
      (∀ i ∈ s, IsHomog (w i) (g i)) → IsHomog (∑ i ∈ s, w i) (∏ i ∈ s, g i) := by
    intro w g s hg
    induction s using Finset.induction with
    | empty => simpa using isHomog_one
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact
        isHomog_mul (hg a (Finset.mem_insert_self a s))
          (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))
  have isHomog_C_mul_X :
    ∀ (a : K) (j : Fin n),
      IsHomog 1 (MvPowerSeries.C a * MvPowerSeries.X j : MvPowerSeries (Fin n) K) := by
    intro a j d hd
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ite_eq_right, mul_zero]
    intro hc; apply hd; subst hc; simp [Finsupp.degree_apply]
  have isHomog_sum :
    ∀ (p : ℕ) (s : Finset (Fin n)) (g : Fin n → MvPowerSeries (Fin n) K),
      (∀ i ∈ s, IsHomog p (g i)) → IsHomog p (∑ i ∈ s, g i) := by
    intro p s g hg d hd; rw [map_sum]; exact Finset.sum_eq_zero (fun i hi => hg i hi d hd)
  have isHomog_pow :
    ∀ {p : ℕ} {f : MvPowerSeries (Fin n) K}, IsHomog p f → ∀ (k : ℕ), IsHomog (k * p) (f ^ k) := by
    intro p f hf k
    induction k with
    | zero => simpa using isHomog_one
    | succ m ih =>
      rw [pow_succ]
      have := isHomog_mul ih hf
      rwa [show m * p + p = (m + 1) * p by ring] at this
  have isHomog_linearSubst :
      ∀ (P : Matrix (Fin n) (Fin n) K) (j : Fin n), IsHomog 1 (linearSubst P j) := by
    intro P j; rw [linearSubst_apply]
    exact isHomog_sum 1 _ _ (fun k _ => isHomog_C_mul_X (P j k) k)
  have isHomog_prod_linearSubst :
    ∀ (P : Matrix (Fin n) (Fin n) K) (c : Fin n →₀ ℕ),
      IsHomog (Finsupp.degree c) (c.prod fun s k => (linearSubst P s) ^ k) := by
    intro P c
    rw [Finsupp.prod, Finsupp.degree_apply]
    exact
      isHomog_prod (fun j => c j) (fun j => (linearSubst P j) ^ (c j)) c.support
        (fun j _ => by
          have := isHomog_pow (isHomog_linearSubst P j) (c j); rwa [mul_one] at this)
  -- `subst ℓ'` preserves homogeneity.
  have hcorrhomog :
    ∀ (p : ℕ) (g : MvPowerSeries (Fin n) K),
      IsHomog p g → IsHomog p (MvPowerSeries.subst ℓ' g) := by
    intro p g hg e he
    rw [MvPowerSeries.coeff_subst hsubl']
    apply finsum_eq_zero_of_forall_eq_zero
    intro c
    by_cases hc : MvPowerSeries.coeff c g = 0
    · rw [hc, zero_smul]
    · have hcp : Finsupp.degree c = p := by
        by_contra h; exact hc (hg c h)
      have hph := isHomog_prod_linearSubst Nmat c
      rw [hℓ'def,
        hph e
          (by
            rw [hcp]; exact he),
        smul_zero]
  -- ===================================================================
  -- Sublemma 3 : lowest-degree behaviour of subst yf is the linear subst ℓ.
  -- ===================================================================
  have hlin :
    ∀ (g : MvPowerSeries (Fin n) K) (q : ℕ),
      IsHomog q g →
        ∀ d,
          Finsupp.degree d = q →
            MvPowerSeries.coeff d (MvPowerSeries.subst yf g) =
              MvPowerSeries.coeff d (MvPowerSeries.subst ℓ g) := by
    intro g q hg d hd
    rw [MvPowerSeries.coeff_subst hsuby, MvPowerSeries.coeff_subst hsubl]
    apply finsum_congr
    intro e
    by_cases he : MvPowerSeries.coeff e g = 0
    · rw [he, zero_smul, zero_smul]
    · have hep : Finsupp.degree e = q := by
        by_contra hcc; exact he (hg e hcc)
      congr 1
      have hdiff :
        MvPowerSeries.coeff d ((e.prod fun s k => yf s ^ k) - (e.prod fun s k => ℓ s ^ k)) =
          0 := by
        apply MvPowerSeries.coeff_of_lt_order
        have hb := order_prod_y_sub_ell e
        have hlt2 : ((Finsupp.degree d : ℕ) : ℕ∞) < ((Finsupp.degree e : ℕ) : ℕ∞) + 1 := by
          rw [hep, hd]; exact_mod_cast lt_add_one _
        exact lt_of_lt_of_le hlt2 hb
      rw [map_sub] at hdiff
      exact sub_eq_zero.mp hdiff
  -- ===================================================================
  -- Linear inversion : subst ℓ ∘ subst ℓ' = id.
  -- ===================================================================
  have hinv : ∀ g, MvPowerSeries.subst ℓ (MvPowerSeries.subst ℓ' g) = g :=
    subst_subst_of_subst_eq_X hsubl hsubl' (subst_linearSubst_linearSubst M Nmat hNM)
  -- ===================================================================
  -- homogComp : the degree-`p` homogeneous part.
  -- ===================================================================
  let homogComp : ℕ → MvPowerSeries (Fin n) K → MvPowerSeries (Fin n) K := fun p f => fun d =>
    if Finsupp.degree d = p then f d else 0
  have coeff_homogComp :
    ∀ (p : ℕ) (f : MvPowerSeries (Fin n) K) (d : Fin n →₀ ℕ),
      MvPowerSeries.coeff d (homogComp p f) =
        if Finsupp.degree d = p then MvPowerSeries.coeff d f else 0 :=
    fun _ _ _ => rfl
  have homogComp_isHomog : ∀ (p : ℕ) (f : MvPowerSeries (Fin n) K), IsHomog p (homogComp p f) := by
    intro p f d hd; rw [coeff_homogComp, ite_eq_right hd]
  -- ===================================================================
  -- The successive-approximation sequence.
  -- ===================================================================
  let B : ℕ → Fin n → MvPowerSeries (Fin n) K := fun p i =>
    Nat.rec (0 : MvPowerSeries (Fin n) K)
      (fun p Bp =>
        Bp + MvPowerSeries.subst ℓ' (homogComp p (MvPowerSeries.X i - MvPowerSeries.subst yf Bp)))
      p
  have hBsucc :
    ∀ p i,
      B (p + 1) i =
        B p i +
          MvPowerSeries.subst ℓ'
            (homogComp p (MvPowerSeries.X i - MvPowerSeries.subst yf (B p i))) :=
    fun p i => rfl
  -- The step lemma giving (S_{p+1}) from (S_p).
  have hstep :
    ∀ (p : ℕ) (i : Fin n) (Bp : MvPowerSeries (Fin n) K),
      (∀ d,
          Finsupp.degree d < p →
            MvPowerSeries.coeff d (MvPowerSeries.subst yf Bp) =
              MvPowerSeries.coeff d (MvPowerSeries.X i)) →
        ∀ d,
          Finsupp.degree d < p + 1 →
            MvPowerSeries.coeff d
                (MvPowerSeries.subst yf
                  (Bp +
                    MvPowerSeries.subst ℓ'
                      (homogComp p (MvPowerSeries.X i - MvPowerSeries.subst yf Bp)))) =
              MvPowerSeries.coeff d (MvPowerSeries.X i) := by
    intro p i Bp hSp d hd
    set δ := MvPowerSeries.X i - MvPowerSeries.subst yf Bp with hδ
    set hp := homogComp p δ with hhp
    set corr := MvPowerSeries.subst ℓ' hp
    rw [MvPowerSeries.subst_add hsuby, map_add]
    have hcorrh : IsHomog p corr := hcorrhomog p hp (homogComp_isHomog p δ)
    rcases Nat.lt_or_ge (Finsupp.degree d) p with hlt | hge
    · have h1 :
        MvPowerSeries.coeff d (MvPowerSeries.subst yf Bp) =
          MvPowerSeries.coeff d (MvPowerSeries.X i) :=
        hSp d hlt
      have hordcorr : ((Finsupp.degree d : ℕ) : ℕ∞) < corr.order :=
        (by exact_mod_cast hlt : ((Finsupp.degree d : ℕ) : ℕ∞) < p).trans_le
          (MvPowerSeries.nat_le_order fun e he => hcorrh e he.ne)
      rw [h1, hloc corr d hordcorr, add_zero]
    · have hdp : Finsupp.degree d = p := by omega
      have h3 :
        MvPowerSeries.coeff d (MvPowerSeries.subst yf corr) =
          MvPowerSeries.coeff d (MvPowerSeries.subst ℓ corr) :=
        hlin corr p hcorrh d hdp
      have h4 : MvPowerSeries.subst ℓ corr = hp := hinv hp
      rw [h3, h4]
      have h5 : MvPowerSeries.coeff d hp = MvPowerSeries.coeff d δ := by
        rw [hhp, coeff_homogComp, ite_eq_left hdp]
      rw [h5, hδ, map_sub]
      ring
  -- (S_p) holds for all p.
  have hS :
    ∀ p i,
      ∀ d,
        Finsupp.degree d < p →
          MvPowerSeries.coeff d (MvPowerSeries.subst yf (B p i)) =
            MvPowerSeries.coeff d (MvPowerSeries.X i) := by
    intro p i
    induction p with
    | zero =>
      intro d hd; omega
    | succ m ih =>
      rw [hBsucc m i]; exact hstep m i (B m i) ih
  -- Single-step stability : coefficients below degree p are unchanged.
  have hstab1 :
    ∀ p i,
      ∀ d,
        Finsupp.degree d < p →
          MvPowerSeries.coeff d (B (p + 1) i) = MvPowerSeries.coeff d (B p i) := by
    intro p i d hd
    rw [hBsucc p i, map_add]
    have hz :
      MvPowerSeries.coeff d
          (MvPowerSeries.subst ℓ'
            (homogComp p (MvPowerSeries.X i - MvPowerSeries.subst yf (B p i)))) =
        0 := by
      have hh :=
        hcorrhomog p (homogComp p (MvPowerSeries.X i - MvPowerSeries.subst yf (B p i)))
          (homogComp_isHomog p _)
      exact hh d (Nat.ne_of_lt hd)
    rw [hz, add_zero]
  -- Monotone stability.
  have hstab :
    ∀ p q i,
      p ≤ q →
        ∀ d,
          Finsupp.degree d < p →
            MvPowerSeries.coeff d (B q i) = MvPowerSeries.coeff d (B p i) := by
    intro p q i hpq
    induction q with
    | zero =>
      intro d hd; omega
    | succ m ih =>
      intro d hd
      rcases Nat.lt_or_ge p (m + 1) with h | h
      · have hpm : p ≤ m := by omega
        rw [hstab1 m i d (by omega), ih hpm d hd]
      · have hpe : p = m + 1 := by omega
        subst hpe; rfl
  -- ===================================================================
  -- The limit series b and the verification.
  -- ===================================================================
  refine ⟨fun i => (fun d => B (Finsupp.degree d + 1) i d : MvPowerSeries (Fin n) K), ?_, ?_⟩
  · -- constant coefficient is zero
    intro i
    change
      MvPowerSeries.constantCoeff
          (fun d => B (Finsupp.degree d + 1) i d : MvPowerSeries (Fin n) K) =
        0
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hcoeff0 :
      MvPowerSeries.coeff (0 : Fin n →₀ ℕ)
          (fun d => B (Finsupp.degree d + 1) i d : MvPowerSeries (Fin n) K) =
        B 1 i 0 := by
      rw [MvPowerSeries.coeff_apply]; simp [Finsupp.degree_apply]
    rw [hcoeff0]
    -- B 1 i = 0
    have hB1 : B 1 i = 0 := by
      change
        (0 : MvPowerSeries (Fin n) K) +
            MvPowerSeries.subst ℓ' (homogComp 0 (MvPowerSeries.X i - MvPowerSeries.subst yf 0)) =
          0
      have hsub0 : ∀ {a : Fin n → MvPowerSeries (Fin n) K}, MvPowerSeries.HasSubst a →
          MvPowerSeries.subst a (0 : MvPowerSeries (Fin n) K) = 0 := fun ha => by
        rw [← MvPowerSeries.substAlgHom_apply ha, map_zero]
      rw [hsub0 hsuby, sub_zero]
      have hhc0 : homogComp 0 (MvPowerSeries.X i : MvPowerSeries (Fin n) K) = 0 := by
        ext d
        rw [coeff_homogComp]
        by_cases hd : Finsupp.degree d = 0
        · rw [ite_eq_left hd]
          have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd
          subst this
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
          simp
        · rw [ite_eq_right hd]; simp
      rw [hhc0]
      rw [hsub0 hsubl', zero_add]
    rw [hB1]; rfl
  · -- subst yf (b i) = X i
    intro i
    apply MvPowerSeries.ext
    intro d
    set bi : MvPowerSeries (Fin n) K := (fun d => B (Finsupp.degree d + 1) i d) with hbidef
    set q := Finsupp.degree d with hq
    -- b i agrees with B (q+1) i on all degrees ≤ q.
    have hagree :
      ∀ e,
        Finsupp.degree e ≤ q → MvPowerSeries.coeff e bi = MvPowerSeries.coeff e (B (q + 1) i) := by
      intro e he
      rw [MvPowerSeries.coeff_apply, hbidef]
      change B (Finsupp.degree e + 1) i e = MvPowerSeries.coeff e (B (q + 1) i)
      rw [MvPowerSeries.coeff_apply]
      have hst := hstab (Finsupp.degree e + 1) (q + 1) i (by omega) e (by omega)
      rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply] at hst
      exact hst.symm
    -- the difference has order > q, so subst yf does not see it at d.
    have hdiff_zero : MvPowerSeries.coeff d (MvPowerSeries.subst yf (bi - B (q + 1) i)) = 0 := by
      apply hloc
      apply lt_of_lt_of_le (b := ((q + 1 : ℕ) : ℕ∞))
      · rw [← hq]; exact_mod_cast lt_add_one _
      · apply MvPowerSeries.nat_le_order
        intro e he
        rw [map_sub, hagree e (by omega), sub_self]
    rw [MvPowerSeries.subst_sub hsuby, map_sub] at hdiff_zero
    have hsub_eq :
      MvPowerSeries.coeff d (MvPowerSeries.subst yf bi) =
        MvPowerSeries.coeff d (MvPowerSeries.subst yf (B (q + 1) i)) := by
      rw [← sub_eq_zero]; exact hdiff_zero
    rw [hsub_eq]
    -- (S_{q+1}) closes the goal.
    exact
      hS (q + 1) i d
        (by
          rw [← hq]; exact lt_add_one q)

/-- If `y` is a regular system of parameters of `K[[X_1, …, X_n]]` over a field `K`, then there are
power series `b_1, …, b_n` with zero constant coefficient such that substituting `y` into each
`b_i` gives `X_i`. -/
theorem exists_right_inverse_subst_field {K : Type*} [Field K] {n : ℕ}
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K)) (hy : IsRegularSystemOfParameters y) :
    ∃ b : Fin n → MvPowerSeries (Fin n) K,
      (∀ i, MvPowerSeries.constantCoeff (b i) = (0 : K)) ∧
        (∀ i,
          MvPowerSeries.subst (fun j => (y j : MvPowerSeries (Fin n) K)) (b i) =
            MvPowerSeries.X i) :=
  exists_right_inverse_of_jacobian_isUnit y
    (fun j => constantCoeff_eq_zero_of_mem_maximalIdeal (y j).2)
    (isUnit_det_jacobian_of_rsop y hy)

/-- If substitution along `b` is a right inverse of substitution along `a` on the variables
(`subst a (b i) = x_i`), then substitution along `a` is surjective. -/
theorem surjective_subst_of_right_inverse {R : Type*} [CommRing R] {n : ℕ}
    {a b : Fin n → MvPowerSeries (Fin n) R} (ha : MvPowerSeries.HasSubst a)
    (hb : MvPowerSeries.HasSubst b)
    (hkey : ∀ i, MvPowerSeries.subst a (b i) = MvPowerSeries.X i) :
    Function.Surjective
      (MvPowerSeries.subst a : MvPowerSeries (Fin n) R → MvPowerSeries (Fin n) R) := by
  exact fun g => ⟨MvPowerSeries.subst b g, subst_subst_of_subst_eq_X ha hb hkey g⟩

/-! ## Engine 1 (statement 1): the comparison map is an isomorphism over a field. -/

/-- (1a) **Surjectivity.** If `y` is a regular system of parameters of `A`, the
comparison map `φ = substAlgHom : K[[Y]] →ₐ[K] A`, `X i ↦ y i`, is surjective. -/
theorem engine_one_surjective {K : Type*} [Field K] {n : ℕ}
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K)) (hy : IsRegularSystemOfParameters y) :
    Function.Surjective
      ((MvPowerSeries.substAlgHom (hasSubst_of_mem_maximalIdeal y) :
        MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)) := by
  obtain ⟨b, hb0, hkey⟩ := exists_right_inverse_subst_field y hy
  rw [MvPowerSeries.coe_substAlgHom]
  exact surjective_subst_of_right_inverse (hasSubst_of_mem_maximalIdeal y)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hb0) hkey

/-- The order of `∏ s, (a s) ^ (d s)` is at least `degree d`, provided every `a s` has order
`≥ 1` (e.g. zero constant coefficient). -/
theorem degree_le_order_prod {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → MvPowerSeries (Fin n) K) (ha : ∀ j, 1 ≤ (a j).order) (d : Fin n →₀ ℕ) :
    ((Finsupp.degree d : ℕ) : ℕ∞) ≤ (d.prod fun s e => a s ^ e).order := by
  exact degree_le_order_prod_of_constantCoeff_eq_zero a
    (fun j => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp (ha j)) d

/-- The degree-1 (linear) coefficient of a substitution `subst a g`, when both `g` and all
`a j` have zero constant coefficient, is given by the linear-part matrix product:
`coeff (single k 1) (subst a g) = ∑ⱼ coeff (single j 1) g · coeff (single k 1) (a j)`.
This is the algebraic statement that the Jacobian of a composite of substitutions is the
product of the Jacobians. -/
theorem coeff_single_one_subst {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → MvPowerSeries (Fin n) K) (ha0 : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (g : MvPowerSeries (Fin n) K) (hg0 : MvPowerSeries.constantCoeff g = 0) (k : Fin n) :
    MvPowerSeries.coeff (Finsupp.single k 1) (MvPowerSeries.subst a g) =
      ∑ j,
        MvPowerSeries.coeff (Finsupp.single j 1) g *
          MvPowerSeries.coeff (Finsupp.single k 1) (a j) := by
  have hsub : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have ha1 : ∀ j, 1 ≤ (a j).order := fun j =>
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (ha0 j)
  rw [MvPowerSeries.coeff_subst hsub]
  rw [finsum_eq_finsetSum_of_support_subset _ (s :=
      Finset.univ.image (fun j : Fin n => Finsupp.single j 1))]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j _
      have hprod : (Finsupp.single j 1).prod (fun s e => a s ^ e) = a j := by
        simp [Finsupp.prod_single_index]
      rw [hprod, smul_eq_mul]
    · intro x _ y _ h
      exact (Finsupp.single_left_inj (by norm_num)).mp h
  · intro d hd
    simp only [Function.mem_support] at hd
    rw [Finset.coe_image]
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
    have hcd : MvPowerSeries.coeff d g ≠ 0 := fun h => hd (by rw [h, zero_smul])
    have hcprod : MvPowerSeries.coeff (Finsupp.single k 1) (d.prod fun s e => a s ^ e) ≠ 0 :=
      fun h => hd (by rw [h, smul_zero])
    have hdeg1 : 1 ≤ Finsupp.degree d := by
      by_contra hc
      push Not at hc
      interval_cases h : Finsupp.degree d
      · rw [(Finsupp.degree_eq_zero_iff d).mp h, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          hg0] at hcd
        exact hcd rfl
    have hdeg2 : Finsupp.degree d ≤ 1 := by
      by_contra hc
      push Not at hc
      have hbound := degree_le_order_prod a ha1 d
      have hlt :
        ((Finsupp.degree (Finsupp.single k 1) : ℕ) : ℕ∞) < (d.prod fun s e => a s ^ e).order := by
        refine lt_of_lt_of_le ?_ hbound
        rw [Finsupp.degree_single]
        exact_mod_cast hc
      exact hcprod (MvPowerSeries.coeff_of_lt_order hlt)
    obtain ⟨i, rfl⟩ : ∃ i, d = Finsupp.single i 1 := by
      apply (Finsupp.sum_eq_one_iff d).mp
      rw [Finsupp.sum, ← Finsupp.degree_apply]
      exact le_antisymm hdeg2 hdeg1
    exact ⟨i, rfl⟩

/-- **Two-sided inversion.** If a family `y` of elements of the maximal ideal of
`R[[x_1, …, x_n]]` with zero constant coefficients admits a family `b`, also with zero
constant coefficients, that is a right inverse for substitution on the variables
(`subst y (b i) = x_i`), then substitution along `y` is injective. -/
theorem injective_subst_of_right_inverse {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {n : ℕ} (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) R))
    (hy0 : ∀ j, MvPowerSeries.constantCoeff (y j : MvPowerSeries (Fin n) R) = (0 : R))
    (b : Fin n → MvPowerSeries (Fin n) R)
    (hb0 : ∀ i, MvPowerSeries.constantCoeff (b i) = (0 : R))
    (hkey : ∀ i,
      MvPowerSeries.subst (fun j => (y j : MvPowerSeries (Fin n) R)) (b i) = MvPowerSeries.X i) :
    Function.Injective
      (MvPowerSeries.subst (fun j => (y j : MvPowerSeries (Fin n) R)) :
        MvPowerSeries (Fin n) R → MvPowerSeries (Fin n) R) := by
  classical
  set yf : Fin n → MvPowerSeries (Fin n) R := fun j => (y j : MvPowerSeries (Fin n) R)
  have hsuby : MvPowerSeries.HasSubst yf := MvPowerSeries.hasSubst_of_constantCoeff_zero hy0
  have hbsub : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  -- Package `b` as a family in the maximal ideal.
  have hbmem : ∀ i, b i ∈ maximalIdeal (MvPowerSeries (Fin n) R) := fun i => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      hb0 i]
    exact not_isUnit_zero
  set b' : Fin n → maximalIdeal (MvPowerSeries (Fin n) R) := fun i => ⟨b i, hbmem i⟩
  -- The Jacobian of `b'` is a left inverse of the Jacobian of `y`, hence a unit; this comes
  -- from the degree-1 part of `subst yf (b i) = X i`.
  have hmatrix : (jacobian b') * (jacobian y) = 1 := by
    ext i k
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hlin := coeff_single_one_subst yf hy0 (b i) (hb0 i) k
    rw [hkey i] at hlin
    rw [coeff_single_one_X] at hlin
    have hsum :
      (∑ j, (jacobian b') i j * (jacobian y) j k) =
        ∑ j,
          MvPowerSeries.coeff (Finsupp.single j 1) (b i) *
            MvPowerSeries.coeff (Finsupp.single k 1) (yf j) :=
      Finset.sum_congr rfl fun _ _ => rfl
    rw [hsum, ← hlin]
    simp [eq_comm]
  have hb'det : IsUnit (jacobian b').det := by
    have : IsUnit ((jacobian b').det * (jacobian y).det) := by
      rw [← Matrix.det_mul, hmatrix, Matrix.det_one]; exact isUnit_one
    exact isUnit_of_mul_isUnit_left this
  -- The right-inverse family `c` of `subst b`; note `(b' j : _) = b j` definitionally.
  obtain ⟨c, hc0, hckey⟩ := exists_right_inverse_of_jacobian_isUnit b' hb0 hb'det
  have hckey' : ∀ i, MvPowerSeries.subst b (c i) = MvPowerSeries.X i := hckey
  have hcsub : MvPowerSeries.HasSubst c := MvPowerSeries.hasSubst_of_constantCoeff_zero hc0
  -- `subst yf ∘ subst b = id` and `subst b ∘ subst c = id`; hence `subst yf = subst c`.
  have hSyc : ∀ g, MvPowerSeries.subst yf g = MvPowerSeries.subst c g := fun g =>
    calc
      MvPowerSeries.subst yf g =
          MvPowerSeries.subst yf (MvPowerSeries.subst b (MvPowerSeries.subst c g)) := by
        rw [subst_subst_of_subst_eq_X hbsub hcsub hckey']
      _ = MvPowerSeries.subst c g := subst_subst_of_subst_eq_X hsuby hbsub hkey _
  exact Function.LeftInverse.injective (g := MvPowerSeries.subst b) fun g => by
    rw [hSyc, subst_subst_of_subst_eq_X hbsub hcsub hckey']

/-- (1b) **Injectivity.** Under the same hypotheses, `φ` is injective. -/
theorem engine_one_injective {K : Type*} [Field K] {n : ℕ}
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) K)) (hy : IsRegularSystemOfParameters y) :
    Function.Injective
      ((MvPowerSeries.substAlgHom (hasSubst_of_mem_maximalIdeal y) :
        MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)) := by
  obtain ⟨b, hb0, hkey⟩ := exists_right_inverse_subst_field y hy
  rw [MvPowerSeries.coe_substAlgHom]
  exact injective_subst_of_right_inverse y
    (fun j => constantCoeff_eq_zero_of_mem_maximalIdeal (y j).2) b hb0 hkey

/-! ## Engine 2 (statement 3): the comparison map is an isomorphism over a Cohen ring. -/

/-- The degree-1 coefficient of a product `g * h` lies in any ideal `J` containing both
constant coefficients. -/
theorem coeff_single_one_mul_mem_of_constantCoeff_mem {Λ : Type*} [CommRing Λ] {n : ℕ} (i : Fin n)
    (g h : MvPowerSeries (Fin n) Λ) (J : Ideal Λ) (hg : MvPowerSeries.constantCoeff g ∈ J)
    (hh : MvPowerSeries.constantCoeff h ∈ J) :
    MvPowerSeries.coeff (Finsupp.single i 1) (g * h) ∈ J := by
  rw [coeff_single_one_mul]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ hh)

/-- **Jacobian invertibility from RSOP (Cohen case).** If `(p, y_1, …, y_n)` is a regular
system of parameters of `B = Λ[[x_1,…,x_n]]` with `p = algebraMap pr` and the `y_i` having
zero constant coefficient, then the `n×n` variable-direction Jacobian matrix
`M i j = coeff (single j 1) (y i)` is invertible over `Λ`. -/
theorem isUnit_det_jacobian_of_rsop_cohen {Λ : Type*} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] {n : ℕ} (pr : ℕ) (hunif : maximalIdeal Λ = Ideal.span {(pr : Λ)})
    (p : maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hp : (p : MvPowerSeries (Fin n) Λ) = algebraMap Λ (MvPowerSeries (Fin n) Λ) (pr : Λ))
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hy0 : ∀ i, MvPowerSeries.constantCoeff (y i : MvPowerSeries (Fin n) Λ) = (0 : Λ))
    (hrsp : IsRegularSystemOfParameters (Fin.cons p y)) : IsUnit (jacobian y).det := by
  classical
  set p₀ : Λ := (pr : Λ) with hp₀
  obtain ⟨-, hspan_rsop⟩ := hrsp
  let B := MvPowerSeries (Fin n) Λ
  let κ := ResidueField B
  let m := maximalIdeal B
  have hp0ne : p₀ ≠ 0 := by
    intro h
    have hb : maximalIdeal Λ = ⊥ := by rw [hunif, h, Ideal.span_singleton_eq_bot.mpr rfl]
    exact (IsDiscreteValuationRing.not_isField Λ) (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hb)
  have hp0mem : p₀ ∈ maximalIdeal Λ := by rw [hunif, Ideal.mem_span_singleton]
  -- `p = C p₀`.
  have hpC : (p : B) = MvPowerSeries.C p₀ := by
    rw [hp, MvPowerSeries.algebraMap_apply]
    simp [hp₀]
  have hmemiff : ∀ (f : B), f ∈ m ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal Λ :=
    mem_maximalIdeal_iff_constantCoeff_mem
  have aux_cc0 : ∀ (f : B), f ∈ m → MvPowerSeries.constantCoeff f ∈ maximalIdeal Λ := fun f hf =>
    (hmemiff f).mp hf
  have hC_mem : ∀ (a : Λ), a ∈ maximalIdeal Λ → (MvPowerSeries.C a : B) ∈ m := by
    intro a ha
    rwa [hmemiff, MvPowerSeries.constantCoeff_C]
  have hC_residue0 : ∀ (a : Λ), a ∈ maximalIdeal Λ → residue B (MvPowerSeries.C a) = 0 := by
    intro a ha
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hC_mem a ha)
  have hdiv : ∀ (x : B), x ∈ m → ∃ a : Λ, MvPowerSeries.constantCoeff x = p₀ * a := by
    intro x hx
    have := (hmemiff x).mp hx
    rw [hunif, Ideal.mem_span_singleton'] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by rw [← ha, mul_comm]⟩
  let dvp : m → Λ := fun f => (hdiv (f : B) f.2).choose
  have hdvp : ∀ (f : m), MvPowerSeries.constantCoeff (f : B) = p₀ * dvp f := fun f =>
    (hdiv (f : B) f.2).choose_spec
  have hdvp_add : ∀ (f g : m), dvp (f + g) = dvp f + dvp g := by
    intro f g
    refine mul_left_cancel₀ hp0ne ?_
    rw [mul_add, ← hdvp f, ← hdvp g, ← hdvp (f + g)]
    show MvPowerSeries.constantCoeff ((f + g : m) : B) = _
    rw [Submodule.coe_add, map_add]
  have hdvp_smul : ∀ (b : B) (f : m), dvp (b • f) = MvPowerSeries.constantCoeff b * dvp f := by
    intro b f
    refine mul_left_cancel₀ hp0ne ?_
    rw [← hdvp (b • f)]
    show MvPowerSeries.constantCoeff ((b • f : m) : B) = _
    have : ((b • f : m) : B) = b * (f : B) := rfl
    rw [this, map_mul, hdvp f]; ring
  -- The cotangent functional `Λ₀ : m → κ^{n+1}` reading off `(dvp, linear coeffs) mod m`.
  let Λ₀ : m →ₗ[B] (Fin (n + 1) → κ) :=
    { toFun := fun f =>
        Fin.cons (residue B (MvPowerSeries.C (a := dvp f)))
          (fun i =>
            residue B (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single i 1) (f : B))))
      map_add' := by
        intro f g
        funext j
        refine Fin.cases ?_ ?_ j
        · simp only [Fin.cons_zero]
          rw [hdvp_add, map_add, map_add, Pi.add_apply, Fin.cons_zero, Fin.cons_zero]
        · intro i
          simp only [Fin.cons_succ]
          rw [Submodule.coe_add, map_add, map_add, map_add, Pi.add_apply, Fin.cons_succ,
            Fin.cons_succ]
      map_smul' := by
        intro b f
        funext j
        refine Fin.cases ?_ ?_ j
        · simp only [Fin.cons_zero, RingHom.id_apply, Pi.smul_apply]
          rw [hdvp_smul, map_mul, map_mul]
          rw [Algebra.smul_def, ← residue_eq_residue_C_constantCoeff b]
          rfl
        · intro i
          simp only [Fin.cons_succ, RingHom.id_apply, Pi.smul_apply]
          have hsmul : ((b • f : m) : B) = b * (f : B) := rfl
          rw [hsmul, coeff_single_one_mul, map_add, map_add]
          have hterm2 :
            residue B
                (MvPowerSeries.C (a :=
                  MvPowerSeries.coeff (Finsupp.single i 1) b *
                    MvPowerSeries.constantCoeff (f : B))) =
              0 :=
            hC_residue0 _ (Ideal.mul_mem_left _ _ (aux_cc0 _ f.2))
          rw [hterm2, add_zero, map_mul, map_mul]
          rw [Algebra.smul_def, ← residue_eq_residue_C_constantCoeff b]
          rfl }
  have Λ₀_apply0 : ∀ (f : m), Λ₀ f 0 = residue B (MvPowerSeries.C (a := dvp f)) := fun f => rfl
  have Λ₀_applys :
    ∀ (f : m) (i : Fin n),
      Λ₀ f i.succ =
        residue B (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single i 1) (f : B))) := by
    intro f i
    change
      (Fin.cons (residue B (MvPowerSeries.C (a := dvp f)))
              (fun i =>
                residue B
                  (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single i 1) (f : B)))) :
            Fin (n + 1) → κ)
          i.succ =
        _
    rw [Fin.cons_succ]
  have Λ₀_kill : m • (⊤ : Submodule B m) ≤ LinearMap.ker Λ₀ := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [LinearMap.mem_ker]
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [Λ₀_apply0]
      apply hC_residue0
      rw [hunif, Ideal.mem_span_singleton']
      obtain ⟨a, ha⟩ := (hdiv r hr); obtain ⟨b, hb⟩ := (hdiv (x : B) x.2)
      refine ⟨a * b, ?_⟩
      refine mul_left_cancel₀ hp0ne ?_
      rw [← hdvp (r • x)]
      have hcoe : ((r • x : m) : B) = r * (x : B) := rfl
      rw [hcoe, map_mul, ha, hb]; ring
    · intro i
      rw [Λ₀_applys]
      apply hC_residue0
      have hcoe : ((r • x : m) : B) = r * (x : B) := rfl
      rw [hcoe]
      exact
        coeff_single_one_mul_mem_of_constantCoeff_mem i r (x : B) (maximalIdeal Λ) (aux_cc0 _ hr)
          (aux_cc0 _ x.2)
  let ΛA : CotangentSpace B →ₗ[B] (Fin (n + 1) → κ) := Submodule.liftQ _ Λ₀ Λ₀_kill
  let Λκ : CotangentSpace B →ₗ[κ] (Fin (n + 1) → κ) :=
    LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective ΛA
  have Λκ_toCotangent : ∀ (x : m), Λκ (m.toCotangent x) = Λ₀ x := fun _ => rfl
  -- The φ ring hom Λ →+* κ used for the descent.
  set φ : Λ →+* κ := (IsLocalRing.residue B).comp (MvPowerSeries.C (σ := Fin n) (R := Λ)) with hφ
  -- The RSOP cotangent family.
  set w : Fin (n + 1) → CotangentSpace B := fun j =>
    m.toCotangent ((Fin.cons p y : Fin (n + 1) → maximalIdeal B) j) with hw
  -- `Λκ` is surjective: it sends the variable/`p` cotangent classes onto the standard basis.
  have hpmem : (MvPowerSeries.C p₀ : B) ∈ m := hC_mem p₀ hp0mem
  have hXmem : ∀ j : Fin n, (MvPowerSeries.X j : B) ∈ m := fun j => by
    simp [hmemiff]
  set vbas : Fin (n + 1) → CotangentSpace B :=
    Fin.cons (m.toCotangent ⟨MvPowerSeries.C p₀, hpmem⟩)
      (fun i => m.toCotangent ⟨MvPowerSeries.X i, hXmem i⟩) with
    hvbas
  have hΛvbas : ∀ j, Λκ (vbas j) = (Pi.single j 1 : Fin (n + 1) → κ) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [hvbas, Fin.cons_zero, Λκ_toCotangent]
      funext k
      refine Fin.cases ?_ ?_ k
      · rw [Λ₀_apply0]
        have hdvp1 : dvp ⟨MvPowerSeries.C p₀, hpmem⟩ = 1 := by
          refine mul_left_cancel₀ hp0ne ?_
          rw [← hdvp ⟨MvPowerSeries.C p₀, hpmem⟩]
          change MvPowerSeries.constantCoeff (MvPowerSeries.C p₀ : B) = _
          rw [MvPowerSeries.constantCoeff_C, mul_one]
        rw [hdvp1, MvPowerSeries.C.map_one, map_one, Pi.single_eq_same]
      · intro i
        rw [Λ₀_applys]
        change
          residue B
              (MvPowerSeries.C (a :=
                MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.C p₀ : B))) =
            _
        rw [MvPowerSeries.coeff_C]
        rw [ite_eq_right
            (by
              intro hc
              have : (Finsupp.single i 1 : Fin n →₀ ℕ) = 0 := hc
              apply_fun (fun f => f i) at this
              simp at this)]
        rw [MvPowerSeries.C.map_zero, map_zero]
        rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i)]
    · intro i
      rw [hvbas, Fin.cons_succ, Λκ_toCotangent]
      funext k
      refine Fin.cases ?_ ?_ k
      · rw [Λ₀_apply0]
        have hdvp0 : dvp ⟨MvPowerSeries.X i, hXmem i⟩ = 0 := by
          refine mul_left_cancel₀ hp0ne ?_
          rw [← hdvp ⟨MvPowerSeries.X i, hXmem i⟩]
          change MvPowerSeries.constantCoeff (MvPowerSeries.X i : B) = _
          rw [MvPowerSeries.constantCoeff_X, mul_zero]
        rw [hdvp0, MvPowerSeries.C.map_zero, map_zero]
        rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
      · intro i'
        rw [Λ₀_applys]
        change
          residue B
              (MvPowerSeries.C (a :=
                MvPowerSeries.coeff (Finsupp.single i' 1) (MvPowerSeries.X i : B))) =
            _
        rw [coeff_single_one_X, Pi.single_apply]
        split_ifs <;> simp_all
  -- Row `j` of `T := Λκ ∘ w` is `Λκ (w j)`.
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) κ := Matrix.of (fun j => Λκ (w j)) with hT
  have hTrow : ∀ j, T j = Λκ (w j) := fun j => rfl
  have hTunit : IsUnit T.det := isUnit_det_of_span_eq_top Λκ vbas w hΛvbas hspan_rsop
  -- `T` is block-triangular: row 0 is `Pi.single 0 1` and row `i.succ` is `Fin.cons 0 (M̄ i)`.
  -- Its determinant equals the determinant of the lower-right block `M̄ = (jacobian y).map φ`.
  set Mbar : Matrix (Fin n) (Fin n) κ := (jacobian y).map φ with hMbar
  -- Row 0 of T.
  have hTrow0 : T 0 = Pi.single 0 1 := by
    rw [hTrow]
    change Λκ (m.toCotangent ((Fin.cons p y : Fin (n + 1) → maximalIdeal B) 0)) = _
    rw [Fin.cons_zero]
    have hpeq : m.toCotangent p = m.toCotangent ⟨MvPowerSeries.C p₀, hpmem⟩ := by
      congr 1; exact Subtype.ext hpC
    rw [hpeq]
    have := hΛvbas 0
    rwa [hvbas, Fin.cons_zero] at this
  -- Rows i.succ of T.
  have hTrowsucc :
    ∀ (i : Fin n) (k : Fin (n + 1)),
      T i.succ k = (Fin.cons (0 : κ) (fun j => Mbar i j) : Fin (n + 1) → κ) k := by
    intro i k
    rw [hTrow]
    change Λκ (m.toCotangent ((Fin.cons p y : Fin (n + 1) → maximalIdeal B) i.succ)) k = _
    rw [Fin.cons_succ, Λκ_toCotangent]
    refine Fin.cases ?_ ?_ k
    · rw [Λ₀_apply0, Fin.cons_zero]
      -- dvp (y i) = 0 since constantCoeff (y i) = 0.
      have hdvpyi : dvp (y i) = 0 := by
        refine mul_left_cancel₀ hp0ne ?_
        rw [← hdvp (y i), hy0 i, mul_zero]
      rw [hdvpyi, MvPowerSeries.C.map_zero, map_zero]
    · intro j
      rw [Λ₀_applys, Fin.cons_succ]
      change
        residue B (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single j 1) (y i : B))) =
          Mbar i j
      rw [hMbar, Matrix.map_apply, jacobian_apply, hφ]
      rfl
  -- det T = det Mbar via the block-triangular structure.
  have hdetT : T.det = Mbar.det := by
    rw [Matrix.det_succ_row_zero]
    rw [Finset.sum_eq_single 0]
    · -- the `j = 0` term: sign `(-1)^0 = 1`, entry `T 0 0 = 1`, minor `= Mbar`.
      have hentry : T 0 0 = 1 := by rw [hTrow0, Pi.single_eq_same]
      have hminor : (T.submatrix Fin.succ (Fin.succAbove 0)).det = Mbar.det := by
        have hmateq : T.submatrix Fin.succ (Fin.succAbove 0) = Mbar := by
          ext i j
          rw [Matrix.submatrix_apply, Fin.succAbove_zero, hTrowsucc i j.succ, Fin.cons_succ]
        rw [hmateq]
      rw [hentry, hminor]
      simp
    · intro b _ hb
      have : T 0 b = 0 := by rw [hTrow0, Pi.single_eq_of_ne hb]
      rw [this, mul_zero, zero_mul]
    · intro hcontra; exact absurd (Finset.mem_univ 0) hcontra
  -- IsUnit det Mbar.
  rw [hdetT] at hTunit
  -- Mbar.det = φ (jacobian y).det.
  have hdetmap : Mbar.det = φ (jacobian y).det := by
    rw [hMbar, RingHom.map_det]; rfl
  rw [hdetmap] at hTunit
  -- Descend: IsUnit (φ (det M)) ⟹ IsUnit (det M).
  by_contra hx
  have hx' : (jacobian y).det ∈ maximalIdeal Λ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hx
  have hz : φ (jacobian y).det = 0 := by
    rw [hφ, RingHom.comp_apply]
    exact hC_residue0 _ hx'
  rw [hz] at hTunit
  exact not_isUnit_zero hTunit

/-- **Formal inverse function theorem (Cohen case), the hard analytic core of Engine 2
surjectivity.** Given a Cohen ring `Λ` with uniformizer the prime `pr`, and a regular
system of parameters `(p, y_1, …, y_n)` of `B = Λ[[x_1,…,x_n]]` with `p = algebraMap pr`
and the `y_i` having zero constant coefficient, there is a family `b : Fin n → B` with
zero constant coefficient (so `HasSubst b`) that is a RIGHT INVERSE to the substitution
`subst y` on the variables: `subst y (b i) = X i` for all `i`. -/
theorem exists_right_inverse_subst_cohen {Λ : Type*} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] {n : ℕ} (pr : ℕ) (hunif : maximalIdeal Λ = Ideal.span {(pr : Λ)})
    (p : maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hp : (p : MvPowerSeries (Fin n) Λ) = algebraMap Λ (MvPowerSeries (Fin n) Λ) (pr : Λ))
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hy0 : ∀ i, MvPowerSeries.constantCoeff (y i : MvPowerSeries (Fin n) Λ) = (0 : Λ))
    (hrsp : IsRegularSystemOfParameters (Fin.cons p y)) :
    ∃ b : Fin n → MvPowerSeries (Fin n) Λ,
      (∀ i, MvPowerSeries.constantCoeff (b i) = (0 : Λ)) ∧
        (∀ i,
          MvPowerSeries.subst (fun j => (y j : MvPowerSeries (Fin n) Λ)) (b i) =
            MvPowerSeries.X i) :=
  exists_right_inverse_of_jacobian_isUnit y hy0
    (isUnit_det_jacobian_of_rsop_cohen pr hunif p hp y hy0 hrsp)

/-- (3a) **Surjectivity, Cohen case.** With `Λ` a Cohen ring, `p` its uniformizer viewed
in `B`, and `(p, y_1, …, y_n)` a regular system of parameters of `B`, the `Λ`-algebra map
`ψ : Λ[[Y]] →ₐ[Λ] B`, `X i ↦ y i`, is surjective. -/
theorem engine_two_surjective {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    {n : ℕ} (pr : ℕ) (hunif : maximalIdeal Λ = Ideal.span {(pr : Λ)})
    (p : maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hp : (p : MvPowerSeries (Fin n) Λ) = algebraMap Λ (MvPowerSeries (Fin n) Λ) (pr : Λ))
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hy0 : ∀ i, MvPowerSeries.constantCoeff (y i : MvPowerSeries (Fin n) Λ) = (0 : Λ))
    (hrsp : IsRegularSystemOfParameters (Fin.cons p y)) :
    Function.Surjective
      ((MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hy0) :
        MvPowerSeries (Fin n) Λ →ₐ[Λ] MvPowerSeries (Fin n) Λ)) := by
  obtain ⟨b, hb0, hkey⟩ := exists_right_inverse_subst_cohen pr hunif p hp y hy0 hrsp
  rw [MvPowerSeries.coe_substAlgHom]
  exact surjective_subst_of_right_inverse (MvPowerSeries.hasSubst_of_constantCoeff_zero hy0)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hb0) hkey

/-- (3b) **Injectivity, Cohen case.** Under the same hypotheses, `ψ` is injective. -/
theorem engine_two_injective {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    {n : ℕ} (pr : ℕ) (hunif : maximalIdeal Λ = Ideal.span {(pr : Λ)})
    (p : maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hp : (p : MvPowerSeries (Fin n) Λ) = algebraMap Λ (MvPowerSeries (Fin n) Λ) (pr : Λ))
    (y : Fin n → maximalIdeal (MvPowerSeries (Fin n) Λ))
    (hy0 : ∀ i, MvPowerSeries.constantCoeff (y i : MvPowerSeries (Fin n) Λ) = (0 : Λ))
    (hrsp : IsRegularSystemOfParameters (Fin.cons p y)) :
    Function.Injective
      ((MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hy0) :
        MvPowerSeries (Fin n) Λ →ₐ[Λ] MvPowerSeries (Fin n) Λ)) := by
  obtain ⟨b, hb0, hkey⟩ := exists_right_inverse_subst_cohen pr hunif p hp y hy0 hrsp
  rw [MvPowerSeries.coe_substAlgHom]
  exact injective_subst_of_right_inverse y hy0 b hb0 hkey

end Stacks.MvPowerSeries.RegularParameters
