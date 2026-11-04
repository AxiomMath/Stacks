module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.MvPowerSeries.Inverse

public import StacksFrontier.RingTheory.CohenRing
public import StacksFrontier.RingTheory.MvPowerSeries.InverseFunction

@[expose] public section

-- Needed for `extend_partial_rsop_field`: the `A := MvPowerSeries (Fin n) K` abbreviation must
-- unfold when elaborating the `finSumFinEquiv`/`Fin.cast` reindexing of the cotangent basis.
set_option backward.isDefEq.respectTransparency false

/-!
# Cotangent spaces of power series rings and quotients by initial variables

For `A = K[[x_1, …, x_n]]` over a field `K`, or `B = Λ[[x_1, …, x_n]]` over a Cohen ring `Λ`,
this file computes an explicit basis of the cotangent space `m/m²` given by the variables, so
its dimension is `n` (resp. `n + 1`), and identifies the quotient by the first `r` variables
with the power series ring in the remaining `n − r` variables. It also extends part of a
regular system of parameters of `A` to a full one.
-/

open IsLocalRing MvPowerSeries

namespace Stacks.MvPowerSeries.RegularParameters

/-- Over a local ring `R`, a power series lies in the maximal ideal of `MvPowerSeries σ R`
exactly when its constant coefficient lies in the maximal ideal of `R`. -/
theorem mem_maximalIdeal_iff_constantCoeff_mem {σ R : Type*} [CommRing R] [IsLocalRing R]
    (f : MvPowerSeries σ R) :
    f ∈ maximalIdeal (MvPowerSeries σ R) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- Membership in the maximal ideal of `MvPowerSeries σ K` (`K` a field) is exactly having zero
constant coefficient. -/
theorem mem_maximalIdeal_iff_constantCoeff_eq_zero_field {σ K : Type*} [Field K]
    (f : MvPowerSeries σ K) :
    f ∈ maximalIdeal (MvPowerSeries σ K) ↔ MvPowerSeries.constantCoeff f = (0 : K) := by
  rw [mem_maximalIdeal_iff_constantCoeff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_ne_zero, not_ne_iff]

/-- A power series with zero constant coefficient is a combination `∑ i, X i * g i` where the
constant coefficient of each `g i` is the linear coefficient of `f` at `X i`. -/
theorem exists_sum_X_mul_of_constantCoeff_eq_zero {R : Type*} [CommRing R] {n : ℕ}
    (f : MvPowerSeries (Fin n) R) (h0 : MvPowerSeries.constantCoeff f = (0 : R)) :
    ∃ g : Fin n → MvPowerSeries (Fin n) R,
      (∀ i, MvPowerSeries.constantCoeff (g i) = MvPowerSeries.coeff (Finsupp.single i 1) f) ∧
        f = ∑ i : Fin n, X i * g i := by
  classical
  have hsupp (e : Fin n →₀ ℕ) (i : Fin n) : (e + Finsupp.single i 1).support.Nonempty :=
    ⟨i, by simp⟩
  have hlc (a b : Fin n →₀ ℕ) (ha : a.support.Nonempty) (hb : b.support.Nonempty) (h : a = b) :
      a.support.min' ha = b.support.min' hb := by
    subst h; rfl
  let g : Fin n → MvPowerSeries (Fin n) R := fun i e =>
    if (e + Finsupp.single i 1).support.min' (hsupp e i) = i then
      MvPowerSeries.coeff (e + Finsupp.single i 1) f
    else 0
  have hgcoeff (i : Fin n) (e : Fin n →₀ ℕ) :
      MvPowerSeries.coeff e (g i) =
        if (e + Finsupp.single i 1).support.min' (hsupp e i) = i then
          MvPowerSeries.coeff (e + Finsupp.single i 1) f
        else 0 := rfl
  have hgmem (i : Fin n) :
      MvPowerSeries.constantCoeff (g i) = MvPowerSeries.coeff (Finsupp.single i 1) f := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hgcoeff i 0]
    have hz : (0 + Finsupp.single i 1 : Fin n →₀ ℕ) = Finsupp.single i 1 := zero_add _
    rw [ite_eq_left (by rw [hlc _ _ _ (by simp) hz]; simp), hz]
  have hterm (i : Fin n) (d : Fin n →₀ ℕ) (hd : Finsupp.single i 1 ≤ d)
      (hdne : d.support.Nonempty) :
      MvPowerSeries.coeff d (X i * g i) =
        if d.support.min' hdne = i then MvPowerSeries.coeff d f else 0 := by
    have heq : (d - Finsupp.single i 1) + Finsupp.single i 1 = d := tsub_add_cancel_of_le hd
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, ite_eq_left hd, one_mul,
      hgcoeff i (d - Finsupp.single i 1), hlc _ d _ hdne heq, heq]
  have hterm0 (i : Fin n) (d : Fin n →₀ ℕ) (hd : ¬Finsupp.single i 1 ≤ d) :
      MvPowerSeries.coeff d (X i * g i) = 0 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, ite_eq_right hd]
  refine ⟨g, hgmem, ?_⟩
  ext d
  rw [map_sum]
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    exact (Finset.sum_eq_zero fun i _ => hterm0 i 0 (by simp)).symm
  have hdne : d.support.Nonempty := Finsupp.support_nonempty_iff.2 hd0
  set i₀ := d.support.min' hdne with hi₀
  have hi₀le : Finsupp.single i₀ 1 ≤ d := Finsupp.single_le_iff.2
    (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 (Finset.min'_mem d.support hdne)))
  rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀), hterm i₀ d hi₀le hdne, ite_eq_left rfl]
  intro i _ hne
  by_cases hle : Finsupp.single i 1 ≤ d
  · rw [hterm i d hle hdne, ite_eq_right fun h => hne (hi₀ ▸ h.symm)]
  · exact hterm0 i d hle

/-- The ideal generated by the variables is the kernel of the constant coefficient. -/
theorem mem_span_X_iff_constantCoeff_eq_zero {A : Type*} [CommRing A] (n : ℕ)
    (x : MvPowerSeries (Fin n) A) :
    x ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A)) ↔
      MvPowerSeries.constantCoeff x = 0 := by
  constructor
  · intro hx
    refine RingHom.mem_ker.mp (Ideal.span_le.2 ?_ hx)
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · intro hx
    obtain ⟨g, _, hg⟩ := exists_sum_X_mul_of_constantCoeff_eq_zero x hx
    rw [hg]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)


/-- Over a local ring, a power series and its constant term have the same residue. -/
theorem residue_eq_residue_C_constantCoeff {σ R : Type*} [CommRing R] [IsLocalRing R]
    (a : MvPowerSeries σ R) :
    residue (MvPowerSeries σ R) a =
      residue (MvPowerSeries σ R) (MvPowerSeries.C (MvPowerSeries.constantCoeff a)) := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
  simp

/-- Over a local ring `R`, a power series with zero constant coefficient and zero linear
coefficients (all degree-1 coefficients vanish) lies in the square of the maximal ideal of
`MvPowerSeries (Fin n) R`. -/
theorem mem_sq_maximalIdeal_of_linear_coeff_zero {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (f : MvPowerSeries (Fin n) R) (h0 : MvPowerSeries.constantCoeff f = (0 : R))
    (h1 : ∀ i : Fin n, MvPowerSeries.coeff (Finsupp.single i 1) f = (0 : R)) :
    f ∈ (maximalIdeal (MvPowerSeries (Fin n) R)) ^ 2 := by
  obtain ⟨g, hg, hsum⟩ := exists_sum_X_mul_of_constantCoeff_eq_zero f h0
  have hmem : ∀ x : MvPowerSeries (Fin n) R, MvPowerSeries.constantCoeff x = 0 →
      x ∈ maximalIdeal (MvPowerSeries (Fin n) R) := fun x hx => by
    rw [mem_maximalIdeal_iff_constantCoeff_mem, hx]; exact Submodule.zero_mem _
  rw [hsum, pow_two]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul
    (hmem _ (MvPowerSeries.constantCoeff_X i)) (hmem _ ((hg i).trans (h1 i)))

/-- A family in a module whose images under a linear map to `ι → κ` are the standard basis
vectors is linearly independent. -/
private theorem linearIndependent_of_apply_eq_single {ι κ M : Type*} [Finite ι] [DecidableEq ι]
    [CommRing κ] [AddCommGroup M] [Module κ M] (v : ι → M) (L : M →ₗ[κ] (ι → κ))
    (h : ∀ j, L (v j) = Pi.single j 1) : LinearIndependent κ v := by
  refine LinearIndependent.of_comp L ?_
  have : L ∘ v = Pi.basisFun κ ι := funext fun j => by
    rw [Function.comp_apply, h, Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun κ ι).linearIndependent

/-- The residue of `a` acts on a cotangent class as `a` does. -/
private theorem residue_smul_toCotangent {A : Type*} [CommRing A] [IsLocalRing A] (a : A)
    (x : maximalIdeal A) :
    residue A a • (maximalIdeal A).toCotangent x = (maximalIdeal A).toCotangent (a • x) := by
  rw [show residue A a • (maximalIdeal A).toCotangent x = a • (maximalIdeal A).toCotangent x from
    by rw [← IsScalarTower.algebraMap_smul (ResidueField A)]; rfl]
  rw [map_smul]

/-- The linear coefficient at `X i` of the variable `X j`, viewed in the residue field. -/
private theorem residue_C_coeff_single_X {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (i j : Fin n) :
    residue (MvPowerSeries (Fin n) R)
        (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single i 1) (X j))) =
      if i = j then 1 else 0 := by
  by_cases h : i = j <;>
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, h]

/-- Subtracting the constant term and the linear part of a power series leaves an element of the
square of the maximal ideal. -/
private theorem sub_C_add_sum_C_mul_X_mem_sq {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (f : MvPowerSeries (Fin n) R) (c : Fin n → R)
    (hc : ∀ i, c i = MvPowerSeries.coeff (Finsupp.single i 1) f) :
    f - (MvPowerSeries.C (MvPowerSeries.constantCoeff f) + ∑ i : Fin n, MvPowerSeries.C (c i) * X i)
      ∈ maximalIdeal (MvPowerSeries (Fin n) R) ^ 2 := by
  rw [← sub_sub]
  refine mem_sq_maximalIdeal_of_linear_coeff_zero _ (by simp [map_sum]) fun j => ?_
  simp [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, MvPowerSeries.coeff_C, hc,
    Finsupp.single_left_inj one_ne_zero]

/-- The cotangent space of `A = MvPowerSeries (Fin n) K` over its residue field has a basis
indexed by `Fin n`. -/
theorem nonempty_basis_cotangentSpace_field {K : Type*} [Field K] {n : ℕ} :
    Nonempty
      (Module.Basis (Fin n) (ResidueField (MvPowerSeries (Fin n) K))
        (CotangentSpace (MvPowerSeries (Fin n) K))) := by
  classical
  set A := MvPowerSeries (Fin n) K
  set κ := ResidueField A
  set m := maximalIdeal A with hm
  have aux_cc0 : ∀ (f : A), f ∈ m → MvPowerSeries.constantCoeff f = 0 := fun f hf =>
    (mem_maximalIdeal_iff_constantCoeff_eq_zero_field f).mp hf
  have aux_coeff_smul :
    ∀ (i : Fin n) (a f : A),
      MvPowerSeries.constantCoeff f = 0 →
        MvPowerSeries.coeff (Finsupp.single i 1) (a * f) =
          MvPowerSeries.constantCoeff a * MvPowerSeries.coeff (Finsupp.single i 1) f := by
    intro i a f hf
    rw [coeff_single_one_mul, hf, mul_zero, add_zero]
  have aux_residue_const :
    ∀ (a : A), residue A a = residue A (MvPowerSeries.C (a := MvPowerSeries.constantCoeff a)) :=
    residue_eq_residue_C_constantCoeff
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
        change
          residue A
              (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single i 1) ((a • f : m) : A))) =
            a • residue A (MvPowerSeries.C (a := MvPowerSeries.coeff (Finsupp.single i 1) (f : A)))
        have hsmul : ((a • f : m) : A) = a * f := rfl
        rw [hsmul, aux_coeff_smul i a f hf, map_mul, map_mul]
        rw [Algebra.smul_def, ← aux_residue_const a]
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
    rw [Λ₀_apply]
    have hrx : ((r • x : m) : A) = r * x := rfl
    rw [hrx, coeff_single_one_mul, aux_cc0 _ hr, aux_cc0 _ x.2, zero_mul, mul_zero, add_zero]
    simp
  let ΛA : CotangentSpace A →ₗ[A] (Fin n → κ) := Submodule.liftQ _ Λ₀ Λ₀_kill
  let Λκ : CotangentSpace A →ₗ[κ] (Fin n → κ) :=
    LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective ΛA
  have Λκ_toCotangent : ∀ (x : m), Λκ (m.toCotangent x) = Λ₀ x := fun _ => rfl
  have hXmem : ∀ j : Fin n, (MvPowerSeries.X j : A) ∈ m := fun j =>
    (mem_maximalIdeal_iff_constantCoeff_eq_zero_field _).2 (MvPowerSeries.constantCoeff_X j)
  set v : Fin n → CotangentSpace A := fun j => m.toCotangent ⟨MvPowerSeries.X j, hXmem j⟩ with hv
  have hΛv : ∀ j, Λκ (v j) = (Pi.single j 1 : Fin n → κ) := by
    intro j
    rw [hv]; simp only []
    rw [Λκ_toCotangent]
    funext i
    rw [Λ₀_apply]
    exact (residue_C_coeff_single_X i j).trans (Pi.single_apply j 1 i).symm
  have hindep : LinearIndependent κ v := linearIndependent_of_apply_eq_single v Λκ hΛv
  have hspan : ⊤ ≤ Submodule.span κ (Set.range v) := by
    intro ξ _
    obtain ⟨f, rfl⟩ := m.toCotangent_surjective ξ
    set c : Fin n → K := fun i => MvPowerSeries.coeff (Finsupp.single i 1) (f : A) with hc
    have hhmem : (f : A) - ∑ i : Fin n, MvPowerSeries.C (a := c i) * MvPowerSeries.X i ∈ m ^ 2 := by
      have := sub_C_add_sum_C_mul_X_mem_sq (f : A) c fun _ => rfl
      rwa [aux_cc0 _ f.2, map_zero, zero_add] at this
    have hfdecomp :
      m.toCotangent f = ∑ i : Fin n, (residue A (MvPowerSeries.C (a := c i))) • v i := by
      have hRHS :
        (∑ i : Fin n, (residue A (MvPowerSeries.C (a := c i))) • (v i)) =
          m.toCotangent
            (∑ i : Fin n,
              ((MvPowerSeries.C (a := c i) : A)) • (⟨MvPowerSeries.X i, hXmem i⟩ : m)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hv]; exact residue_smul_toCotangent _ _
      rw [hRHS, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero, Submodule.coe_sub]
      have hcoe :
        (((∑ i : Fin n, ((MvPowerSeries.C (a := c i) : A)) • (⟨MvPowerSeries.X i, hXmem i⟩ : m))) :
            m) =
          (⟨∑ i : Fin n, MvPowerSeries.C (a := c i) * MvPowerSeries.X i, by
              exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hXmem i)⟩ :
            m) := by
        apply Subtype.ext
        simp only [Submodule.coe_sum, SetLike.val_smul, smul_eq_mul]
      rw [hcoe]
      exact hhmem
    rw [hfdecomp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hindep hspan⟩

/-- The cotangent space of `A = MvPowerSeries (Fin n) K` has dimension `n` over its residue
field. -/
theorem finrank_cotangentSpace_field {K : Type*} [Field K] {n : ℕ} :
    Module.finrank (ResidueField (MvPowerSeries (Fin n) K))
        (CotangentSpace (MvPowerSeries (Fin n) K)) =
      n := by
  obtain ⟨bas⟩ := nonempty_basis_cotangentSpace_field (K := K) (n := n)
  rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]

/-- The cotangent space of `A = MvPowerSeries (Fin n) K` is finite-dimensional over the
residue field. -/
instance finiteDimensional_cotangentSpace_field {K : Type*} [Field K] {n : ℕ} :
    Module.Finite (ResidueField (MvPowerSeries (Fin n) K))
      (CotangentSpace (MvPowerSeries (Fin n) K)) := by
  obtain ⟨bas⟩ := nonempty_basis_cotangentSpace_field (K := K) (n := n)
  exact Module.Finite.of_basis bas

/-- For a Cohen ring `Λ`, the cotangent space of `B = MvPowerSeries (Fin n) Λ` over its residue
field has a basis indexed by `Fin (n + 1)`. -/
theorem nonempty_basis_cotangentSpace_cohen {Λ : Type*} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] (hΛ : IsCohenRing Λ) {n : ℕ} :
    Nonempty
      (Module.Basis (Fin (n + 1)) (ResidueField (MvPowerSeries (Fin n) Λ))
        (CotangentSpace (MvPowerSeries (Fin n) Λ))) := by
  classical
  set B := MvPowerSeries (Fin n) Λ
  set κ := ResidueField B
  set m := maximalIdeal B with hm
  obtain ⟨pr, hprime, hunif⟩ := hΛ.uniformizer_prime
  set p₀ : Λ := (pr : Λ)
  have hp0ne : p₀ ≠ 0 := by
    intro h
    have hb : maximalIdeal Λ = ⊥ := by rw [hunif, h, Ideal.span_singleton_eq_bot.mpr rfl]
    exact (IsDiscreteValuationRing.not_isField Λ) (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hb)
  have hp0mem : p₀ ∈ maximalIdeal Λ := by rw [hunif, Ideal.mem_span_singleton]
  have hmemiff : ∀ (f : B), f ∈ m ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal Λ := by
    intro f; rw [hm]; exact mem_maximalIdeal_iff_constantCoeff_mem f
  have aux_cc0 : ∀ (f : B), f ∈ m → MvPowerSeries.constantCoeff f ∈ maximalIdeal Λ := fun f hf =>
    (hmemiff f).mp hf
  have hC_mem : ∀ (a : Λ), a ∈ maximalIdeal Λ → (MvPowerSeries.C a : B) ∈ m := fun a ha => by
    rwa [hmemiff, MvPowerSeries.constantCoeff_C]
  have hC_residue0 : ∀ (a : Λ), a ∈ maximalIdeal Λ → residue B (MvPowerSeries.C a) = 0 :=
    fun a ha => (residue_eq_zero_iff _).2 (hC_mem a ha)
  have aux_residue_const :
    ∀ (a : B), residue B a = residue B (MvPowerSeries.C (a := MvPowerSeries.constantCoeff a)) :=
    residue_eq_residue_C_constantCoeff
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
          rw [Algebra.smul_def, ← aux_residue_const b]
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
          rw [hterm2, add_zero, map_mul, map_mul, Algebra.smul_def, ← aux_residue_const b]
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
  have hpmem : (MvPowerSeries.C p₀ : B) ∈ m := hC_mem p₀ hp0mem
  have hXmem : ∀ j : Fin n, (MvPowerSeries.X j : B) ∈ m := by
    intro j
    rw [hmemiff, MvPowerSeries.constantCoeff_X]; exact Submodule.zero_mem _
  set v : Fin (n + 1) → CotangentSpace B :=
    Fin.cons (m.toCotangent ⟨MvPowerSeries.C p₀, hpmem⟩)
      (fun i => m.toCotangent ⟨MvPowerSeries.X i, hXmem i⟩) with
    hv
  have hv0 : v 0 = m.toCotangent ⟨MvPowerSeries.C p₀, hpmem⟩ := by rw [hv, Fin.cons_zero]
  have hvs : ∀ i : Fin n, v i.succ = m.toCotangent ⟨MvPowerSeries.X i, hXmem i⟩ := by
    intro i; rw [hv, Fin.cons_succ]
  have hΛv : ∀ j, Λκ (v j) = (Pi.single j 1 : Fin (n + 1) → κ) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [hv0, Λκ_toCotangent]
      funext k
      refine Fin.cases ?_ ?_ k
      · rw [Λ₀_apply0]
        have hdvp1 : dvp ⟨MvPowerSeries.C p₀, hpmem⟩ = 1 := by
          refine mul_left_cancel₀ hp0ne ?_
          rw [← hdvp ⟨MvPowerSeries.C p₀, hpmem⟩]
          show MvPowerSeries.constantCoeff (MvPowerSeries.C p₀ : B) = _
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
      rw [hvs i, Λκ_toCotangent]
      funext k
      refine Fin.cases ?_ ?_ k
      · rw [Λ₀_apply0]
        have hdvp0 : dvp ⟨MvPowerSeries.X i, hXmem i⟩ = 0 := by
          refine mul_left_cancel₀ hp0ne ?_
          rw [← hdvp ⟨MvPowerSeries.X i, hXmem i⟩]
          show MvPowerSeries.constantCoeff (MvPowerSeries.X i : B) = _
          rw [MvPowerSeries.constantCoeff_X, mul_zero]
        rw [hdvp0, MvPowerSeries.C.map_zero, map_zero]
        rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
      · intro i'
        rw [Λ₀_applys]
        rw [residue_C_coeff_single_X i' i, Pi.single_apply]
        simp only [Fin.succ_inj]
  have hindep : LinearIndependent κ v := linearIndependent_of_apply_eq_single v Λκ hΛv
  have hspan : ⊤ ≤ Submodule.span κ (Set.range v) := by
    intro ξ _
    obtain ⟨f, rfl⟩ := m.toCotangent_surjective ξ
    set c : Fin n → Λ := fun i => MvPowerSeries.coeff (Finsupp.single i 1) (f : B) with hc
    have hhmem := sub_C_add_sum_C_mul_X_mem_sq (f : B) c fun _ => rfl
    have hfdecomp :
      m.toCotangent f =
        (residue B (MvPowerSeries.C (a := dvp f))) • v 0 +
          ∑ i : Fin n, (residue B (MvPowerSeries.C (a := c i))) • v (i.succ) := by
      rw [hv0]
      have hvs' :
        ∀ i : Fin n,
          (residue B (MvPowerSeries.C (a := c i))) • v (i.succ) =
            m.toCotangent
              ((MvPowerSeries.C (a := c i) : B) • (⟨MvPowerSeries.X i, hXmem i⟩ : m)) := by
        intro i; rw [hvs i]; exact residue_smul_toCotangent _ _
      rw [residue_smul_toCotangent]
      rw [show
          (∑ i : Fin n, (residue B (MvPowerSeries.C (a := c i))) • v (i.succ)) =
            m.toCotangent
              (∑ i : Fin n,
                ((MvPowerSeries.C (a := c i) : B)) • (⟨MvPowerSeries.X i, hXmem i⟩ : m))
          from by
          rw [map_sum]; exact Finset.sum_congr rfl (fun i _ => hvs' i)]
      rw [← map_add, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero, Submodule.coe_sub]
      have hcoe :
        (((MvPowerSeries.C (a := dvp f) : B) • (⟨MvPowerSeries.C p₀, hpmem⟩ : m) +
              ∑ i : Fin n,
                ((MvPowerSeries.C (a := c i) : B)) • (⟨MvPowerSeries.X i, hXmem i⟩ : m)) :
            m) =
          (⟨MvPowerSeries.C (MvPowerSeries.constantCoeff (f : B)) +
                ∑ i : Fin n, MvPowerSeries.C (a := c i) * MvPowerSeries.X i,
              Ideal.add_mem _ (hC_mem _ (aux_cc0 _ f.2))
                (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hXmem i))⟩ :
            m) := by
        apply Subtype.ext
        simp only [Submodule.coe_add, Submodule.coe_sum, SetLike.val_smul, smul_eq_mul]
        congr 1
        rw [← map_mul]
        congr 1
        rw [mul_comm, ← hdvp f]
      rw [hcoe]
      change
        (f : B) -
            (MvPowerSeries.C (MvPowerSeries.constantCoeff (f : B)) +
              ∑ i : Fin n, MvPowerSeries.C (a := c i) * MvPowerSeries.X i) ∈
          m ^ 2
      exact hhmem
    rw [hfdecomp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.succ, rfl⟩))
  exact ⟨Module.Basis.mk hindep hspan⟩

/-- For a Cohen ring `Λ`, the cotangent space of `B = MvPowerSeries (Fin n) Λ` has dimension
`n + 1` over its residue field. -/
theorem finrank_cotangentSpace_cohen {Λ : Type*} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] (hΛ : IsCohenRing Λ) {n : ℕ} :
    Module.finrank (ResidueField (MvPowerSeries (Fin n) Λ))
        (CotangentSpace (MvPowerSeries (Fin n) Λ)) =
      n + 1 := by
  obtain ⟨bas⟩ := nonempty_basis_cotangentSpace_cohen (Λ := Λ) hΛ (n := n)
  rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]

/-! ## Quotient by the initial variables -/

namespace QuotInitVars

/-- Embedding `Fin (n-r) → Fin n` placing indices on the last `n-r` coordinates: `j ↦ r+j`. -/
def embedFn {n r : ℕ} (hr : r ≤ n) : Fin (n - r) → Fin n := fun j =>
  ⟨r + (j : ℕ), by omega⟩

/-- The underlying natural number of `embedFn hr j` is `r + j`. -/
@[simp] theorem embedFn_val {n r : ℕ} (hr : r ≤ n) (j : Fin (n - r)) :
    ((embedFn hr j : Fin n) : ℕ) = r + (j : ℕ) := rfl

/-- The map `embedFn` is injective. -/
theorem embedFn_injective {n r : ℕ} (hr : r ≤ n) : Function.Injective (embedFn hr) := by
  intro x y h; have := congrArg Fin.val h; simp only [embedFn_val] at this; exact Fin.ext (by omega)

/-- The induced map on exponent multisets `(Fin (n-r) →₀ ℕ) → (Fin n →₀ ℕ)`. -/
noncomputable def embedIdx {n r : ℕ} (hr : r ≤ n) (β : Fin (n - r) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.mapDomain (embedFn hr) β

/-- The partial inverse of `embedIdx` (forgetting the first `r` coordinates). -/
noncomputable def pushIdx {n r : ℕ} (hr : r ≤ n) (d : Fin n →₀ ℕ) : Fin (n - r) →₀ ℕ :=
  Finsupp.comapDomain (embedFn hr) d ((embedFn_injective hr).injOn)

/-- An exponent vanishing on the first `r` coordinates is recovered by `embedIdx` from its image
under `pushIdx`. -/
theorem embedIdx_pushIdx {n r : ℕ} (hr : r ≤ n) (d : Fin n →₀ ℕ)
    (hgood : ∀ s : Fin n, (s : ℕ) < r → d s = 0) : embedIdx hr (pushIdx hr d) = d :=
  Finsupp.mapDomain_comapDomain (embedFn hr) (embedFn_injective hr) d fun s hs => by
    have hsr : r ≤ (s : ℕ) := by
      by_contra h
      exact Finsupp.mem_support_iff.1 hs (hgood s (by omega))
    exact ⟨⟨(s : ℕ) - r, by omega⟩, Fin.ext (by simp only [embedFn_val]; omega)⟩

/-- `pushIdx` is a left inverse of `embedIdx`. -/
theorem pushIdx_embedIdx {n r : ℕ} (hr : r ≤ n) (β : Fin (n - r) →₀ ℕ) :
    pushIdx hr (embedIdx hr β) = β :=
  Finsupp.comapDomain_mapDomain (embedFn hr) (embedFn_injective hr) β

/-- An exponent in the image of `embedIdx` vanishes on the first `r` coordinates. -/
theorem embedIdx_apply_eq_zero_of_lt {n r : ℕ} (hr : r ≤ n) (β : Fin (n - r) →₀ ℕ) (s : Fin n)
    (hs : (s : ℕ) < r) : embedIdx hr β s = 0 := by
  rw [embedIdx]; apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp only [embedFn_val] at this; omega

/-- A power series all of whose monomials involve at least one variable from a finset `s`
lies in the ideal generated by the corresponding variables. -/
theorem mem_span_X_image_of_coeff_eq_zero {σ R : Type*} [CommRing R] (s : Finset σ)
    (g : MvPowerSeries σ R)
    (hg : ∀ α : σ →₀ ℕ, (∀ i ∈ s, α i = 0) → MvPowerSeries.coeff α g = 0) :
    g ∈ Ideal.span ((fun a => (MvPowerSeries.X a : MvPowerSeries σ R)) '' s) := by
  classical
  induction s using Finset.induction generalizing g with
  | empty =>
    have hz : g = 0 := by
      ext α; simpa using hg α (by simp)
    rw [hz]; exact Ideal.zero_mem _
  | insert a t ha ih =>
    set g' : MvPowerSeries σ R := fun β => if β a = 0 then g β else 0
    have hdvd : MvPowerSeries.X a ∣ (g - g') := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub]
      have hc : MvPowerSeries.coeff m g' = if m a = 0 then MvPowerSeries.coeff m g else 0 := rfl
      rw [hc, ite_eq_left hm, sub_self]
    have hg'cond : ∀ α : σ →₀ ℕ, (∀ i ∈ t, α i = 0) → MvPowerSeries.coeff α g' = 0 := by
      intro α hα
      have hc : MvPowerSeries.coeff α g' = if α a = 0 then MvPowerSeries.coeff α g else 0 := rfl
      rw [hc]
      split
      · next h0 =>
          exact hg _ fun i hi => (Finset.mem_insert.mp hi).elim (· ▸ h0) (hα i)
      · rfl
    have hg'mem :
      g' ∈ Ideal.span ((fun a => (MvPowerSeries.X a : MvPowerSeries σ R)) '' (t : Set σ)) :=
      ih g' hg'cond
    have hsubset : ((t : Set σ)) ⊆ ((insert a t : Finset σ) : Set σ) := by
      rw [Finset.coe_insert]; exact Set.subset_insert _ _
    have hspan_sub :
      ((fun a => (MvPowerSeries.X a : MvPowerSeries σ R)) '' (t : Set σ)) ⊆
        ((fun a => (MvPowerSeries.X a : MvPowerSeries σ R)) ''
          ((insert a t : Finset σ) : Set σ)) :=
      Set.image_mono hsubset
    have hg'mem' :
      g' ∈
        Ideal.span
          ((fun a => (MvPowerSeries.X a : MvPowerSeries σ R)) ''
            ((insert a t : Finset σ) : Set σ)) :=
      Ideal.span_mono hspan_sub hg'mem
    have hXamem :
      MvPowerSeries.X a ∈
        Ideal.span
          ((fun a => (MvPowerSeries.X a : MvPowerSeries σ R)) ''
            ((insert a t : Finset σ) : Set σ)) := by
      apply Ideal.subset_span; exact ⟨a, by simp, rfl⟩
    have hsub_mem :
      (g - g') ∈
        Ideal.span
          ((fun a => (MvPowerSeries.X a : MvPowerSeries σ R)) ''
            ((insert a t : Finset σ) : Set σ)) := by
      obtain ⟨q, hq⟩ := hdvd; rw [hq]; exact Ideal.mul_mem_right q _ hXamem
    have hgeq : g = (g - g') + g' := by ring
    rw [hgeq]; exact Ideal.add_mem _ hsub_mem hg'mem'

/-- The coefficient of a `Finsupp.prod` of the forward substitution family. -/
theorem coeff_prod_pow_eq_ite {R : Type*} [CommSemiring R] {n r : ℕ} (hr : r ≤ n)
    (a : Fin n → MvPowerSeries (Fin (n - r)) R) (ha0 : ∀ i : Fin n, (i : ℕ) < r → a i = 0)
    (haX : ∀ i : Fin n, ∀ h : ¬(i : ℕ) < r, a i = MvPowerSeries.X ⟨(i : ℕ) - r, by omega⟩)
    (d : Fin n →₀ ℕ) (β : Fin (n - r) →₀ ℕ) :
    MvPowerSeries.coeff β (d.prod fun s e => a s ^ e) = if d = embedIdx hr β then 1 else 0 := by
  classical
  by_cases hgood : ∀ s : Fin n, (s : ℕ) < r → d s = 0
  · have hprodmon :
      (d.prod fun s e => a s ^ e) = MvPowerSeries.monomial (pushIdx hr d) (1 : R) := by
      conv_lhs => rw [← embedIdx_pushIdx hr d hgood, embedIdx]
      rw [Finsupp.prod_mapDomain_index_inj (embedFn_injective hr)]
      have hstep :
        ∀ (j : Fin (n - r)) (e : ℕ),
          a (embedFn hr j) ^ e = (MvPowerSeries.X j : MvPowerSeries (Fin (n - r)) R) ^ e := by
        intro j e; congr 1
        rw [haX (embedFn hr j)
            (by
              simp only [embedFn_val]; omega)]
        congr 1; apply Fin.ext; simp only [embedFn_val]; omega
      rw [Finsupp.prod_congr (fun j _ => hstep j _), ← MvPowerSeries.monomial_one_eq]
    rw [hprodmon, MvPowerSeries.coeff_monomial]
    by_cases hde : d = embedIdx hr β
    · rw [ite_eq_left hde, ite_eq_left]; rw [hde, pushIdx_embedIdx]
    · rw [ite_eq_right hde, ite_eq_right]
      intro hcontra; apply hde; rw [← embedIdx_pushIdx hr d hgood, hcontra]
  · push Not at hgood
    obtain ⟨s₀, hs₀r, hs₀pos⟩ := hgood
    have hmem : s₀ ∈ d.support := Finsupp.mem_support_iff.mpr hs₀pos
    have hzero : (d.prod fun s e => a s ^ e) = 0 := by
      rw [Finsupp.prod]; apply Finset.prod_eq_zero hmem
      rw [ha0 s₀ hs₀r, zero_pow (Finsupp.mem_support_iff.mp hmem)]
    rw [hzero, map_zero, ite_eq_right]
    intro hde; apply hs₀pos; rw [hde, embedIdx_apply_eq_zero_of_lt hr β s₀ hs₀r]

/-- The coefficient identity for the forward substitution map: substituting `X i ↦ 0`
for `i < r` and `X i ↦ X (i-r)` otherwise reads off coefficients via `embedIdx`. -/
theorem coeff_subst_forward {R : Type*} [CommRing R] {n r : ℕ} (hr : r ≤ n)
    (a : Fin n → MvPowerSeries (Fin (n - r)) R) (ha0 : ∀ i : Fin n, (i : ℕ) < r → a i = 0)
    (haX : ∀ i : Fin n, ∀ h : ¬(i : ℕ) < r, a i = MvPowerSeries.X ⟨(i : ℕ) - r, by omega⟩)
    (hasub : MvPowerSeries.HasSubst a) (f : MvPowerSeries (Fin n) R) (β : Fin (n - r) →₀ ℕ) :
    MvPowerSeries.coeff β (MvPowerSeries.subst a f) = MvPowerSeries.coeff (embedIdx hr β) f := by
  classical
  rw [MvPowerSeries.coeff_subst hasub f β]
  have hG :
    ∀ d : Fin n →₀ ℕ,
      MvPowerSeries.coeff β (d.prod fun s e => a s ^ e) = if d = embedIdx hr β then 1 else 0 :=
    fun d => coeff_prod_pow_eq_ite hr a ha0 haX d β
  have hfun :
    (fun d : Fin n →₀ ℕ =>
        MvPowerSeries.coeff d f • MvPowerSeries.coeff β (d.prod fun s e => a s ^ e)) =
      (fun d => if d = embedIdx hr β then MvPowerSeries.coeff (embedIdx hr β) f else 0) := by
    funext d; rw [hG d]; by_cases h : d = embedIdx hr β <;> simp [h]
  rw [hfun, finsum_eq_single _ (embedIdx hr β)]
  · simp
  · intro d hd; simp [hd]

end QuotInitVars

/-- The kernel of the substitution `X i ↦ 0` (`i < r`), `X i ↦ X (i - r)` (`i ≥ r`) is the ideal
generated by the first `r` variables. -/
theorem ker_substAlgHom_initial_vars {R : Type*} [CommRing R] {n r : ℕ} (hr : r ≤ n)
    (a : Fin n → MvPowerSeries (Fin (n - r)) R) (ha0 : ∀ i : Fin n, (i : ℕ) < r → a i = 0)
    (haX : ∀ i : Fin n, ∀ h : ¬(i : ℕ) < r, a i = MvPowerSeries.X ⟨(i : ℕ) - r, by omega⟩)
    (hasub : MvPowerSeries.HasSubst a) :
    RingHom.ker (MvPowerSeries.substAlgHom (R := R) hasub) =
      Ideal.span
        (Set.range
          (fun i : Fin r => (MvPowerSeries.X (Fin.castLE hr i) : MvPowerSeries (Fin n) R))) := by
  classical
  have hsetEq :
    (Set.range
        (fun i : Fin r => (MvPowerSeries.X (Fin.castLE hr i) : MvPowerSeries (Fin n) R))) =
      (fun a => (MvPowerSeries.X a : MvPowerSeries (Fin n) R)) ''
        ((Finset.univ.image (Fin.castLE hr) : Finset (Fin n)) : Set (Fin n)) := by
    simp [Set.range_comp']
  rw [hsetEq]
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker, MvPowerSeries.substAlgHom_apply] at hf
    refine QuotInitVars.mem_span_X_image_of_coeff_eq_zero _ _ fun α hα => ?_
    have hgood : ∀ s : Fin n, (s : ℕ) < r → α s = 0 := fun s hs =>
      hα _ (Finset.mem_image.2 ⟨⟨(s : ℕ), hs⟩, Finset.mem_univ _, Fin.ext (by simp [Fin.castLE])⟩)
    have key := QuotInitVars.coeff_subst_forward hr a ha0 haX hasub f (QuotInitVars.pushIdx hr α)
    rw [QuotInitVars.embedIdx_pushIdx hr α hgood] at key
    rw [← key, hf, map_zero]
  · rw [Ideal.span_le]
    rintro x ⟨y, hy, rfl⟩
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    rw [SetLike.mem_coe, RingHom.mem_ker, MvPowerSeries.substAlgHom_apply,
      MvPowerSeries.subst_X hasub]
    exact ha0 _ (by simp [Fin.castLE])

/-- The quotient of `MvPowerSeries (Fin n) R` by the ideal generated by the first `r` variables is
isomorphic, as an `R`-algebra, to `MvPowerSeries (Fin (n - r)) R`. -/
theorem quotient_initial_vars {R : Type*} [CommRing R] {n r : ℕ} (hr : r ≤ n) :
    Nonempty
      ((MvPowerSeries (Fin n) R ⧸
          Ideal.span
            (Set.range
              (fun i : Fin r =>
                (MvPowerSeries.X (Fin.castLE hr i) : MvPowerSeries (Fin n) R)))) ≃ₐ[R]
        MvPowerSeries (Fin (n - r)) R) := by
  classical
  set a : Fin n → MvPowerSeries (Fin (n - r)) R := fun i =>
    if h : (i : ℕ) < r then 0 else MvPowerSeries.X ⟨(i : ℕ) - r, by omega⟩ with ha_def
  have ha0 : ∀ i : Fin n, (i : ℕ) < r → a i = 0 := fun i hi => by
    simp only [ha_def, dite_eq_left hi]
  have haX : ∀ i : Fin n, ∀ h : ¬(i : ℕ) < r, a i = MvPowerSeries.X ⟨(i : ℕ) - r, by omega⟩ :=
    fun i h => by simp only [ha_def, dite_eq_right h]
  have hasub : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    by_cases hi : (i : ℕ) < r
    · rw [ha0 i hi, map_zero]
    · rw [haX i hi, MvPowerSeries.constantCoeff_X]
  set b : Fin (n - r) → MvPowerSeries (Fin n) R := fun j =>
    MvPowerSeries.X (QuotInitVars.embedFn hr j) with hb_def
  have hbsub : MvPowerSeries.HasSubst b :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hrinv : Function.RightInverse (MvPowerSeries.substAlgHom (R := R) hbsub)
      (MvPowerSeries.substAlgHom (R := R) hasub) := by
    intro z
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply,
      ← Function.comp_apply (f := MvPowerSeries.subst a) (g := MvPowerSeries.subst b),
      MvPowerSeries.subst_comp_subst hbsub hasub]
    have hid : (fun j : Fin (n - r) => MvPowerSeries.subst a (b j)) = MvPowerSeries.X := by
      funext j
      rw [hb_def, MvPowerSeries.subst_X hasub,
        haX (QuotInitVars.embedFn hr j) (by simp only [QuotInitVars.embedFn_val]; omega)]
      congr 1
      exact Fin.ext (by simp only [QuotInitVars.embedFn_val]; omega)
    rw [hid, MvPowerSeries.subst_self]
    rfl
  exact ⟨(Ideal.quotientEquivAlgOfEq R (ker_substAlgHom_initial_vars hr a ha0 haX hasub).symm).trans
    (Ideal.quotientKerAlgEquivOfRightInverse (R₁ := R) hrinv)⟩

/-- Given `z_1, …, z_r` in the maximal ideal of `A = MvPowerSeries (Fin n) K` whose cotangent
images are linearly independent, there exist `w_1, …, w_{n−r}` such that the concatenation
`z ++ w` is a regular system of parameters of `A`. -/
theorem extend_partial_rsop_field {K : Type*} [Field K] {n r : ℕ}
    (z : Fin r → maximalIdeal (MvPowerSeries (Fin n) K))
    (hz : IsPartOfRegularSystemOfParameters z) (hr : r ≤ n) :
    ∃ w : Fin (n - r) → maximalIdeal (MvPowerSeries (Fin n) K),
      IsRegularSystemOfParameters (Fin.append z w ∘ Fin.cast (by omega : n = r + (n - r))) := by
  classical
  set A := MvPowerSeries (Fin n) K
  unfold IsPartOfRegularSystemOfParameters at hz
  set v : Fin r → CotangentSpace A := fun i => (maximalIdeal A).toCotangent (z i) with hv
  have hindv : LinearIndependent (ResidueField A) v := hz
  set S : Submodule (ResidueField A) (CotangentSpace A) :=
    Submodule.span (ResidueField A) (Set.range v) with hS
  obtain ⟨W, hW⟩ := S.exists_isCompl
  have hfinV : Module.finrank (ResidueField A) (CotangentSpace A) = n :=
    finrank_cotangentSpace_field (K := K) (n := n)
  have hfinS : Module.finrank (ResidueField A) S = r := by
    rw [hS, finrank_span_eq_card hindv, Fintype.card_fin]
  have hfinW : Module.finrank (ResidueField A) W = n - r := by
    have hadd := Submodule.finrank_add_eq_of_isCompl hW
    rw [hfinS, hfinV] at hadd
    omega
  set bW : Module.Basis (Fin (n - r)) (ResidueField A) W :=
    Module.finBasisOfFinrankEq (ResidueField A) W hfinW with hbW
  set bW' : Fin (n - r) → CotangentSpace A := fun j => (bW j : CotangentSpace A) with hbW'
  have hsurj : Function.Surjective (maximalIdeal A).toCotangent :=
    Ideal.toCotangent_surjective (maximalIdeal A)
  set w : Fin (n - r) → maximalIdeal A := fun j => (hsurj (bW' j)).choose with hw
  have hwspec : ∀ j, (maximalIdeal A).toCotangent (w j) = bW' j := fun j =>
    (hsurj (bW' j)).choose_spec
  refine ⟨w, ?_⟩
  unfold IsRegularSystemOfParameters
  set g : Fin n → CotangentSpace A := fun i =>
    (maximalIdeal A).toCotangent ((Fin.append z w ∘ Fin.cast (by omega : n = r + (n - r))) i) with
    hg
  have happend :
    (fun i => (maximalIdeal A).toCotangent (Fin.append z w i)) = Fin.append v bW' := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k; simp only [Fin.append_left]; rfl
    · intro k; simp only [Fin.append_right]; exact hwspec k
  have hgeq : g = Fin.append v bW' ∘ Fin.cast (by omega : n = r + (n - r)) := by
    funext i
    simp only [hg, Function.comp_apply]
    have := congrFun happend (Fin.cast (by omega : n = r + (n - r)) i)
    simpa using this
  have hindbW' : LinearIndependent (ResidueField A) bW' := by
    rw [hbW']
    exact bW.linearIndependent.map' W.subtype (by simp)
  have hspanbW' : Submodule.span (ResidueField A) (Set.range bW') = W := by
    have hr : Set.range bW' = (W.subtype) '' (Set.range bW) := by
      rw [hbW']; rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image]
    simp [bW.span_eq]
  have hdisj :
    Disjoint (Submodule.span (ResidueField A) (Set.range v))
      (Submodule.span (ResidueField A) (Set.range bW')) := by
    rw [hspanbW']
    have hvS : Submodule.span (ResidueField A) (Set.range v) = S := hS.symm
    rw [hvS]
    exact hW.disjoint
  have hsum : LinearIndependent (ResidueField A) (Sum.elim v bW') :=
    LinearIndependent.sum_type hindv hindbW' hdisj
  have happ : Fin.append v bW' = Sum.elim v bW' ∘ finSumFinEquiv.symm := by
    have hcomp : Fin.append v bW' ∘ finSumFinEquiv = Sum.elim v bW' := by
      ext x; cases x <;> simp [Fin.append, Fin.addCases]
    rw [← hcomp]; ext x; simp
  have hindapp : LinearIndependent (ResidueField A) (Fin.append v bW') := by
    rw [happ]; exact hsum.comp _ finSumFinEquiv.symm.injective
  have hindg : LinearIndependent (ResidueField A) g := by
    rw [hgeq]
    exact hindapp.comp _ (Fin.cast_injective _)
  refine ⟨hindg, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hsub : Subsingleton (CotangentSpace A) := Module.finrank_zero_iff.mp hfinV
    exact Subsingleton.elim _ _
  · have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hcard : Fintype.card (Fin n) = Module.finrank (ResidueField A) (CotangentSpace A) := by
      rw [Fintype.card_fin, hfinV]
    exact hindg.span_eq_top_of_card_eq_finrank hcard

end Stacks.MvPowerSeries.RegularParameters
