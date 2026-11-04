module

public import Mathlib.RingTheory.DualNumber
public import Mathlib.LinearAlgebra.Matrix.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ProcyclicQuotientDegreeTwo
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.SpecialFibre
public import StacksFrontier.Deformation.Representation.FixedDeterminantFiniteness.SquareZero
public import StacksFrontier.Deformation.Representation.FixedDeterminantFlatness.AdjointRepresentation

/-!
# The tangent space of a fixed-determinant deformation ring bounds `H ¹(π, ad⁰)`

Let `R` be the universal deformation ring of `ρ₀ : π → GLₙ(𝐅_ℓ)` with determinant fixed to `δ`,
let `ρ₀` be absolutely irreducible and `ℓ ∤ n`, and let `y₁, …, y_d ∈ 𝔪_R` generate `𝔪_R` modulo
`𝔪_R² + ℓR`. A locally constant `1`-cocycle `z : π → ad⁰` gives the deformation
`g ↦ (1 + ε z(g)) ρ₀(g)` over the dual numbers `𝐅_ℓ[ε]`, with determinant `δ`, hence a
classifying map `ψ_z : R → 𝐅_ℓ[ε]`. The vector `(ψ_z(y_i))_i ∈ (ε 𝐅_ℓ)^d` determines `ψ_z`, and
`ψ_z` determines the class of `z` up to coboundaries. Hence `H ¹(π, ad⁰)` (locally constant
cochains) is finite of dimension at most `d`.

## Main results

* `Deformation.IsUniversalFixedDeterminantDeformation.finiteDimensional_lcH1_and_finrank_le`:
  `H ¹(π, ad⁰)` is finite-dimensional of dimension at most `d`.
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.GroupCohomology groupCohomology

universe u v

namespace Deformation

/-! ### Matrices over the dual numbers -/

section DualMatrix

variable {ℓ n : ℕ} [Fact ℓ.Prime]

local notation "D" => DualNumber (ZMod ℓ)

/-- The matrix `a + ε b` over the dual numbers. -/
def dmat (a b : Matrix (Fin n) (Fin n) (ZMod ℓ)) : Matrix (Fin n) (Fin n) D :=
  fun i j => TrivSqZeroExt.inl (a i j) + TrivSqZeroExt.inr (b i j)

/-- The real part of an entry of `a + ε b` is the corresponding entry of `a`. -/
@[simp] lemma dmat_fst (a b : Matrix (Fin n) (Fin n) (ZMod ℓ)) (i j : Fin n) :
    (dmat a b i j).fst = a i j := by simp [dmat]

/-- The `ε`-part of an entry of `a + ε b` is the corresponding entry of `b`. -/
@[simp] lemma dmat_snd (a b : Matrix (Fin n) (Fin n) (ZMod ℓ)) (i j : Fin n) :
    (dmat a b i j).snd = b i j := by simp [dmat]

omit [Fact ℓ.Prime] in
/-- Two matrices over the dual numbers are equal if their entries have equal real parts and equal
`ε`-parts. -/
lemma dmat_ext {X Y : Matrix (Fin n) (Fin n) D}
    (h1 : ∀ i j, (X i j).fst = (Y i j).fst) (h2 : ∀ i j, (X i j).snd = (Y i j).snd) : X = Y :=
  Matrix.ext fun i j => TrivSqZeroExt.ext (h1 i j) (h2 i j)

/-- Every matrix over the dual numbers is `a + ε b` for its real part `a` and `ε`-part `b`. -/
lemma eq_dmat (X : Matrix (Fin n) (Fin n) D) :
    X = dmat (fun i j => (X i j).fst) (fun i j => (X i j).snd) :=
  dmat_ext (fun i j => (dmat_fst (fun i j => (X i j).fst) (fun i j => (X i j).snd) i j).symm)
    (fun i j => (dmat_snd (fun i j => (X i j).fst) (fun i j => (X i j).snd) i j).symm)

/-- `(a + ε b)(c + ε d) = ac + ε (ad + bc)`. -/
lemma dmat_mul (a b c d : Matrix (Fin n) (Fin n) (ZMod ℓ)) :
    dmat a b * dmat c d = dmat (a * c) (a * d + b * c) := by
  refine dmat_ext (fun i j => ?_) (fun i j => ?_)
  · simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, dmat_fst,
      dmat_snd, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      Matrix.add_apply, Finset.sum_add_distrib]

/-- The matrix `1 + ε 0` is the identity matrix. -/
lemma dmat_one : dmat (1 : Matrix (Fin n) (Fin n) (ZMod ℓ)) 0 = 1 := by
  refine dmat_ext (fun i j => ?_) (fun i j => ?_) <;> by_cases h : i = j <;>
    simp [Matrix.one_apply, h]

/-- `a + ε b` as an invertible matrix, `a` being invertible with inverse `a'`. -/
def dunit (a a' b : Matrix (Fin n) (Fin n) (ZMod ℓ)) (h : a * a' = 1) :
    Matrix.GeneralLinearGroup (Fin n) D where
  val := dmat a b
  inv := dmat a' (-(a' * b * a'))
  val_inv := by
    rw [dmat_mul, h, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul,
      neg_add_cancel, dmat_one]
  inv_val := by
    have h' : a' * a = 1 := mul_eq_one_comm.mp h
    rw [dmat_mul, h', Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, h', Matrix.mul_one,
      add_neg_cancel, dmat_one]

/-- The underlying matrix of `dunit a a' b h` is `a + ε b`. -/
@[simp] lemma coe_dunit (a a' b : Matrix (Fin n) (Fin n) (ZMod ℓ)) (h : a * a' = 1) :
    ((dunit a a' b h : Matrix.GeneralLinearGroup (Fin n) D) : Matrix (Fin n) (Fin n) D) =
      dmat a b := rfl

/-- If `a a' = 1` and `b a'` has trace zero, then `det (a + ε b) = det a`. -/
lemma det_dmat (a b a' : Matrix (Fin n) (Fin n) (ZMod ℓ)) (h : a * a' = 1)
    (hb : (b * a').trace = 0) : (dmat a b).det = TrivSqZeroExt.inl a.det := by
  have hfac : dmat a b = dmat 1 (b * a') * dmat a 0 := by
    have h' : a' * a = 1 := mul_eq_one_comm.mp h
    rw [dmat_mul, Matrix.one_mul, Matrix.mul_zero, zero_add, Matrix.mul_assoc, h',
      Matrix.mul_one]
  have h0 : dmat a 0 = a.map (TrivSqZeroExt.inlHom (ZMod ℓ) (ZMod ℓ)) :=
    dmat_ext (fun i j => by simp [TrivSqZeroExt.inlHom])
      (fun i j => by simp [TrivSqZeroExt.inlHom])
  set I : Ideal D := RingHom.ker (TrivSqZeroExt.fstHom (ZMod ℓ) (ZMod ℓ) (ZMod ℓ)).toRingHom
  have hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0 := by
    intro x hx y hy
    simp only [I, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      TrivSqZeroExt.fstHom_apply] at hx hy
    refine TrivSqZeroExt.ext (by simp [hx]) (by simp [hx, hy])
  have h1 : dmat 1 (b * a') = 1 + (b * a').map TrivSqZeroExt.inr := by
    refine dmat_ext (fun i j => ?_) (fun i j => ?_) <;> by_cases h : i = j <;>
      simp [h]
  have hdet1 : (dmat 1 (b * a')).det = 1 := by
    rw [h1, Matrix.det_one_add_of_mul_eq_zero I hI _ (fun i j => by simp [I])]
    have : ((b * a').map (TrivSqZeroExt.inr : ZMod ℓ → D)).trace =
        TrivSqZeroExt.inr (b * a').trace := by
      simp [Matrix.trace, Finset.sum_smul]
    rw [this, hb, TrivSqZeroExt.inr_zero, add_zero]
  rw [hfac, Matrix.det_mul, hdet1, one_mul, h0]
  exact (RingHom.map_det (TrivSqZeroExt.inlHom (ZMod ℓ) (ZMod ℓ)) a).symm

/-- If `A Aᵢ = 1`, `c ≠ 0` and `A q + c u' A = c u A + q A`, then conjugating
`c⁻¹ (q - t)` by `A` changes it by `u - u'`. -/
private lemma conj_sub_eq_of_mul_add_smul {K : Type*} [Field K]
    {A Ai q u u' : Matrix (Fin n) (Fin n) K}
    {c t : K} (hAAi : A * Ai = 1) (hc : c ≠ 0) (h : A * q + c • (u' * A) = c • (u * A) + q * A) :
    A * (c⁻¹ • (q - t • 1)) * Ai - c⁻¹ • (q - t • 1) = u - u' := by
  have h₃ : A * q * Ai - q = c • (u - u') := by
    have := congrArg (· * Ai) h
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hAAi, Matrix.mul_one] at this
    rw [smul_sub, Matrix.mul_assoc]
    calc A * (q * Ai) - q = (A * (q * Ai) + c • u') - c • u' - q := by abel
      _ = c • u + q - c • u' - q := by rw [this]
      _ = c • u - c • u' := by abel
  have h₄ : A * (c⁻¹ • (q - t • 1)) * Ai - c⁻¹ • (q - t • 1) = c⁻¹ • (A * q * Ai - q) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hAAi, smul_sub]
    abel
  rw [h₄, h₃, smul_smul, inv_mul_cancel₀ hc, one_smul]

end DualMatrix

namespace IsUniversalFixedDeterminantDeformation

variable {ℓ n : ℕ} [Fact ℓ.Prime] {π : Type u} [Group π] [TopologicalSpace π]
  [IsTopologicalGroup π]
  {ρ₀ : π →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)} {δ : π →ₜ* ℤ_[ℓ]ˣ}
  {R : Type v} [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
  {reduce : R →+* ZMod ℓ} {ρuniv : π →ₜ* Matrix.GeneralLinearGroup (Fin n) R}

local notation "D" => DualNumber (ZMod ℓ)
local notation "AD" => AdZero (ρ₀.toMonoidHom)

/-- The `ℤ_[ℓ]`-algebra structure of the dual numbers over `𝐅_ℓ`. -/
abbrev dualAlgebra : Algebra ℤ_[ℓ] D :=
  ((TrivSqZeroExt.inlHom (ZMod ℓ) (ZMod ℓ)).comp PadicInt.toZMod).toAlgebra

/-- The topology of the dual numbers defined by their maximal ideal; it is discrete. -/
abbrev dualTopology : TopologicalSpace D := (maximalIdeal D).adicTopology

attribute [local instance] dualAlgebra dualTopology

/-- The square of the maximal ideal of the dual numbers over `𝐅_ℓ` is zero. -/
lemma maximalIdeal_dual_sq : maximalIdeal D ^ 2 = ⊥ := by
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow,
    Ideal.span_singleton_eq_bot, pow_two, DualNumber.eps_mul_eps]

/-- The adic topology on the dual numbers is discrete. -/
instance : DiscreteTopology D :=
  discreteTopology_adicTopology_of_pow_eq_bot _ maximalIdeal_dual_sq

/-- The topology on matrices over the dual numbers is discrete. -/
instance : DiscreteTopology (Matrix (Fin n) (Fin n) D) :=
  inferInstanceAs (DiscreteTopology (Fin n → Fin n → D))

omit [IsTopologicalGroup π] in
/-- The residual representation `ρ₀` is locally constant. -/
lemma isLocallyConstant_ρ₀ : IsLocallyConstant fun g => ρ₀ g :=
  (IsLocallyConstant.iff_continuous _).mpr ρ₀.continuous

omit [IsTopologicalGroup π] in
/-- A `1`-cocycle vanishes at the identity. -/
lemma isCocycle₁_apply_one {z : π → AD} (hz : IsCocycle₁ z) : z 1 = 0 := by
  have := hz 1 1
  simp only [mul_one, one_smul] at this
  exact add_eq_right.mp this.symm

/-- **The first order deformation `(1 + ε z) ρ₀` of a `1`-cocycle `z : π → ad⁰`.** -/
def dualRep (z : lcCocycles₁ (ZMod ℓ) π AD) : π →ₜ* Matrix.GeneralLinearGroup (Fin n) D where
  toFun g := dunit (ρ₀ g) ((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) ((z.1 g).val * ρ₀ g)
    (Units.mul_inv _)
  map_one' := by
    refine Units.ext ?_
    rw [coe_dunit, isCocycle₁_apply_one z.2.2, map_one, AdZero.val_zero, Matrix.zero_mul]
    exact dmat_one
  map_mul' g h := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_dunit, coe_dunit, coe_dunit, dmat_mul]
    have e1 : ((ρ₀ (g * h) : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) (ZMod ℓ)) =
        ρ₀ g * ρ₀ h := by rw [map_mul, Units.val_mul]
    have e2 : (z.1 (g * h)).val = (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * (z.1 h).val *
        (((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) (ZMod ℓ)) +
        (z.1 g).val := by
      rw [z.2.2 g h]
      rfl
    have hinv : (((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) (ZMod ℓ)) *
        (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) = 1 :=
      Units.inv_mul _
    rw [e1, e2]
    congr 1
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) :
      Matrix (Fin n) (Fin n) (ZMod ℓ)), hinv, Matrix.one_mul]
  continuous_toFun := by
    refine IsLocallyConstant.continuous ?_
    exact (z.2.1.comp₂ isLocallyConstant_ρ₀ Prod.mk).comp
      (fun p : AD × Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ) =>
      dunit (p.2 : Matrix (Fin n) (Fin n) (ZMod ℓ)) ((p.2⁻¹ : Matrix.GeneralLinearGroup _ _) :
        Matrix (Fin n) (Fin n) (ZMod ℓ))
        (p.1.val * (p.2 : Matrix (Fin n) (Fin n) (ZMod ℓ)))
        (Units.mul_inv _))

omit [IsTopologicalGroup π] in
/-- The matrix `dualRep z g` is `ρ₀(g) + ε z(g) ρ₀(g)`. -/
@[simp] lemma coe_dualRep (z : lcCocycles₁ (ZMod ℓ) π AD) (g : π) :
    ((dualRep z g : Matrix.GeneralLinearGroup (Fin n) D) : Matrix (Fin n) (Fin n) D) =
      dmat (ρ₀ g) ((z.1 g).val * (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ))) := rfl

/-- The reduction of the dual numbers to `𝐅_ℓ`. -/
abbrev dualReduce : D →+* ZMod ℓ := (TrivSqZeroExt.fstHom (ZMod ℓ) (ZMod ℓ) (ZMod ℓ)).toRingHom

omit [IsTopologicalGroup π] in
/-- The reduction of `dualRep z` to `𝐅_ℓ` is `ρ₀`. -/
lemma dualRep_isConjugate (z : lcCocycles₁ (ZMod ℓ) π AD) :
    IsConjugate (fun g => Matrix.GeneralLinearGroup.map dualReduce (dualRep z g))
      (fun g => ρ₀ g) := by
  refine ⟨1, fun g => ?_⟩
  rw [one_mul, inv_one, mul_one]
  ext i j
  simp [dualReduce]

omit [IsTopologicalGroup π] in
/-- The determinant of `dualRep z` is `δ`, viewed in the dual numbers. -/
lemma det_dualRep (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (z : lcCocycles₁ (ZMod ℓ) π AD) (g : π) :
    Matrix.GeneralLinearGroup.det (dualRep z g) = Units.map (algebraMap ℤ_[ℓ] D) (δ g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_dualRep,
    det_dmat (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ))
      ((z.1 g).val * (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)))
      (((ρ₀ g)⁻¹ : Matrix.GeneralLinearGroup _ _) : Matrix (Fin n) (Fin n) (ZMod ℓ))
      (Units.mul_inv _)
      (by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, AdZero.trace_val])]
  have := congrArg Units.val (h.delta_reduce g)
  rw [Matrix.GeneralLinearGroup.val_det_apply] at this
  rw [Units.coe_map, MonoidHom.coe_coe, ← this]
  rfl

/-- If `a + ε b = a' + ε b'`, then `a = a'` and `b = b'`. -/
lemma dmat_injective {a b a' b' : Matrix (Fin n) (Fin n) (ZMod ℓ)} (h : dmat a b = dmat a' b') :
    a = a' ∧ b = b' := by
  refine ⟨Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · simpa using congrArg (fun X => (X i j).fst) h
  · simpa using congrArg (fun X => (X i j).snd) h

/-- The product of two dual numbers with zero real part is zero. -/
lemma mul_eq_zero_of_fst_eq_zero {u v : D} (hu : u.fst = 0) (hv : v.fst = 0) : u * v = 0 :=
  TrivSqZeroExt.ext (by simp [hu]) (by simp [hu, hv])

omit [IsTopologicalGroup π] in
/-- A `ℤ_[ℓ]`-algebra map from a universal deformation ring to the dual numbers kills the maximal
ideal modulo `ε`. -/
lemma fst_eq_zero_of_mem (_h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (ψ : R →ₐ[ℤ_[ℓ]] D) {b : R} (hb : b ∈ maximalIdeal R) : (ψ b).fst = 0 := by
  let f : R →+* ZMod ℓ := dualReduce.comp ψ.toRingHom
  have hf : Function.Surjective f := fun x => by
    obtain ⟨c, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := ℓ)) x
    refine ⟨algebraMap ℤ_[ℓ] R c, ?_⟩
    simp only [f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    rfl
  have hker := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hf)
  rwa [← hker] at hb

omit [IsTopologicalGroup π] in
/-- A `ℤ_[ℓ]`-algebra map from a universal deformation ring to the dual numbers reduces to the
reduction map. -/
lemma fst_comp_eq (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (ψ : R →ₐ[ℤ_[ℓ]] D) (a : R) : (ψ a).fst = reduce a := by
  obtain ⟨c, hc⟩ := h.surjective_mk_maximalIdeal_comp_algebraMap (Ideal.Quotient.mk _ a)
  simp only [RingHom.comp_apply, Ideal.Quotient.eq] at hc
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ maximalIdeal R, a = algebraMap ℤ_[ℓ] R c - b :=
    ⟨algebraMap ℤ_[ℓ] R c - a, hc, by ring⟩
  have hrb : reduce b = 0 := by
    rwa [← RingHom.mem_ker, h.ker_reduce]
  rw [map_sub, map_sub, TrivSqZeroExt.fst_sub, fst_eq_zero_of_mem h ψ hb, hrb, AlgHom.commutes,
    h.reduce_algebraMap]
  rfl

omit [IsTopologicalGroup π] in
/-- **An algebra map from the deformation ring to the dual numbers is determined by its values on
generators of the cotangent space.** -/
lemma algHom_ext_of_le (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    {d : ℕ} (y : Fin d → R) (hym : ∀ i, y i ∈ maximalIdeal R)
    (hy : maximalIdeal R ≤ Ideal.span (Set.range y) ⊔ maximalIdeal R ^ 2 ⊔
      Ideal.span {algebraMap ℤ_[ℓ] R ℓ})
    (ψ ψ' : R →ₐ[ℤ_[ℓ]] D) (hψ : ∀ i, ψ (y i) = ψ' (y i)) : ψ = ψ' := by
  have hdiff : ∀ a : R, (ψ a - ψ' a).fst = 0 := fun a => by
    rw [TrivSqZeroExt.fst_sub, fst_comp_eq h, fst_comp_eq h, sub_self]
  have hℓ : ∀ φ : R →ₐ[ℤ_[ℓ]] D, φ (algebraMap ℤ_[ℓ] R ℓ) = 0 := fun φ => by
    rw [AlgHom.commutes]
    show TrivSqZeroExt.inl (PadicInt.toZMod (ℓ : ℤ_[ℓ])) = 0
    simp
  have hsq : ∀ φ : R →ₐ[ℤ_[ℓ]] D, ∀ a ∈ maximalIdeal R ^ 2, φ a = 0 := by
    intro φ a ha
    rw [pow_two] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [map_mul]
      exact mul_eq_zero_of_fst_eq_zero (fst_eq_zero_of_mem h φ hx) (fst_eq_zero_of_mem h φ hy)
    · rw [map_add, hx, hy, add_zero]
  have hspan : Ideal.span (Set.range y) ≤ maximalIdeal R :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hym)
  have key : ∀ a ∈ Ideal.span (Set.range y) ⊔ maximalIdeal R ^ 2 ⊔
      Ideal.span {algebraMap ℤ_[ℓ] R ℓ}, ψ a = ψ' a := by
    intro a ha
    obtain ⟨a₁₂, h₁₂, a₃, h₃, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.mp h₁₂
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp h₃
    simp only [map_add, map_mul, hℓ, mul_zero, add_zero, hsq ψ a₂ h₂, hsq ψ' a₂ h₂]
    refine Submodule.span_induction (p := fun x _ => ψ x = ψ' x) ?_ (by simp) ?_ ?_ h₁
    · rintro _ ⟨i, rfl⟩
      exact hψ i
    · intro x x' _ _ hx hx'
      rw [map_add, map_add, hx, hx']
    · intro r x hx hxe
      rw [smul_eq_mul, map_mul, map_mul, ← hxe, ← sub_eq_zero, ← sub_mul]
      exact mul_eq_zero_of_fst_eq_zero (hdiff r) (fst_eq_zero_of_mem h ψ (hspan hx))
  refine AlgHom.ext fun a => ?_
  obtain ⟨c, hc⟩ := h.surjective_mk_maximalIdeal_comp_algebraMap (Ideal.Quotient.mk _ a)
  simp only [RingHom.comp_apply, Ideal.Quotient.eq] at hc
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ maximalIdeal R, a = algebraMap ℤ_[ℓ] R c - b :=
    ⟨algebraMap ℤ_[ℓ] R c - a, hc, by ring⟩
  rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, key b (hy hb)]

omit [IsTopologicalGroup π] in
/-- If `P` conjugates `dualRep z` to `dualRep z'` and `P = p + ε q`, then `p` commutes with `ρ₀`
and `ρ₀ q + z' ρ₀ p = p z ρ₀ + q ρ₀`. -/
private lemma dualRep_conj_dmat {z z' : lcCocycles₁ (ZMod ℓ) π AD}
    {P : Matrix.GeneralLinearGroup (Fin n) D}
    {p q : Matrix (Fin n) (Fin n) (ZMod ℓ)} (hP : ∀ g, dualRep z' g = P * dualRep z g * P⁻¹)
    (hPeq : (P : Matrix (Fin n) (Fin n) D) = dmat p q) (g : π) :
    (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * p = p * ρ₀ g ∧
      (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * q +
        (z'.1 g).val * (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) * p =
      p * ((z.1 g).val * (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ))) +
        q * (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) := by
  have h₁ : dualRep z' g * P = P * dualRep z g := by
    rw [hP g, mul_assoc, inv_mul_cancel, mul_one]
  have h₂ := congrArg (fun X : Matrix.GeneralLinearGroup (Fin n) D =>
    (X : Matrix (Fin n) (Fin n) D)) h₁
  simp only [Units.val_mul, coe_dualRep, hPeq, dmat_mul] at h₂
  exact dmat_injective h₂

omit [IsTopologicalGroup π] in
/-- **Conjugate first order deformations differ by a coboundary** (Schur's lemma). -/
lemma exists_dZero_eq_of_isConjugate (hirr : IsAbsolutelyIrreducible fun g => ρ₀ g)
    (hn : ¬ ℓ ∣ n) (z z' : lcCocycles₁ (ZMod ℓ) π AD)
    (hc : IsConjugate (fun g => dualRep z g) (fun g => dualRep z' g)) :
    ∃ m : AD, dZero m = z.1 - z'.1 := by
  classical
  obtain ⟨P, hP⟩ := hc
  set fstM : Matrix (Fin n) (Fin n) D →+* Matrix (Fin n) (Fin n) (ZMod ℓ) :=
    (dualReduce (ℓ := ℓ)).mapMatrix
  set p : Matrix (Fin n) (Fin n) (ZMod ℓ) := fstM P
  set q : Matrix (Fin n) (Fin n) (ZMod ℓ) := fun i j => ((P : Matrix (Fin n) (Fin n) D) i j).snd
  set p' : Matrix (Fin n) (Fin n) (ZMod ℓ) := fstM (P⁻¹ : Matrix.GeneralLinearGroup _ D)
  have hPeq : (P : Matrix (Fin n) (Fin n) D) = dmat p q := eq_dmat _
  have hpp' : p * p' = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hn' : (n : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hcomp := dualRep_conj_dmat (fun g => hP g) hPeq
  obtain ⟨c, hcp⟩ := Matrix.mem_range_scalar_of_commute_span_eq_top (ℓ := ℓ) (S := ZMod ℓ)
    (fun g => (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ))) hirr p (fun g => by
      have hid : ((ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ))).map (algebraMap (ZMod ℓ) (ZMod ℓ)) =
          (ρ₀ g : Matrix (Fin n) (Fin n) (ZMod ℓ)) := by ext; simp
      rw [hid]
      exact (hcomp g).1)
  have hpc : p = c • (1 : Matrix (Fin n) (Fin n) (ZMod ℓ)) := by
    rw [← hcp, Matrix.smul_one_eq_diagonal]
    rfl
  by_cases hc0 : c = 0
  · have h01 : (1 : Matrix (Fin n) (Fin n) (ZMod ℓ)) = 0 := by
      rw [← hpp', hpc, hc0, zero_smul, Matrix.zero_mul]
    have hsub : ∀ X : AD, X = 0 := fun X => by
      ext1
      rw [← Matrix.one_mul X.val, h01, Matrix.zero_mul, AdZero.val_zero]
    exact ⟨0, funext fun g => by
      rw [Pi.sub_apply, hsub (z.1 g), hsub (z'.1 g), sub_zero, dZero_apply, smul_zero,
        sub_zero]⟩
  set t : ZMod ℓ := q.trace / n
  have hq0 : (q - t • (1 : Matrix (Fin n) (Fin n) (ZMod ℓ))).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      div_mul_cancel₀ _ hn', sub_self]
  have hm0 : (c⁻¹ • (q - t • (1 : Matrix (Fin n) (Fin n) (ZMod ℓ)))).trace = 0 := by
    rw [Matrix.trace_smul, hq0, smul_zero]
  refine ⟨AdZero.mk _ hm0, funext fun g => ?_⟩
  ext1
  obtain ⟨-, h2⟩ := hcomp g
  set A : Matrix (Fin n) (Fin n) (ZMod ℓ) := Units.val (ρ₀ g)
  set Ai : Matrix (Fin n) (Fin n) (ZMod ℓ) := Units.val (ρ₀ g)⁻¹
  have hAAi : A * Ai = 1 := Units.mul_inv _
  rw [hpc] at h2
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h2
  show A * (c⁻¹ • (q - t • 1)) * Ai - c⁻¹ • (q - t • 1) = ((z.1 g).val - (z'.1 g).val)
  exact conj_sub_eq_of_mul_add_smul hAAi hc0 h2

omit [IsTopologicalGroup π] in
/-- **`H ¹(π, ad⁰)` is finite of dimension at most the number of generators of the cotangent
space.** Here `H ¹` is built from locally constant cochains, `ρ₀` is absolutely irreducible,
`ℓ ∤ n`, and `y₁, …, y_d ∈ 𝔪_R` generate `𝔪_R` modulo `𝔪_R² + ℓR`. -/
theorem finiteDimensional_lcH1_and_finrank_le
    (h : IsUniversalFixedDeterminantDeformation ℓ n π ρ₀ δ R reduce ρuniv)
    (hirr : IsAbsolutelyIrreducible fun g => ρ₀ g) (hn : ¬ ℓ ∣ n)
    {d : ℕ} (y : Fin d → R) (hym : ∀ i, y i ∈ maximalIdeal R)
    (hy : maximalIdeal R ≤ Ideal.span (Set.range y) ⊔ maximalIdeal R ^ 2 ⊔
      Ideal.span {algebraMap ℤ_[ℓ] R ℓ}) :
    FiniteDimensional (ZMod ℓ) (LcH1 (ZMod ℓ) π AD) ∧
      Module.finrank (ZMod ℓ) (LcH1 (ZMod ℓ) π AD) ≤ d := by
  classical
  have hcD : IsAdicComplete (maximalIdeal D) D :=
    isAdicComplete_of_pow_eq_bot _ maximalIdeal_dual_sq
  have hred : Function.Surjective (dualReduce (ℓ := ℓ)) := fun x =>
    ⟨TrivSqZeroExt.inl x, by simp [dualReduce]⟩
  choose ψ _ hψ using fun z : lcCocycles₁ (ZMod ℓ) π AD =>
    h.exists_of_small D rfl hcD dualReduce hred continuous_of_discreteTopology
      (fun a => rfl) (dualRep z) (dualRep_isConjugate z) (det_dualRep h z)
  let Φ : lcCocycles₁ (ZMod ℓ) π AD → Fin d → ZMod ℓ := fun z i => (ψ z (y i)).snd
  have key : ∀ z z', Φ z = Φ z' → ∃ m : AD, dZero m = z.1 - z'.1 := by
    intro z z' hΦ
    have hψeq : ψ z = ψ z' := algHom_ext_of_le h y hym hy _ _ fun i =>
      TrivSqZeroExt.ext (by rw [fst_comp_eq h, fst_comp_eq h]) (congrFun hΦ i)
    obtain ⟨P, hP⟩ := hψ z
    obtain ⟨Q, hQ⟩ := hψ z'
    refine exists_dZero_eq_of_isConjugate hirr hn z z' ⟨Q * P⁻¹, fun g => ?_⟩
    show dualRep z' g = Q * P⁻¹ * dualRep z g * (Q * P⁻¹)⁻¹
    rw [show dualRep z' g = _ from hQ g, show dualRep z g = _ from hP g, hψeq]
    group
  let out := Function.surjInv (LcH1.mk_surjective (ZMod ℓ) (K := π) (M := AD))
  let f : LcH1 (ZMod ℓ) π AD → Fin d → ZMod ℓ := fun v => Φ (out v)
  have hf : Function.Injective f := by
    intro v w hvw
    obtain ⟨m, hm⟩ := key _ _ hvw
    have h0 : LcH1.mk (ZMod ℓ) (K := π) (M := AD) (out v - out w) = 0 :=
      (LcH1.mk_eq_zero_iff (ZMod ℓ) _).mpr ⟨m, hm⟩
    rw [map_sub, sub_eq_zero] at h0
    have e1 := Function.surjInv_eq (LcH1.mk_surjective (ZMod ℓ) (K := π) (M := AD)) v
    have e2 := Function.surjInv_eq (LcH1.mk_surjective (ZMod ℓ) (K := π) (M := AD)) w
    rwa [← e1, ← e2]
  have : Finite (LcH1 (ZMod ℓ) π AD) := Finite.of_injective f hf
  have : FiniteDimensional (ZMod ℓ) (LcH1 (ZMod ℓ) π AD) := Module.Finite.of_finite
  refine ⟨inferInstance, ?_⟩
  let : Fintype (LcH1 (ZMod ℓ) π AD) := Fintype.ofFinite _
  have h1 := Fintype.card_le_of_injective f hf
  rw [Module.card_eq_pow_finrank (K := ZMod ℓ), Fintype.card_fun, Fintype.card_fin,
    ZMod.card] at h1
  exact (Nat.pow_le_pow_iff_right (Fact.out : ℓ.Prime).one_lt).mp h1

end IsUniversalFixedDeterminantDeformation

end Deformation
