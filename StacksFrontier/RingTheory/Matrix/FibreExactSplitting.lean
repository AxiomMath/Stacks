module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Splitting the cokernel of a matrix from the exactness of a fibre

Let `A` be a commutative ring, `p ⊂ A` a prime ideal and `D₂ : A^{n₂} → A^{n₁}`,
`D₁ : A^{n₁} → A^{n₀}` matrices (acting on row vectors) with `D₂ D₁ = 0`.  If the complex
`κ(p)^{n₂} → κ(p)^{n₁} → κ(p)^{n₀}` is exact in the middle, then on a principal open
neighbourhood `D(f)` of `p` the cokernel of `D₁` is free and split: there are matrices `q`, `s`,
`t` over `A_f` with `D₁ q = 0`, `s q = 1` and `q s + t D₁ = 1`.

## Main results

* `Matrix.exists_split_of_free_cokernel`: a free cokernel of a matrix is split.
* `Matrix.free_cokernel_of_fibre_exact`: over a local ring, exactness of the fibre makes the
  cokernel free.
* `Matrix.exists_away_split_of_fibre_exact`: the splitting on a principal open neighbourhood.
* `Matrix.exists_away_retract_of_idempotent`: an idempotent matrix splits on a principal open
  neighbourhood, so the direct summand it cuts out of a free module is free there.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
-/

@[expose] public section

open TensorProduct

universe u

namespace Matrix

variable {R : Type u} [CommRing R]

/-- The cokernel of a matrix acting on row vectors. -/
abbrev rowCokernel {n₁ n₀ : ℕ} (D : Matrix (Fin n₁) (Fin n₀) R) : Type u :=
  (Fin n₀ → R) ⧸ LinearMap.range D.vecMulLinear

/-- **A free cokernel of a matrix is split.**  If the cokernel of `D : R^{n₁} → R^{n₀}` is free,
there are matrices `q : R^{n₀} → R^r`, `s : R^r → R^{n₀}` and `t : R^{n₀} → R^{n₁}` with `D q = 0`,
`s q = 1` and `q s + t D = 1`. -/
theorem exists_split_of_free_cokernel {n₁ n₀ : ℕ} (D : Matrix (Fin n₁) (Fin n₀) R)
    [Module.Free R D.rowCokernel] :
    ∃ (r : ℕ) (q : Matrix (Fin n₀) (Fin r) R) (s : Matrix (Fin r) (Fin n₀) R)
      (t : Matrix (Fin n₀) (Fin n₁) R), D * q = 0 ∧ s * q = 1 ∧ q * s + t * D = 1 := by
  classical
  let W := D.rowCokernel
  let π : (Fin n₀ → R) →ₗ[R] W := Submodule.mkQ _
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have : Module.Finite R W := Module.Finite.of_surjective π hπ
  let b₀ := Module.Free.chooseBasis R W
  let r := Fintype.card (Module.Free.ChooseBasisIndex R W)
  let b : Module.Basis (Fin r) R W := b₀.reindex (Fintype.equivFin _)
  let Q : (Fin n₀ → R) →ₗ[R] (Fin r → R) := b.equivFun.toLinearMap ∘ₗ π
  choose x hx using fun j : Fin r => hπ (b j)
  let q : Matrix (Fin n₀) (Fin r) R := fun i => Q (Pi.single i 1)
  have hq : ∀ v, v ᵥ* q = Q v := by
    intro v
    have h : q.vecMulLinear = Q := by
      refine LinearMap.pi_ext fun i c => ?_
      rw [Matrix.vecMulLinear_apply, Matrix.single_vecMul]
      have : Pi.single i c = c • (Pi.single i 1 : Fin n₀ → R) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_smul]
      rfl
    exact congrArg (fun φ : (Fin n₀ → R) →ₗ[R] (Fin r → R) => φ v) h
  let s : Matrix (Fin r) (Fin n₀) R := fun j => x j
  have hs : ∀ w : Fin r → R, π (w ᵥ* s) = ∑ j, w j • b j := by
    intro w
    have h : w ᵥ* s = ∑ j, w j • x j := by
      have hw : w = ∑ j, w j • (Pi.single j 1 : Fin r → R) := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hw]
      rw [← Matrix.vecMulLinear_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]
      rfl
    rw [h, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hx]
  have hmem : ∀ i : Fin n₀, Pi.single i 1 - ((Pi.single i 1) ᵥ* q) ᵥ* s ∈
      LinearMap.range D.vecMulLinear := by
    intro i
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    change π _ = 0
    rw [map_sub, hq, hs]
    have := b.sum_equivFun (π (Pi.single i 1))
    change π (Pi.single i 1) - ∑ j, Q (Pi.single i 1) j • b j = 0
    rw [show (fun j => Q (Pi.single i 1) j • b j) = fun j => b.equivFun (π (Pi.single i 1)) j • b j
      from rfl, this, sub_self]
  choose y hy using hmem
  let t : Matrix (Fin n₀) (Fin n₁) R := fun i => y i
  refine ⟨r, q, s, t, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => congrFun (?_ : (D * q).row i = 0) j
    rw [← Matrix.single_one_vecMul, ← Matrix.vecMul_vecMul, hq]
    have : π (Pi.single i 1 ᵥ* D) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨Pi.single i 1, rfl⟩
    change b.equivFun (π _) = 0
    rw [this, map_zero]
  · refine Matrix.ext fun j k => congrFun
      (?_ : (s * q).row j = (1 : Matrix (Fin r) (Fin r) R).row j) k
    rw [← Matrix.single_one_vecMul, ← Matrix.single_one_vecMul, ← Matrix.vecMul_vecMul,
      Matrix.vecMul_one, Matrix.single_one_vecMul, hq]
    change b.equivFun (π (x j)) = _
    rw [hx]
    funext k
    rw [b.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  · refine Matrix.ext fun i k => congrFun (?_ : (q * s + t * D).row i =
      (1 : Matrix (Fin n₀) (Fin n₀) R).row i) k
    rw [← Matrix.single_one_vecMul, ← Matrix.single_one_vecMul, Matrix.vecMul_add,
      ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_one,
      Matrix.single_one_vecMul i t]
    have := hy i
    rw [Matrix.vecMulLinear_apply] at this
    change _ + y i ᵥ* D = _
    rw [this]
    abel

/-- Tensoring the map of a matrix on row vectors with an `R`-algebra `k` is the map of the image
matrix over `k`, read through `k ⊗ R^m ≅ k^m`. -/
theorem piScalarRight_lTensor_vecMulLinear {m n : ℕ} (k : Type*) [CommRing k] [Algebra R k]
    (D : Matrix (Fin m) (Fin n) R) (z : k ⊗[R] (Fin m → R)) :
    piScalarRight R k k (Fin n) ((D.vecMulLinear.lTensor k) z) =
      piScalarRight R k k (Fin m) z ᵥ* D.map (algebraMap R k) := by
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    funext j
    simp [Matrix.vecMul, dotProduct, piScalarRightHom_tmul, Algebra.smul_def, mul_comm,
      mul_left_comm, Finset.mul_sum]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.add_vecMul]

/-- **Over a local ring, exactness of the fibre makes the cokernel free.**  If `D₂ D₁ = 0` and
`k^{n₂} → k^{n₁} → k^{n₀}` is exact in the middle over the residue field `k`, then the cokernel
of `D₁` is free. -/
theorem free_rowCokernel_of_fibre_exact [IsLocalRing R] {n₂ n₁ n₀ : ℕ}
    (D₂ : Matrix (Fin n₂) (Fin n₁) R) (D₁ : Matrix (Fin n₁) (Fin n₀) R) (h : D₂ * D₁ = 0)
    (hfib : ∀ x : Fin n₁ → IsLocalRing.ResidueField R,
      x ᵥ* D₁.map (algebraMap R (IsLocalRing.ResidueField R)) = 0 →
        ∃ y, y ᵥ* D₂.map (algebraMap R (IsLocalRing.ResidueField R)) = x) :
    Module.Free R D₁.rowCokernel := by
  let k := IsLocalRing.ResidueField R
  let ι := (LinearMap.range D₁.vecMulLinear).subtype
  refine Module.free_of_lTensor_residueField_injective ι (Submodule.mkQ _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _) ?_
  have hρ := LinearMap.lTensor_surjective k D₁.vecMulLinear.surjective_rangeRestrict
  have hcomp : ι ∘ₗ D₁.vecMulLinear.rangeRestrict = D₁.vecMulLinear :=
    LinearMap.subtype_comp_codRestrict _ _ _
  have hzero : D₁.vecMulLinear.rangeRestrict ∘ₗ D₂.vecMulLinear = 0 := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    change (y ᵥ* D₂) ᵥ* D₁ = 0
    rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_zero]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨z, rfl⟩ := hρ w
  have hz : D₁.vecMulLinear.lTensor k z = 0 := by
    rw [← hcomp, LinearMap.lTensor_comp, LinearMap.comp_apply]; exact hw
  have hz' := congrArg (piScalarRight R k k (Fin n₀)) hz
  rw [piScalarRight_lTensor_vecMulLinear, map_zero] at hz'
  obtain ⟨y', hy'⟩ := hfib _ hz'
  have hy : D₂.vecMulLinear.lTensor k ((piScalarRight R k k (Fin n₂)).symm y') = z := by
    apply (piScalarRight R k k (Fin n₁)).injective
    rw [piScalarRight_lTensor_vecMulLinear, LinearEquiv.apply_symm_apply, hy']
  rw [← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

/-- A matrix whose entries vanish in a localization is killed by one element of the submonoid. -/
theorem exists_mem_smul_eq_zero_of_map_eq_zero {m n : Type*} [Finite m] [Finite n]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (X : Matrix m n R) (hX : X.map (algebraMap R S) = 0) :
    ∃ c ∈ M, c • X = 0 := by
  classical
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  have h : ∀ i j, ∃ c : M, (c : R) * X i j = 0 := fun i j =>
    (IsLocalization.map_eq_zero_iff M S (X i j)).mp (congrFun (congrFun hX i) j)
  choose c hc using h
  refine ⟨∏ i, ∏ j, (c i j : R), Submonoid.prod_mem _ fun i _ => Submonoid.prod_mem _
    fun j _ => (c i j).2, ?_⟩
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  calc (c i j : R) * (∏ x ∈ Finset.univ.erase j, (c i x : R)) *
          (∏ x ∈ Finset.univ.erase i, ∏ y, (c x y : R)) * X i j
      = ((∏ x ∈ Finset.univ.erase j, (c i x : R)) * (∏ x ∈ Finset.univ.erase i, ∏ y, (c x y : R)))
          * ((c i j : R) * X i j) := by ring
    _ = 0 := by rw [hc, mul_zero]

/-- A matrix killed by an element which becomes a unit along a ring map vanishes there. -/
theorem map_eq_zero_of_smul_eq_zero {m n : Type*} {S : Type*} [CommRing S] (φ : R →+* S)
    {c : R} (hc : IsUnit (φ c)) {X : Matrix m n R} (h : c • X = 0) : X.map φ = 0 := by
  ext i j
  have := congrArg φ (congrFun (congrFun h i) j)
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.zero_apply, map_zero] at this
  exact (hc.mul_right_eq_zero).mp this

/-- Mapping a matrix along `algebraMap` commutes with scalar multiplication by elements of the
base ring. -/
private theorem map_algebraMap_smul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {m n : Type*} (a : A) (X : Matrix m n A) :
    (a • X).map (algebraMap A B) = a • X.map (algebraMap A B) :=
  Matrix.map_smul _ _ (fun _ => by rw [smul_eq_mul, map_mul, Algebra.smul_def]) X

/-- **The cokernel of a matrix is free and split on a principal open neighbourhood of a prime at
which the fibre is exact.**  If `D₂ D₁ = 0` and `κ(p)^{n₂} → κ(p)^{n₁} → κ(p)^{n₀}` is exact in
the middle, there are `f ∉ p` and `r` such that over every `A`-algebra `B` in which `f` is a unit
there are matrices `q`, `s`, `t` with `D₁ q = 0`, `s q = 1` and `q s + t D₁ = 1`. -/
theorem exists_away_split_of_fibre_exact {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {n₂ n₁ n₀ : ℕ} (D₂ : Matrix (Fin n₂) (Fin n₁) A) (D₁ : Matrix (Fin n₁) (Fin n₀) A)
    (h : D₂ * D₁ = 0)
    (hfib : ∀ x : Fin n₁ → p.ResidueField, x ᵥ* D₁.map (algebraMap A p.ResidueField) = 0 →
      ∃ y, y ᵥ* D₂.map (algebraMap A p.ResidueField) = x) :
    ∃ f ∉ p, ∃ r : ℕ, ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B f) →
      ∃ (q : Matrix (Fin n₀) (Fin r) B) (s : Matrix (Fin r) (Fin n₀) B)
        (t : Matrix (Fin n₀) (Fin n₁) B), D₁.map (algebraMap A B) * q = 0 ∧ s * q = 1 ∧
          q * s + t * D₁.map (algebraMap A B) = 1 := by
  classical
  let Ap := Localization.AtPrime p
  let φ := algebraMap A Ap
  have hκ : ∀ {m n : ℕ} (D : Matrix (Fin m) (Fin n) A),
      (D.map φ).map (algebraMap Ap (IsLocalRing.ResidueField Ap)) =
        D.map (algebraMap A p.ResidueField) := by
    intro m n D
    rw [Matrix.map_map, IsScalarTower.algebraMap_eq A Ap p.ResidueField]
    rfl
  have hfree : Module.Free Ap (D₁.map φ).rowCokernel := by
    refine free_rowCokernel_of_fibre_exact (D₂.map φ) (D₁.map φ) ?_ ?_
    · rw [← Matrix.map_mul, h, Matrix.map_zero _ (map_zero φ)]
    · intro x hx
      rw [hκ] at hx
      obtain ⟨y, hy⟩ := hfib x hx
      exact ⟨y, by rw [hκ]; exact hy⟩
  obtain ⟨r, q, s, t, h₁, h₂, h₃⟩ := exists_split_of_free_cokernel (D₁.map φ)
  obtain ⟨bq, hbq⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl
    (fun ij : Fin n₀ × Fin r => q ij.1 ij.2)
  obtain ⟨bs, hbs⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl
    (fun ij : Fin r × Fin n₀ => s ij.1 ij.2)
  obtain ⟨bt, hbt⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl
    (fun ij : Fin n₀ × Fin n₁ => t ij.1 ij.2)
  choose q₀ hq₀ using hbq
  choose s₀ hs₀ using hbs
  choose t₀ ht₀ using hbt
  let Q₀ : Matrix (Fin n₀) (Fin r) A := fun i j => q₀ (i, j)
  let S₀ : Matrix (Fin r) (Fin n₀) A := fun i j => s₀ (i, j)
  let T₀ : Matrix (Fin n₀) (Fin n₁) A := fun i j => t₀ (i, j)
  have eQ : Q₀.map φ = (bq : A) • q := by ext i j; exact hq₀ (i, j)
  have eS : S₀.map φ = (bs : A) • s := by ext i j; exact hs₀ (i, j)
  have eT : T₀.map φ = (bt : A) • t := by ext i j; exact ht₀ (i, j)
  obtain ⟨c₁, hc₁, e₁⟩ := exists_mem_smul_eq_zero_of_map_eq_zero p.primeCompl Ap (D₁ * Q₀) (by
    rw [Matrix.map_mul, eQ, Matrix.mul_smul, h₁, smul_zero])
  obtain ⟨c₂, hc₂, e₂⟩ := exists_mem_smul_eq_zero_of_map_eq_zero p.primeCompl Ap
    (S₀ * Q₀ - ((bs : A) * bq) • 1) (by
      rw [Matrix.map_sub _ (map_sub φ), Matrix.map_mul, eS, eQ, map_algebraMap_smul,
        Matrix.smul_mul, Matrix.mul_smul, h₂, smul_smul, Matrix.map_one _ (map_zero φ) (map_one φ),
        sub_self])
  obtain ⟨c₃, hc₃, e₃⟩ := exists_mem_smul_eq_zero_of_map_eq_zero p.primeCompl Ap
    ((bt : A) • (Q₀ * S₀) + ((bq : A) * bs) • (T₀ * D₁) - ((bq : A) * bs * bt) • 1) (by
      rw [Matrix.map_sub _ (map_sub φ), Matrix.map_add _ (map_add φ), map_algebraMap_smul,
        map_algebraMap_smul, map_algebraMap_smul, Matrix.map_mul, Matrix.map_mul, eQ, eS, eT,
        Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, smul_smul, smul_smul,
        show (bt : A) * bq * bs = (bq : A) * bs * bt by ring, ← smul_add, h₃, sub_self])
  let f : A := (bq : A) * bs * bt * c₁ * c₂ * c₃
  have hf : f ∈ p.primeCompl := p.primeCompl.mul_mem (p.primeCompl.mul_mem
    (p.primeCompl.mul_mem (p.primeCompl.mul_mem (p.primeCompl.mul_mem bq.2 bs.2) bt.2) hc₁) hc₂) hc₃
  refine ⟨f, hf, r, fun B _ _ hfB => ?_⟩
  let ψ := algebraMap A B
  have hu : ∀ {a b : A}, IsUnit (ψ (a * b)) → IsUnit (ψ a) ∧ IsUnit (ψ b) := fun h => by
    rw [map_mul] at h
    exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩
  obtain ⟨h12345, uc₃⟩ := hu hfB
  obtain ⟨h1234, uc₂⟩ := hu h12345
  obtain ⟨h123, uc₁⟩ := hu h1234
  obtain ⟨h12, ut⟩ := hu h123
  obtain ⟨uq, us⟩ := hu h12
  have E₁ := map_eq_zero_of_smul_eq_zero ψ uc₁ e₁
  have E₂ := map_eq_zero_of_smul_eq_zero ψ uc₂ e₂
  have E₃ := map_eq_zero_of_smul_eq_zero ψ uc₃ e₃
  rw [Matrix.map_mul] at E₁
  rw [Matrix.map_sub _ (map_sub ψ), Matrix.map_mul, map_algebraMap_smul,
    Matrix.map_one _ (map_zero ψ) (map_one ψ), sub_eq_zero] at E₂
  rw [Matrix.map_sub _ (map_sub ψ), Matrix.map_add _ (map_add ψ), map_algebraMap_smul,
    map_algebraMap_smul, map_algebraMap_smul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_one _ (map_zero ψ) (map_one ψ), sub_eq_zero] at E₃
  refine ⟨(uq.unit⁻¹ : Bˣ) • Q₀.map ψ, (us.unit⁻¹ : Bˣ) • S₀.map ψ, (ut.unit⁻¹ : Bˣ) • T₀.map ψ,
    ?_, ?_, ?_⟩
  · rw [Matrix.mul_smul, E₁, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, E₂, smul_smul, ← algebraMap_smul B, Units.smul_def,
      smul_smul]
    convert one_smul B (1 : Matrix (Fin r) (Fin r) B)
    rw [Units.val_mul, map_mul]
    calc ((us.unit⁻¹ : Bˣ) : B) * ((uq.unit⁻¹ : Bˣ) : B) * (ψ bs * ψ bq)
        = (((us.unit⁻¹ : Bˣ) : B) * us.unit) * (((uq.unit⁻¹ : Bˣ) : B) * uq.unit) := by
          simp only [IsUnit.unit_spec]; ring
      _ = 1 := by simp
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [← algebraMap_smul B (bt : A), ← algebraMap_smul B ((bq : A) * bs),
      ← algebraMap_smul B ((bq : A) * bs * bt)] at E₃
    have iq := uq.val_inv_mul
    have is := us.val_inv_mul
    have it := ut.val_inv_mul
    let w : B := ((uq.unit⁻¹ : Bˣ) : B) * ((us.unit⁻¹ : Bˣ) : B) * ((ut.unit⁻¹ : Bˣ) : B)
    calc (uq.unit⁻¹ * us.unit⁻¹) • (Q₀.map ψ * S₀.map ψ) + ut.unit⁻¹ • (T₀.map ψ * D₁.map ψ)
        = w • (ψ bt • (Q₀.map ψ * S₀.map ψ) + ψ ((bq : A) * bs) • (T₀.map ψ * D₁.map ψ)) := by
          rw [smul_add, smul_smul, smul_smul, Units.smul_def, Units.smul_def]
          congr 2
          · simp only [w, Units.val_mul]
            linear_combination (-(((uq.unit⁻¹ : Bˣ) : B) * ((us.unit⁻¹ : Bˣ) : B))) * it
          · simp only [w, map_mul]
            linear_combination (-((ut.unit⁻¹ : Bˣ) : B) * ((us.unit⁻¹ : Bˣ) : B) * ψ bs) * iq -
              ((ut.unit⁻¹ : Bˣ) : B) * is
      _ = w • (ψ ((bq : A) * bs * bt) • (1 : Matrix (Fin n₀) (Fin n₀) B)) := by rw [E₃]
      _ = 1 := by
          rw [smul_smul]
          convert one_smul B (1 : Matrix (Fin n₀) (Fin n₀) B)
          simp only [w, map_mul]
          linear_combination ((uq.unit⁻¹ : Bˣ) : B) * ((us.unit⁻¹ : Bˣ) : B) * ψ bq * ψ bs * it +
            ((uq.unit⁻¹ : Bˣ) : B) * ψ bq * is + iq

/-- **Over a field, a row vector orthogonal to the kernel of a matrix is a combination of its
rows.** -/
theorem exists_vecMul_eq_of_forall_dotProduct_eq_zero {K : Type*} [Field K] {n₂ n₁ : ℕ}
    (D : Matrix (Fin n₂) (Fin n₁) K) (x : Fin n₁ → K)
    (h : ∀ l : Fin n₁ → K, D *ᵥ l = 0 → x ⬝ᵥ l = 0) : ∃ y, y ᵥ* D = x := by
  classical
  by_contra hne
  have hx : x ∉ LinearMap.range D.vecMulLinear := by
    rintro ⟨y, hy⟩
    exact hne ⟨y, hy⟩
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  let l : Fin n₁ → K := fun i => f (Pi.single i 1)
  have hfl : ∀ v, f v = v ⬝ᵥ l := by
    intro v
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin n₁ → K) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, dotProduct, l]
  have hDl : D *ᵥ l = 0 := by
    funext i
    have hmem : D i ∈ LinearMap.range D.vecMulLinear :=
      ⟨Pi.single i 1, by rw [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]; rfl⟩
    have : f (D i) = 0 := by
      have : f (D i) ∈ Submodule.map f (LinearMap.range D.vecMulLinear) := ⟨_, hmem, rfl⟩
      rw [hmap] at this
      exact (Submodule.mem_bot K).mp this
    rw [hfl] at this
    simpa [Matrix.mulVec, dotProduct_comm] using this
  exact hf (by rw [hfl]; exact h l hDl)

/-- **Exactness of the fibre at the kernel of a map to a field, from orthogonality of the kernels
over that field.**  If `φ : A → K` is a ring map to a field and every row vector killed by `D₁`
over `K` is orthogonal to every column vector killed by `D₂`, then the complex is exact in the
middle over the residue field of the prime `ker φ`. -/
theorem fibre_exact_of_forall_dotProduct_eq_zero {A K : Type*} [CommRing A] [Field K]
    (φ : A →+* K) [(RingHom.ker φ).IsPrime] {n₂ n₁ n₀ : ℕ} (D₂ : Matrix (Fin n₂) (Fin n₁) A)
    (D₁ : Matrix (Fin n₁) (Fin n₀) A)
    (horth : ∀ x l : Fin n₁ → K, x ᵥ* D₁.map φ = 0 → D₂.map φ *ᵥ l = 0 → x ⬝ᵥ l = 0) :
    ∀ x : Fin n₁ → (RingHom.ker φ).ResidueField,
      x ᵥ* D₁.map (algebraMap A (RingHom.ker φ).ResidueField) = 0 →
        ∃ y, y ᵥ* D₂.map (algebraMap A (RingHom.ker φ).ResidueField) = x := by
  classical
  let p := RingHom.ker φ
  let ψ : p.ResidueField →+* K := Ideal.ResidueField.lift p φ le_rfl (by
    intro a ha
    exact (isUnit_iff_ne_zero.mpr fun h => ha h))
  have hψ : ∀ a, ψ (algebraMap A p.ResidueField a) = φ a :=
    Ideal.ResidueField.lift_algebraMap _ _ _ _
  have hmap : ∀ {m n : ℕ} (D : Matrix (Fin m) (Fin n) A),
      (D.map (algebraMap A p.ResidueField)).map ψ = D.map φ := by
    intro m n D; ext i j; exact hψ _
  intro x hx
  refine exists_vecMul_eq_of_forall_dotProduct_eq_zero _ x fun l hl => ?_
  apply ψ.injective
  rw [map_zero]
  have h1 : (ψ ∘ x) ᵥ* D₁.map φ = 0 := by
    rw [← hmap]; funext i; rw [← RingHom.map_vecMul, hx]; simp
  have h2 : D₂.map φ *ᵥ (ψ ∘ l) = 0 := by
    rw [← hmap]; funext i; rw [← RingHom.map_mulVec, hl]; simp
  rw [← horth _ _ h1 h2, RingHom.map_dotProduct]


/-- **An idempotent matrix splits on a principal open neighbourhood of a prime.**  If `E` is an
idempotent square matrix over `A` and `p` a prime, there are `f ∉ p` and `r` such that over every
`A`-algebra `B` in which `f` is a unit there are matrices `a`, `b` with `b a = 1` and `a b = E`:
the image of `E` is free of rank `r` near `p`.  This is
`Matrix.exists_away_split_of_fibre_exact` for the complex `E`, `1 - E`, which is exact in the
middle on every fibre. -/
theorem exists_away_retract_of_idempotent {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {n : ℕ} (E : Matrix (Fin n) (Fin n) A) (hE : E * E = E) :
    ∃ f ∉ p, ∃ r : ℕ, ∀ (B : Type u) [CommRing B] [Algebra A B], IsUnit (algebraMap A B f) →
      ∃ (a : Matrix (Fin n) (Fin r) B) (b : Matrix (Fin r) (Fin n) B),
        b * a = 1 ∧ a * b = E.map (algebraMap A B) := by
  have h : E * (1 - E) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hE, sub_self]
  have hm : ∀ {B : Type u} [CommRing B] [Algebra A B],
      (1 - E).map (algebraMap A B) = 1 - E.map (algebraMap A B) := fun {B} _ _ => by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply]
  obtain ⟨f, hf, r, hB⟩ := exists_away_split_of_fibre_exact p E (1 - E) h (fun x hx => by
    refine ⟨x, ?_⟩
    rw [hm, Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hx
    exact hx.symm)
  refine ⟨f, hf, r, fun B _ _ hu => ?_⟩
  obtain ⟨q, s, t, h₁, h₂, h₃⟩ := hB B hu
  let E' := E.map (algebraMap A B)
  have hE' : E' * E' = E' := by rw [← Matrix.map_mul, hE]
  rw [hm] at h₁ h₃
  have hq : E' * q = q := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h₁
    exact h₁.symm
  refine ⟨q, s * E', ?_, ?_⟩
  · rw [Matrix.mul_assoc, hq, h₂]
  · calc q * (s * E') = (q * s + t * (1 - E')) * E' := by
          rw [Matrix.add_mul, Matrix.mul_assoc t, Matrix.sub_mul, Matrix.one_mul, hE', sub_self,
            Matrix.mul_zero, add_zero, Matrix.mul_assoc]
      _ = E' := by rw [h₃, Matrix.one_mul]

end Matrix

end
