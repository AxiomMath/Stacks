module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs

/-!
# The content lemma: non-zero-divisors of `C ⊗[k] A` are detected on fibres

Let `k` be a field, `C` and `A` commutative `k`-algebras and `β ∈ C ⊗[k] A`.  If for every
maximal ideal `m` of `A` the image of `β` in `C ⊗[k] A/m` is a non-zero-divisor, then `β` is a
non-zero-divisor of `C ⊗[k] A` (Perrin's thesis, I §3; McCoy's theorem is the case `C = k[X]`).
No finiteness or noetherian hypothesis is needed on `C` or `A`.

## Main results

* `Matrix.exists_det_submatrix_ne_zero`: a matrix over a field acting injectively on `L → K`,
  `L` finite, has a nonzero `L × L` minor.
* `TensorProduct.mem_nonZeroDivisors_of_forall_quotient`,
  `TensorProduct.mem_nonZeroDivisors_of_forall_residueField`: the content lemma.
* `TensorProduct.mem_nonZeroDivisors_of_forall_not_isNilpotent`: the form with "every zero divisor
  of every fibre is nilpotent" and "the image of `β` in no fibre is nilpotent".
* `TensorProduct.mem_nonZeroDivisors_of_forall_residueField_ne_zero`: for `C` geometrically
  integral (e.g. a domain over an algebraically closed field), nonzero images suffice.

## Implementation notes

Fix a `k`-basis `(c_i)` of `C`; then `C ⊗[k] M ≅ ι →₀ M` naturally in `M`
(`TensorProduct.ContentNonZeroDivisor.coord`), and multiplication by `β` on `C ⊗[k] A` is the
column-finite matrix `mulMatrix C β` over `A`, whose image along `A → K` is the matrix of the
image of `β`.  If `γ β = 0` with `γ ≠ 0`, let `L` be the (finite) support of `γ`.  At a maximal
ideal `m` the image of `β` in `C ⊗[k] κ(m)` acts injectively, so the columns `L` of its matrix
are independent and some `L × L` minor `δ` of `mulMatrix C β` survives in `κ(m)`, i.e. `δ ∉ m`;
by Cramer's rule `δ` annihilates every coordinate of `γ`.  So the annihilator of `γ` lies in no
maximal ideal, whence `γ = 0`.
-/

@[expose] public section

open scoped TensorProduct

universe u

/-- **Cramer's rule, annihilation form**: if `M` kills `v`, then `M.det` annihilates `v`. -/
theorem Matrix.det_smul_eq_zero_of_mulVec_eq_zero {α n : Type*} [CommRing α] [Fintype n]
    [DecidableEq n] {M : Matrix n n α} {v : n → α} (h : M.mulVec v = 0) : M.det • v = 0 := by
  simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using
    congrArg (Matrix.mulVec M.adjugate) h

/-- **A matrix over a field acting injectively on `L → K` has rows spanning `L → K`.** -/
theorem Matrix.span_range_eq_top_of_mulVec_eq_zero {K ι L : Type*} [Field K] [Fintype L]
    (N : Matrix ι L K) (h : ∀ v : L → K, (∀ i, ∑ l, N i l * v l = 0) → v = 0) :
    Submodule.span K (Set.range N) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
    inferInstance
  let v : L → K := fun l => f (Pi.single l 1)
  have hfv : ∀ x : L → K, f x = ∑ l, x l * v l := fun x => by
    conv_lhs => rw [show x = ∑ l, x l • (Pi.single l 1 : L → K) from
      funext fun j => by simp [Finset.sum_apply, Pi.single_apply]]
    simp only [map_sum, map_smul, smul_eq_mul, v]
  have hv : v = 0 := h v fun i => by
    rw [← hfv, ← Submodule.mem_bot K, ← hf]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
  exact hf0 (LinearMap.ext fun x => by simp [hfv, hv])

/-- **A matrix over a field with injective action on `L → K` has a nonzero maximal minor**:
some choice of `|L|` rows gives a square submatrix with nonzero determinant. -/
theorem Matrix.exists_det_submatrix_ne_zero {K ι L : Type*} [Field K] [Fintype L] [DecidableEq L]
    (N : Matrix ι L K) (h : ∀ v : L → K, (∀ i, ∑ l, N i l * v l = 0) → v = 0) :
    ∃ e : L → ι, (N.submatrix e id).det ≠ 0 := by
  classical
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent K (Set.range N)
  let B := Module.Basis.mk hbli (by
    rw [Subtype.range_coe, hbspan, Matrix.span_range_eq_top_of_mulVec_eq_zero N h])
  have : Finite b := Module.Finite.finite_basis B
  have := Fintype.ofFinite b
  let eqv : L ≃ b := Fintype.equivOfCardEq (by
    rw [← Module.finrank_fintype_fun_eq_card K, Module.finrank_eq_card_basis B])
  choose e he using fun l => hbS (eqv l).2
  have hli : LinearIndependent K (fun l => (N.submatrix e id) l) := by
    rw [show (fun l => (N.submatrix e id) l) = fun l => ((eqv l : b) : L → K) from
      funext fun l => funext fun l' => by simp [Matrix.submatrix, he]]
    exact hbli.comp eqv eqv.injective
  exact ⟨e, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero⟩

namespace TensorProduct.ContentNonZeroDivisor

variable {k C : Type*} [Field k] [CommRing C] [Algebra k C]

variable (k C) in
/-- The index type of the chosen `k`-basis of `C`. -/
abbrev ι := Module.Basis.ofVectorSpaceIndex k C

variable (k C) in
/-- The chosen `k`-basis of `C`. -/
noncomputable abbrev bC : Module.Basis (ι k C) k C := Module.Basis.ofVectorSpace k C

variable (C) in
/-- Coordinates of `C ⊗[k] M` in the chosen basis of `C`. -/
noncomputable def coord (M : Type*) [AddCommGroup M] [Module k M] :
    C ⊗[k] M ≃ₗ[k] ι k C →₀ M := by
  classical exact TensorProduct.congr (bC k C).repr (LinearEquiv.refl k M) ≪≫ₗ
    TensorProduct.finsuppScalarLeft k M (ι k C)

variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The coordinates of a pure tensor. -/
lemma coord_tmul (c : C) (m : M) (i : ι k C) :
    coord C M (c ⊗ₜ m) i = (bC k C).repr c i • m := by
  simp [coord]

/-- The coordinates of a basis vector tensor `m`. -/
lemma coord_basis_tmul (j : ι k C) (m : M) :
    coord C M ((bC k C) j ⊗ₜ m) = Finsupp.single j m := by
  classical
  ext i
  rw [coord_tmul, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- An element of `C ⊗[k] M` is the sum of basis vectors tensored with its coordinates. -/
lemma eq_sum_coord (t : C ⊗[k] M) :
    t = (coord C M t).sum fun i m => (bC k C) i ⊗ₜ m := by
  refine (coord C M).injective ?_
  simp_rw [map_finsuppSum, coord_basis_tmul]
  exact (Finsupp.sum_single _).symm

/-- Coordinates are natural in `M`. -/
lemma coord_lTensor (g : M →ₗ[k] N) (t : C ⊗[k] M) (i : ι k C) :
    coord C N (g.lTensor C t) i = g (coord C M t i) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul c m => simp [coord_tmul]
  | add s t hs ht => simp [hs, ht]

variable {A A' : Type*} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']

/-- Multiplication by `1 ⊗ a` multiplies every coordinate by `a`. -/
lemma coord_one_tmul_mul (a : A) (t : C ⊗[k] A) (i : ι k C) :
    coord C A ((1 ⊗ₜ a) * t) i = a * coord C A t i := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul c a' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, coord_tmul, coord_tmul, mul_smul_comm]
  | add s t hs ht => simp [mul_add, hs, ht]

/-- Coordinates commute with base change along a `k`-algebra map `A → A'`. -/
lemma coord_map (g : A →ₐ[k] A') (t : C ⊗[k] A) (i : ι k C) :
    coord C A' (Algebra.TensorProduct.map (AlgHom.id k C) g t) i = g (coord C A t i) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul c a => simp [coord_tmul]
  | add s t hs ht => simp [hs, ht]

variable (C) in
/-- The matrix of multiplication by `β` in the chosen basis of `C`. -/
noncomputable def mulMatrix (β : C ⊗[k] A) : Matrix (ι k C) (ι k C) A :=
  fun i l => coord C A (β * ((bC k C) l ⊗ₜ 1)) i

/-- The coordinates of `β γ` are those of `γ` multiplied by the matrix of `β`. -/
lemma coord_mul (β γ : C ⊗[k] A) (i : ι k C) :
    coord C A (β * γ) i = (coord C A γ).sum fun l a => mulMatrix C β i l * a := by
  conv_lhs => rw [eq_sum_coord γ]
  rw [Finsupp.mul_sum, map_finsuppSum, Finsupp.sum_apply]
  refine Finsupp.sum_congr fun l _ => ?_
  rw [show (bC k C) l ⊗ₜ[k] coord C A γ l = (1 ⊗ₜ coord C A γ l) * ((bC k C) l ⊗ₜ 1) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one],
    mul_left_comm, coord_one_tmul_mul, mulMatrix, mul_comm]

/-- The matrix of the image of `β` is the image of the matrix of `β`. -/
lemma mulMatrix_map (g : A →ₐ[k] A') (β : C ⊗[k] A) (i l : ι k C) :
    mulMatrix C (Algebra.TensorProduct.map (AlgHom.id k C) g β) i l = g (mulMatrix C β i l) := by
  have : Algebra.TensorProduct.map (AlgHom.id k C) g β * ((bC k C) l ⊗ₜ 1) =
      Algebra.TensorProduct.map (AlgHom.id k C) g (β * ((bC k C) l ⊗ₜ 1)) := by
    rw [map_mul, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  rw [mulMatrix, mulMatrix, this, coord_map]

variable {K : Type*} [Field K] [Algebra k K]

/-- The coordinates of `∑_{l ∈ L} c_l ⊗ v_l` on `L`. -/
lemma coord_sum_basis_tmul {L : Finset (ι k C)} (v : L → K) (l : L) :
    coord C K (∑ l' : L, (bC k C) l' ⊗ₜ[k] v l') (l : ι k C) = v l := by
  classical
  rw [map_sum, Finsupp.finsetSum_apply]
  simp_rw [coord_basis_tmul, Finsupp.single_apply]
  rw [Finset.sum_eq_single l (fun l' _ hl' => ite_eq_right fun h => hl' (Subtype.ext h)) (by simp)]
  simp

/-- The coordinates of `∑_{l ∈ L} c_l ⊗ v_l` off `L` vanish. -/
lemma coord_sum_basis_tmul_of_notMem {L : Finset (ι k C)} (v : L → K) (i : ι k C) (hi : i ∉ L) :
    coord C K (∑ l' : L, (bC k C) l' ⊗ₜ[k] v l') i = 0 := by
  classical
  rw [map_sum, Finsupp.finsetSum_apply]
  simp_rw [coord_basis_tmul, Finsupp.single_apply]
  exact Finset.sum_eq_zero fun l' _ => ite_eq_right fun h : (l' : ι k C) = i => hi (h ▸ l'.2)

/-- **The reduced matrix of a non-zero-divisor acts injectively.**  If the image of `β` in
`C ⊗[k] K` along a `k`-algebra map `g : A → K` to a field is a non-zero-divisor, then the matrix
of `β` reduced along `g` kills no nonzero family of coordinates indexed by a finite set `L`. -/
lemma eq_zero_of_sum_mulMatrix_eq_zero (β : C ⊗[k] A) (g : A →ₐ[k] K)
    (h : Algebra.TensorProduct.map (AlgHom.id k C) g β ∈ nonZeroDivisors (C ⊗[k] K))
    {L : Finset (ι k C)} (v : L → K)
    (hv : ∀ i, ∑ l : L, g (mulMatrix C β i (l : ι k C)) * v l = 0) :
    v = 0 := by
  classical
  have hsupp : (coord C K (∑ l' : L, (bC k C) l' ⊗ₜ[k] v l')).support ⊆ L := fun i hi =>
    not_not.mp fun hiL => Finsupp.mem_support_iff.mp hi (coord_sum_basis_tmul_of_notMem v i hiL)
  have hz : (∑ l' : L, (bC k C) l' ⊗ₜ[k] v l') = 0 := by
    refine mem_nonZeroDivisors_iff_right.mp h _ ?_
    rw [mul_comm]
    refine (coord C K).injective ?_
    ext i
    rw [coord_mul, map_zero, Finsupp.zero_apply,
      Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => mul_zero _), ← Finset.sum_coe_sort L]
    refine (Finset.sum_congr rfl fun l _ => ?_).trans (hv i)
    exact congrArg₂ (· * ·) (mulMatrix_map g β i l) (coord_sum_basis_tmul v l)
  funext l
  rw [← coord_sum_basis_tmul v l, hz, map_zero, Finsupp.zero_apply, Pi.zero_apply]

/-- **The local step of the content lemma.**  If `γ β = 0` in `C ⊗[k] A` and the image of `β`
in `C ⊗[k] K`, along a `k`-algebra map `g : A → K` to a field killing an ideal `m`, is a
non-zero-divisor, then some element outside `m` annihilates every coordinate of `γ`: a maximal
minor of the matrix of `β` on the support of `γ` that survives in `K` (Cramer's rule). -/
lemma exists_not_mem_mul_coord_eq_zero (β γ : C ⊗[k] A) (hβγ : γ * β = 0) (m : Ideal A)
    (g : A →ₐ[k] K) (hg : ∀ a ∈ m, g a = 0)
    (h : Algebra.TensorProduct.map (AlgHom.id k C) g β ∈ nonZeroDivisors (C ⊗[k] K)) :
    ∃ δ ∉ m, ∀ l, δ * coord C A γ l = 0 := by
  classical
  let x := coord C A γ
  let L := x.support
  let N : Matrix (ι k C) L K := fun i l => g (mulMatrix C β i l)
  obtain ⟨e, he⟩ := Matrix.exists_det_submatrix_ne_zero N (eq_zero_of_sum_mulMatrix_eq_zero β g h)
  let Msub : Matrix L L A := fun l' l => mulMatrix C β (e l') l
  refine ⟨Msub.det, fun hδ => he ?_, ?_⟩
  · rw [show N.submatrix e id = (g : A →+* K).mapMatrix Msub from Matrix.ext fun _ _ => rfl,
      ← RingHom.map_det]
    exact hg _ hδ
  · have hw : Msub.mulVec (fun l : L => x l) = 0 := by
      funext l'
      have h0 : coord C A (β * γ) (e l') = 0 := by
        rw [mul_comm, hβγ, map_zero, Finsupp.zero_apply]
      rwa [coord_mul, Finsupp.sum, ← Finset.sum_coe_sort] at h0
    intro l
    by_cases hl : l ∈ L
    · exact congrFun (Matrix.det_smul_eq_zero_of_mulVec_eq_zero hw) ⟨l, hl⟩
    · rw [Finsupp.notMem_support_iff.mp hl, mul_zero]

end TensorProduct.ContentNonZeroDivisor

namespace TensorProduct

open ContentNonZeroDivisor

variable {k C A : Type*} [Field k] [CommRing C] [Algebra k C] [CommRing A] [Algebra k A]

/-- The content lemma, from the local step at every maximal ideal. -/
theorem mem_nonZeroDivisors_of_forall_isMaximal (β : C ⊗[k] A)
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (K : Type*) (_ : Field K) (_ : Algebra k K)
      (g : A →ₐ[k] K), (∀ a ∈ m, g a = 0) ∧
        Algebra.TensorProduct.map (AlgHom.id k C) g β ∈ nonZeroDivisors (C ⊗[k] K)) :
    β ∈ nonZeroDivisors (C ⊗[k] A) := by
  classical
  rw [mem_nonZeroDivisors_iff_right]
  intro γ hγ
  by_contra hne
  let x := coord C A γ
  have hx : x ≠ 0 := fun h0 => hne ((coord C A).injective (h0.trans (map_zero _).symm))
  let I : Ideal A := (Submodule.span A {x}).annihilator
  have hI : I ≠ ⊤ := fun htop => hx (by
    simpa [I, Submodule.mem_annihilator_span_singleton] using (Ideal.eq_top_iff_one I).mp htop)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨K, _, _, g, hg, hβ⟩ := h m hm
  obtain ⟨δ, hδ, hδx⟩ := exists_not_mem_mul_coord_eq_zero β γ hγ m g hg hβ
  exact hδ (hIm ((Submodule.mem_annihilator_span_singleton x δ).mpr
    (Finsupp.ext fun l => by simpa using hδx l)))

/-- **Content lemma** ([Perrin, I 3]; the algebraic input of the stabiliser construction).  Let
`C` and `A` be algebras over a field `k` and `β ∈ C ⊗[k] A`.  If for every maximal ideal `m` of
`A` the image of `β` in `C ⊗[k] A/m` is a non-zero-divisor, then `β` is a non-zero-divisor.
No finiteness or noetherian hypothesis is needed: in the coordinates given by a `k`-basis of
`C`, a maximal minor of `β` on the support of a would-be annihilated element survives modulo
every maximal ideal and annihilates that element (Cramer's rule). -/
theorem mem_nonZeroDivisors_of_forall_quotient (β : C ⊗[k] A)
    (h : ∀ m : Ideal A, m.IsMaximal →
      Algebra.TensorProduct.map (AlgHom.id k C) (Ideal.Quotient.mkₐ k m) β ∈
        nonZeroDivisors (C ⊗[k] (A ⧸ m))) :
    β ∈ nonZeroDivisors (C ⊗[k] A) :=
  mem_nonZeroDivisors_of_forall_isMaximal β fun m hm =>
    ⟨A ⧸ m, Ideal.Quotient.field m, inferInstance, Ideal.Quotient.mkₐ k m,
      fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha, h m hm⟩

/-- **Content lemma, residue field form**: if for every point `p` of `Spec A` the image of `β` in
`C ⊗[k] κ(p)` is a non-zero-divisor, then `β` is a non-zero-divisor of `C ⊗[k] A` (only the
closed points are used). -/
theorem mem_nonZeroDivisors_of_forall_residueField (β : C ⊗[k] A)
    (h : ∀ p : PrimeSpectrum A,
      Algebra.TensorProduct.map (AlgHom.id k C) (IsScalarTower.toAlgHom k A p.asIdeal.ResidueField)
        β ∈ nonZeroDivisors (C ⊗[k] p.asIdeal.ResidueField)) :
    β ∈ nonZeroDivisors (C ⊗[k] A) :=
  mem_nonZeroDivisors_of_forall_isMaximal β fun m hm =>
    ⟨m.ResidueField, inferInstance, inferInstance, IsScalarTower.toAlgHom k A m.ResidueField,
      fun a ha => by
        show algebraMap A m.ResidueField a = 0
        rwa [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField],
      h ⟨m, hm.isPrime⟩⟩

/-- **Content lemma, nilpotent form** (Perrin): if in every fibre `C ⊗[k] κ(p)` every zero
divisor is nilpotent, and the image of `β` in every fibre is not nilpotent, then `β` is a
non-zero-divisor of `C ⊗[k] A`. -/
theorem mem_nonZeroDivisors_of_forall_not_isNilpotent (β : C ⊗[k] A)
    (hC : ∀ p : PrimeSpectrum A, ∀ z : C ⊗[k] p.asIdeal.ResidueField,
      z ∉ nonZeroDivisors (C ⊗[k] p.asIdeal.ResidueField) → IsNilpotent z)
    (h : ∀ p : PrimeSpectrum A, ¬ IsNilpotent
      (Algebra.TensorProduct.map (AlgHom.id k C) (IsScalarTower.toAlgHom k A p.asIdeal.ResidueField)
        β)) :
    β ∈ nonZeroDivisors (C ⊗[k] A) :=
  mem_nonZeroDivisors_of_forall_residueField β fun p =>
    not_not.mp fun hz => h p (hC p _ hz)

/-- **Content lemma, integral form**: if `C` is geometrically integral over `k` (for instance a
domain over an algebraically closed field) and the image of `β` in `C ⊗[k] κ(p)` is nonzero for
every point `p` of `Spec A`, then `β` is a non-zero-divisor of `C ⊗[k] A`. -/
theorem mem_nonZeroDivisors_of_forall_residueField_ne_zero {k C A : Type u} [Field k] [CommRing C]
    [Algebra k C] [CommRing A] [Algebra k A] [Algebra.IsGeometricallyIntegral k C]
    (β : C ⊗[k] A)
    (h : ∀ p : PrimeSpectrum A,
      Algebra.TensorProduct.map (AlgHom.id k C) (IsScalarTower.toAlgHom k A p.asIdeal.ResidueField)
        β ≠ 0) :
    β ∈ nonZeroDivisors (C ⊗[k] A) :=
  mem_nonZeroDivisors_of_forall_residueField β fun p =>
    have := (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct k C).mp
      inferInstance p.asIdeal.ResidueField
    mem_nonZeroDivisors_of_ne_zero (h p)

end TensorProduct
