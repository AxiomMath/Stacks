module

public import StacksFrontier.RingTheory.Rig.Algebraization.NormalBundleOfRel

/-!
# The quasi-idempotent variety and its normal bundle data

Fix `N, c : ℕ` and let `F = (F_{ij})` be the generic `N × N` matrix, whose `N²` entries are the
variables of `A[F] = A[x₁, …, x_{N²}]` (the variable `x_{(i,j)}` is indexed by
`finProdFinEquiv (i, j)`). The *quasi-idempotent variety* is cut out by the `N²` entries of

  `G = F² − aᶜ F`,

and its completion `Q = A⟨F⟩ / (G)` is an object of the category of Stacks 0AL4 over `(A, (a))`.
This file builds the normal bundle data `Rig.NormalBundle.Data` of `Q` for its tautological
presentation, via `Rig.NormalBundle.Data.ofRel`, with exponent `2c` and an explicit matrix `S`.

## The relation

Write `⟨Y, G⟩ = ∑_{ij} Y_{ij} G_{ij}` and `F' = Fᵀ`. Then `∂G_{ij}/∂F_{pq}` is the
`(p, q)`-entry of `Λ(e_{ij})`, where `Λ(Y) = Y F' + F' Y − aᶜ Y`, and the matrix
`S_{(ij),(pq)} = δ_{ip} F_{jq} + F_{pi} δ_{qj} − aᶜ δ_{ip} δ_{qj}` encodes `σ(Z) = ⟨Λ(Z), G⟩`.
The identity

  `Λ²(Y) − a^{2c} Y = 2 (Y Gᵀ + Gᵀ Y) − (ad_{F'}(F' Y) − ad_{F'}(Y F'))`

together with `⟨ad_{F'}(Z), G⟩ = ⟨Z, F G − G F⟩ = 0` shows
`⟨Λ²(Y), G⟩ − a^{2c} ⟨Y, G⟩ = 2 ⟨Y Gᵀ + Gᵀ Y, G⟩ ∈ (G)²`, which is the relation required by
`Data.ofRel` with exponent `2c`. Everything is proved over an arbitrary commutative ring and then
specialised to the polynomial ring `A[F]` and mapped to its completion.

## Main definitions

* `Rig.NormalBundle.QuasiIdempotent.fPoly`, `SPoly`, `jacPoly`, `EtPoly`: the polynomial families
  `G`, `S`, `∂G` and the lift `Ẽ`.
* `Rig.NormalBundle.QuasiIdempotent.Qobj`: the completed quasi-idempotent variety.
* `Rig.NormalBundle.QuasiIdempotent.Qpres`: its tautological presentation.
* `Rig.NormalBundle.QuasiIdempotent.qdata`: its normal bundle data.

## Main results

* `Rig.NormalBundle.QuasiIdempotent.qdata_f`, `qdata_S`, `qdata_Et`: the generators, the matrix
  `S` and the lift `Ẽ` of `qdata` are images of the polynomial families `fPoly`, `SPoly`, `EtPoly`.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped Matrix

universe u

namespace Rig

namespace NormalBundle

namespace QuasiIdempotent

section MatrixAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pairing `⟨Y, G⟩ = ∑_{ij} Y_{ij} G_{ij} = tr(Yᵀ G)`. -/
def pairing (Y G : Matrix ι ι R) : R := (Yᵀ * G).trace

omit [DecidableEq ι] in
/-- `⟨Y, G⟩` is the sum of the entrywise products `Y_{ij} G_{ij}`. -/
theorem pairing_eq_sum (Y G : Matrix ι ι R) :
    pairing Y G = ∑ l : ι × ι, Y l.1 l.2 * G l.1 l.2 := by
  simp only [pairing, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [DecidableEq ι] in
/-- The pairing is additive in its first argument: `⟨Y − Y', G⟩ = ⟨Y, G⟩ − ⟨Y', G⟩`. -/
theorem pairing_sub_left (Y Y' G : Matrix ι ι R) :
    pairing (Y - Y') G = pairing Y G - pairing Y' G := by
  rw [pairing, pairing, pairing, Matrix.transpose_sub, Matrix.sub_mul, Matrix.trace_sub]

omit [DecidableEq ι] in
/-- `⟨Mᵀ Z, G⟩ = ⟨Z, M G⟩`. -/
theorem pairing_transpose_mul (M Z G : Matrix ι ι R) : pairing (Mᵀ * Z) G = pairing Z (M * G) := by
  rw [pairing, pairing, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- `⟨Z Mᵀ, G⟩ = ⟨Z, G M⟩`. -/
theorem pairing_mul_transpose (M Z G : Matrix ι ι R) : pairing (Z * Mᵀ) G = pairing Z (G * M) := by
  rw [pairing, pairing, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- If the entries of `Y` and of `G` lie in `K`, then `⟨Y, G⟩ ∈ K²`. -/
theorem pairing_mem_sq {K : Ideal R} {Y G : Matrix ι ι R} (hY : ∀ i j, Y i j ∈ K)
    (hG : ∀ i j, G i j ∈ K) : pairing Y G ∈ K ^ 2 := by
  rw [pairing_eq_sum, pow_two]
  exact Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_mul (hY _ _) (hG _ _)

/-- The linear map `Λ(Y) = Y Fᵀ + Fᵀ Y − u Y`, the differential of `⟨Y, F² − u F⟩` in `F`. -/
def lam (F : Matrix ι ι R) (u : R) (Y : Matrix ι ι R) : Matrix ι ι R :=
  Y * Fᵀ + Fᵀ * Y - u • Y

omit [DecidableEq ι] in
/-- **The key identity**: `Λ²(Y) − u² Y = 2 (Y Gᵀ + Gᵀ Y) − (ad_{F'}(F' Y) − ad_{F'}(Y F'))` with
`G = F² − u F` and `F' = Fᵀ`. -/
theorem lam_lam (F : Matrix ι ι R) (u : R) (Y : Matrix ι ι R) :
    lam F u (lam F u Y) - u ^ 2 • Y =
      2 • (Y * (quasiDefect u F)ᵀ + (quasiDefect u F)ᵀ * Y) -
        ((Fᵀ * (Fᵀ * Y) - Fᵀ * Y * Fᵀ) - (Fᵀ * (Y * Fᵀ) - Y * Fᵀ * Fᵀ)) := by
  rw [quasiDefect, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_smul]
  simp only [lam, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_sub, smul_add, smul_smul]
  module

omit [DecidableEq ι] in
/-- `F` commutes with `F² − u F`. -/
theorem mul_quasiDefect_comm (F : Matrix ι ι R) (u : R) :
    F * quasiDefect u F = quasiDefect u F * F := by
  rw [quasiDefect, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- `⟨ad_{Fᵀ}(Z), F² − u F⟩ = 0`. -/
theorem pairing_ad (F : Matrix ι ι R) (u : R) (Z : Matrix ι ι R) :
    pairing (Fᵀ * Z - Z * Fᵀ) (quasiDefect u F) = 0 := by
  rw [pairing_sub_left, pairing_transpose_mul, pairing_mul_transpose, mul_quasiDefect_comm,
    sub_self]

omit [DecidableEq ι] in
/-- **The relation, in matrix form**: `⟨Λ²(Y) − u² Y, G⟩ ∈ K²` whenever the entries of
`G = F² − u F` lie in `K`. -/
theorem pairing_lam_lam_mem {K : Ideal R} {F : Matrix ι ι R} {u : R}
    (hG : ∀ i j, quasiDefect u F i j ∈ K) (Y : Matrix ι ι R) :
    pairing (lam F u (lam F u Y) - u ^ 2 • Y) (quasiDefect u F) ∈ K ^ 2 := by
  rw [lam_lam, pairing_sub_left, pairing_sub_left, pairing_ad, pairing_ad, sub_zero, sub_zero]
  refine pairing_mem_sq (fun i j ↦ ?_) hG
  rw [Matrix.smul_apply, Matrix.add_apply]
  exact Submodule.smul_of_tower_mem _ _ (K.add_mem
    (Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_left _ _ (hG _ _))
    (Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_right _ _ (hG _ _)))

/-- The matrix `S_{(ij),(pq)} = δ_{ip} F_{jq} + F_{pi} δ_{qj} − u δ_{ip} δ_{qj}` of
`Z ↦ Λ(Z)`. -/
def smat (F : Matrix ι ι R) (u : R) : Matrix (ι × ι) (ι × ι) R := fun l v ↦
  (1 : Matrix ι ι R) l.1 v.1 * F l.2 v.2 + F v.1 l.1 * (1 : Matrix ι ι R) v.2 l.2 -
    u * ((1 : Matrix ι ι R) l.1 v.1 * (1 : Matrix ι ι R) v.2 l.2)

/-- The matrix `J_{(pq),(ij)} = δ_{pi} F_{qj} + F_{ip} δ_{qj} − u δ_{pi} δ_{qj}` of partial
derivatives `∂G_{ij}/∂F_{pq}` of `G = F² − u F`. -/
def jmat (F : Matrix ι ι R) (u : R) : Matrix (ι × ι) (ι × ι) R := fun v l ↦
  (1 : Matrix ι ι R) v.1 l.1 * F v.2 l.2 + F l.1 v.1 * (1 : Matrix ι ι R) v.2 l.2 -
    u * ((1 : Matrix ι ι R) v.1 l.1 * (1 : Matrix ι ι R) v.2 l.2)

/-- `S` is the matrix of `Λ`: `∑_{pq} S_{(ij),(pq)} Z_{pq} = Λ(Z)_{ij}`. -/
theorem sum_smat_mul (F : Matrix ι ι R) (u : R) (Z : Matrix ι ι R) (l : ι × ι) :
    ∑ v, smat F u l v * Z v.1 v.2 = lam F u Z l.1 l.2 := by
  simp only [smat, lam, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul, Fintype.sum_prod_type, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, mul_ite, one_mul,
    zero_mul, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_comm]

/-- The columns of `J` are the images `Λ(e_{ij})` of the matrix units. -/
theorem jmat_eq (F : Matrix ι ι R) (u : R) (v l : ι × ι) :
    jmat F u v l = lam F u (Matrix.single l.1 l.2 1) v.1 v.2 := by
  simp only [jmat, lam, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul, Matrix.single_apply, Matrix.one_apply, ite_and, ite_mul,
    mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  split_ifs <;> simp_all

/-- **The relation, in coordinates**: for every `l₀`,
`∑_l (∑_v S_{lv} J_{vl₀} − δ_{ll₀} u²) G_l ∈ K²`. -/
theorem sum_smat_jmat_mem {K : Ideal R} {F : Matrix ι ι R} {u : R}
    (hG : ∀ i j, quasiDefect u F i j ∈ K) (l₀ : ι × ι) :
    ∑ l, (∑ v, smat F u l v * jmat F u v l₀ -
      (1 : Matrix (ι × ι) (ι × ι) R) l l₀ * u ^ 2) * quasiDefect u F l.1 l.2 ∈ K ^ 2 := by
  have h := pairing_lam_lam_mem hG (Matrix.single l₀.1 l₀.2 1)
  rw [pairing_eq_sum] at h
  convert h using 1
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  simp only [jmat_eq, sum_smat_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [Matrix.one_apply, Matrix.single_apply]
  by_cases h : l = l₀
  · subst h; simp
  · have h' : ¬(l₀.1 = l.1 ∧ l₀.2 = l.2) := fun h' ↦ h (Prod.ext h'.1.symm h'.2.symm)
    rw [if_neg h, if_neg h', zero_mul, mul_zero]

end MatrixAlgebra

section Polynomial

variable (A : Type u) [CommRing A]

/-- The generic `N × N` matrix `F_{ij} = x_{(i,j)}` over `A[x₁, …, x_{N²}]`, the variable
`x_{(i,j)}` being indexed by `finProdFinEquiv (i, j)`. -/
def Fpoly (N : ℕ) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin (N * N)) A) :=
  Matrix.of fun i j ↦ X (finProdFinEquiv (i, j))

variable {A} (a : A) (N c : ℕ)

/-- The matrix `G = F² − aᶜ F` of equations of the quasi-idempotent variety. -/
def Gpoly : Matrix (Fin N) (Fin N) (MvPolynomial (Fin (N * N)) A) :=
  quasiDefect (C (a ^ c)) (Fpoly A N)

/-- The equations `G_{ij}` of the quasi-idempotent variety, indexed by `Fin (N * N)`:
`fPoly (finProdFinEquiv (i, j)) = G_{ij}`. -/
def fPoly (l : Fin (N * N)) : MvPolynomial (Fin (N * N)) A :=
  Gpoly a N c (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2

/-- The matrix `S_{(ij),(pq)} = δ_{ip} F_{jq} + F_{pi} δ_{qj} − aᶜ δ_{ip} δ_{qj}`, indexed by
`Fin (N * N)`. -/
def SPoly : Matrix (Fin (N * N)) (Fin (N * N)) (MvPolynomial (Fin (N * N)) A) :=
  fun l v ↦ smat (Fpoly A N) (C (a ^ c)) (finProdFinEquiv.symm l) (finProdFinEquiv.symm v)

/-- The Jacobian matrix `(∂G_l/∂x_v)_{vl}` of the equations. -/
def jacPoly : Matrix (Fin (N * N)) (Fin (N * N)) (MvPolynomial (Fin (N * N)) A) :=
  fun v l ↦ pderiv v (fPoly a N c l)

/-- The ideal `(G)` of `A[x₁, …, x_{N²}]`. -/
def KPoly : Ideal (MvPolynomial (Fin (N * N)) A) := Ideal.span (Set.range (fPoly a N c))

/-- The lift `Ẽ` of the normal bundle data, as a matrix of polynomials: the improved lift of
`E₀ = (Jac · S)ᵀ` for `u = a^{2c}`. -/
def EtPoly : Matrix (Fin (N * N)) (Fin (N * N)) (MvPolynomial (Fin (N * N)) A) :=
  improvedLift (C (a ^ (2 * c))) (jacPoly a N c * SPoly a N c)ᵀ

/-- `fPoly (finProdFinEquiv (i, j)) = G_{ij}`. -/
theorem fPoly_apply (w : Fin N × Fin N) :
    fPoly a N c (finProdFinEquiv w) = Gpoly a N c w.1 w.2 := by
  rw [fPoly, Equiv.symm_apply_apply]

/-- `∂F_{ij}/∂x_v = δ_{pi} δ_{qj}` for `v = finProdFinEquiv (p, q)`. -/
theorem pderiv_Fpoly (v : Fin (N * N)) (i j : Fin N) :
    pderiv v (Fpoly A N i j) =
      (1 : Matrix (Fin N) (Fin N) (MvPolynomial (Fin (N * N)) A)) (finProdFinEquiv.symm v).1 i *
        (1 : Matrix (Fin N) (Fin N) (MvPolynomial (Fin (N * N)) A))
          (finProdFinEquiv.symm v).2 j := by
  obtain ⟨⟨p, q⟩, rfl⟩ := finProdFinEquiv.surjective v
  rw [Equiv.symm_apply_apply]
  simp only [Fpoly, Matrix.of_apply, pderiv_X, Pi.single_apply, finProdFinEquiv.injective.eq_iff,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hi : p = i <;> by_cases hj : q = j
  · subst hi hj; simp
  · simp [hi, hj, Ne.symm hj]
  · simp [hi, hj, Ne.symm hi]
  · simp [hi, hj, Ne.symm hi, Ne.symm hj]

/-- The Jacobian of the equations is the matrix `jmat`. -/
theorem jacPoly_eq (v l : Fin (N * N)) :
    jacPoly a N c v l =
      jmat (Fpoly A N) (C (a ^ c)) (finProdFinEquiv.symm v) (finProdFinEquiv.symm l) := by
  rw [jacPoly, fPoly, Gpoly, quasiDefect, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
    smul_eq_mul, map_sub, map_sum, pderiv_C_mul]
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_Fpoly, jmat]
  generalize finProdFinEquiv.symm v = w
  generalize finProdFinEquiv.symm l = w'
  simp only [Finset.sum_add_distrib, Matrix.one_apply, mul_ite, ite_mul, one_mul, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  split_ifs <;> ring

/-- Every entry `G_{ij}` lies in the ideal `(G)`. -/
theorem Gpoly_mem (i j : Fin N) : Gpoly a N c i j ∈ KPoly a N c := by
  rw [← fPoly_apply a N c (i, j)]
  exact Ideal.subset_span ⟨_, rfl⟩

/-- **The relation for the quasi-idempotent variety, on polynomials**:
`∑_l ((S · Jac)_{lj} − δ_{lj} a^{2c}) G_l ∈ (G)²`. -/
theorem relPoly (j : Fin (N * N)) :
    ∑ l, ((SPoly a N c * jacPoly a N c) l j -
      (1 : Matrix (Fin (N * N)) (Fin (N * N)) (MvPolynomial (Fin (N * N)) A)) l j *
        C (a ^ (2 * c))) * fPoly a N c l ∈ KPoly a N c ^ 2 := by
  have h := sum_smat_jmat_mem (K := KPoly a N c) (Gpoly_mem a N c) (finProdFinEquiv.symm j)
  rw [← finProdFinEquiv.sum_comp]
  convert h using 1
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [fPoly_apply, Gpoly, Matrix.mul_apply, ← finProdFinEquiv.sum_comp]
  simp only [SPoly, jacPoly_eq, Equiv.symm_apply_apply]
  congr 2
  rw [pow_mul', map_pow]
  simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq_symm_apply]

end Polynomial

section Completed

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (a : A) (N c : ℕ)

/-- The ideal `(G)` of the completed polynomial algebra `A⟨x₁, …, x_{N²}⟩`. -/
def ideal : Ideal (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) :=
  Ideal.span (Set.range fun l ↦ algebraMap (MvPolynomial (Fin (N * N)) A)
    (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) (fPoly a N c l))

/-- **The completed quasi-idempotent variety** `A⟨F⟩ / (F² − aᶜ F)`, as an object of the
category of Stacks 0AL4 over `(A, (a))`. -/
def Qobj : AdicFiniteTypeAlgebra.{u, u} A (Ideal.span {a}) :=
  PerturbedPresentation.quotientObj A (Ideal.span {a}) (N * N) (ideal a N c)

/-- The tautological presentation of the completed quasi-idempotent variety. -/
abbrev Qpres : CompletedPolynomialPresentation (Ideal.span {a}) (Qobj a N c) where
  variableCount := N * N
  ideal := ideal a N c
  quotientEquiv := AlgEquiv.refl

omit [IsNoetherianRing A] in
/-- The image of `x ∈ A` in `A⟨x₁, …, x_{N²}⟩` is the image of the constant polynomial `C x`. -/
theorem algebraMap_eq_algebraMap_C (x : A) :
    algebraMap A (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) x =
      algebraMap (MvPolynomial (Fin (N * N)) A)
        (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) (C x) := by
  rw [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin (N * N)) A), MvPolynomial.algebraMap_eq]

omit [IsNoetherianRing A] in
/-- The image of the ideal `(G)` of `A[x₁, …, x_{N²}]` in `A⟨x₁, …, x_{N²}⟩` is contained in
`ideal a N c`, the ideal generated by the images of the `G_{ij}`. -/
theorem map_KPoly_le :
    (KPoly a N c).map (algebraMap (MvPolynomial (Fin (N * N)) A)
      (completedPolynomialAlgebra (Ideal.span {a}) (N * N))) ≤ ideal a N c := by
  rw [KPoly, Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro _ ⟨l, rfl⟩
  exact Ideal.subset_span ⟨l, rfl⟩

/-- The Jacobian of the images of the equations is the image of their Jacobian. -/
theorem jacobian_eq :
    jacobian (Qobj a N c) (Qpres a N c) (fun l ↦ algebraMap (MvPolynomial (Fin (N * N)) A)
      (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) (fPoly a N c l)) =
      (jacPoly a N c).map (algebraMap (MvPolynomial (Fin (N * N)) A)
        (completedPolynomialAlgebra (Ideal.span {a}) (N * N))) := by
  refine Matrix.ext fun v l ↦ ?_
  exact (completedNaiveCotangentComplex (Qobj a N c) (Qpres a N c)).partialDeriv_polynomial v _

/-- **The relation for the quasi-idempotent variety**: `∑_l ((S · Jac)_{lj} − δ_{lj} a^{2c}) [G_l]`
vanishes in `J / J²`. -/
theorem rel (j : Fin (N * N)) :
    ∑ l, (((SPoly a N c).map (algebraMap (MvPolynomial (Fin (N * N)) A)
        (completedPolynomialAlgebra (Ideal.span {a}) (N * N))) *
      jacobian (Qobj a N c) (Qpres a N c) (fun l ↦ algebraMap (MvPolynomial (Fin (N * N)) A)
        (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) (fPoly a N c l))) l j -
      (1 : Matrix (Fin (N * N)) (Fin (N * N)) (Qpres a N c).completedPolynomialRing) l j *
        algebraMap A (Qpres a N c).completedPolynomialRing (a ^ (2 * c))) *
      algebraMap (MvPolynomial (Fin (N * N)) A)
        (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) (fPoly a N c l) ∈
      (Qpres a N c).ideal ^ 2 := by
  set ι := algebraMap (MvPolynomial (Fin (N * N)) A)
    (completedPolynomialAlgebra (Ideal.span {a}) (N * N))
  have hx := Ideal.mem_map_of_mem ι (relPoly a N c j)
  rw [Ideal.map_pow] at hx
  refine Ideal.pow_right_mono (map_KPoly_le a N c) 2 ?_
  convert hx using 1
  rw [jacobian_eq, ← Matrix.map_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have h1 : (1 : Matrix (Fin (N * N)) (Fin (N * N)) (Qpres a N c).completedPolynomialRing) l j =
      ι ((1 : Matrix (Fin (N * N)) (Fin (N * N)) (MvPolynomial (Fin (N * N)) A)) l j) := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (map_one ι).symm
    · exact (map_zero ι).symm
  rw [map_mul, map_sub, map_mul, Matrix.map_apply, h1, algebraMap_eq_algebraMap_C]

/-- **The normal bundle data of the completed quasi-idempotent variety**, built by
`Rig.NormalBundle.Data.ofRel` from the equations `G_{ij}`, the exponent `2c` and the matrix
`S`. -/
def qdata : Data (Qobj a N c) (Qpres a N c) :=
  Data.ofRel (Qobj a N c) (Qpres a N c) (fun l ↦ algebraMap (MvPolynomial (Fin (N * N)) A)
    (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) (fPoly a N c l)) rfl (2 * c)
    ((SPoly a N c).map (algebraMap (MvPolynomial (Fin (N * N)) A)
      (completedPolynomialAlgebra (Ideal.span {a}) (N * N)))) (rel a N c)

/-- The field `m` of `qdata`, its number of generators, is `N²`. -/
@[simp] theorem qdata_m : (qdata a N c).m = N * N := rfl

/-- The field `c` of `qdata` is `3 · 2c`. -/
@[simp] theorem qdata_c : (qdata a N c).c = 3 * (2 * c) := rfl

/-- The generators of `qdata` are the images of the polynomials `fPoly`. -/
theorem qdata_f (l : Fin (N * N)) :
    (qdata a N c).f l = algebraMap (MvPolynomial (Fin (N * N)) A)
      (completedPolynomialAlgebra (Ideal.span {a}) (N * N)) (fPoly a N c l) := rfl

/-- The matrix `S` of `qdata` is the image of the polynomial matrix `a^{4c} SPoly`. -/
theorem qdata_S :
    (qdata a N c).S = ((C (a ^ (2 * (2 * c))) : MvPolynomial (Fin (N * N)) A) • SPoly a N c).map
      (algebraMap (MvPolynomial (Fin (N * N)) A)
        (completedPolynomialAlgebra (Ideal.span {a}) (N * N))) := by
  refine (Data.ofRel_S (Qobj a N c) (Qpres a N c) _ rfl (2 * c) _ (rel a N c)).trans ?_
  rw [Matrix.map_smul' _ _ _ (map_mul _), algebraMap_eq_algebraMap_C]

/-- The lift `Ẽ` of `qdata` is the image of the polynomial matrix `EtPoly`. -/
theorem qdata_Et :
    (qdata a N c).Et = (EtPoly a N c).map (algebraMap (MvPolynomial (Fin (N * N)) A)
      (completedPolynomialAlgebra (Ideal.span {a}) (N * N))) := by
  refine (Data.ofRel_Et (Qobj a N c) (Qpres a N c) _ rfl (2 * c) _ (rel a N c)).trans ?_
  rw [jacobian_eq, ← Matrix.map_mul, ← Matrix.transpose_map, EtPoly,
    improvedLift_map, algebraMap_eq_algebraMap_C]

end Completed

end QuasiIdempotent

end NormalBundle

end Rig

end
