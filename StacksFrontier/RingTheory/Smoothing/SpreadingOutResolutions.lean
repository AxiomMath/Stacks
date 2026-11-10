module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import StacksFrontier.RingTheory.FormallySmooth.Retract
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smoothing.LocalSmoothingSituation
public import StacksFrontier.RingTheory.Smoothing.StandardSmoothPresentation

/-!
# Spreading out a resolution from a minimal singular prime

Let `R → A → Λ ⊃ q` be a local smoothing situation and `p = R ∩ q`. If the localized chain
`R_p → A_p → Λ_q ⊃ q Λ_q` can be resolved, then already before localizing there is a
factorization `A → C → Λ` with `C` of finite presentation over `R` and `H_{C/R} Λ ⊄ q`.

The proof spreads out a resolution. A resolution of the localized chain may be replaced by a
standard smooth `R_p`-algebra `D`, presented as `R_p[x_1, …, x_n]/(f_1, …, f_c)` in such a way
that the images of generators of `A` are among the `x_i`. Clearing denominators puts the `f_j`
in `R[x_1, …, x_n]`, at the cost of one element `s ∈ R ∖ p` which also clears the relations of
`A`. The coordinates of the `R_p`-point of `D` in `Λ_q` are fractions `λ_i / t` with
`t ∉ q`, so homogenizing the `f_j` in one extra variable and multiplying by one further
element `λ_0 ∉ q` gives relations that hold in `Λ` on the nose. The ring

`C = A[x_0, …, x_{n + 1}]/(x_0 F_j(x_1, …, x_{n + 1}), x_0 (x_i - a_i x_{n + 1}))`

then maps to `Λ`, and inverting `b = x_0 x_{n + 1} s · F(jacobian)` makes it a retract of a
smooth `R`-algebra, so `b` lies in the singular ideal of `C` while its image avoids `q`.

## Main results

* `Stacks.Smoothing.exists_finitePresentation_factorization_singularIdeal_not_le`: the lemma
  above, Stacks 07F9.
* `Stacks.Smoothing.isStandardSmoothRingMap_of_isStandardSmooth`: Mathlib's
  `Algebra.IsStandardSmooth` gives a standard smooth presentation in the explicit form used by
  `Stacks.Smoothing.standardSmooth_presentation_with_prescribed_generators`.
* `Stacks.Smoothing.smooth_localization_away_jacobianDet`: inverting the Jacobian determinant of
  a presentation with `c ≤ n` relations produces a smooth algebra.

## Implementation notes

The minimality of `q` over `𝔥_A` is carried as a hypothesis, because the source assumes it, but
it is not used: the construction only needs a resolution of the localized chain. So the statement
proved here is formally stronger than the source's.

The smooth model is produced by `Stacks.Smoothing.exists_smooth_model` together with its
universal property, which is what lets the retraction `V → C_b` be built without unfolding the
three localizations it is assembled from.

## References

* [Swan, *Néron–Popescu desingularization*, Lemma 12.2][swan]
* [Popescu, *General Néron desingularization*, Lemma 2][popescu-GND]
* [Stacks Project, Tag 07F9](https://stacks.math.columbia.edu/tag/07F9)
-/

@[expose] public section

namespace Stacks.Smoothing

open MvPolynomial

universe u v w

/-! ### Clearing denominators -/

/-- A finite family of elements of `R` that die in a localization `T` is annihilated by a single
element of the localizing submonoid. -/
private theorem exists_mem_forall_mul_eq_zero {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (M : Submonoid R) [IsLocalization M T] {ι : Type*} [Finite ι] (x : ι → R)
    (hx : ∀ i, algebraMap R T (x i) = 0) : ∃ s ∈ M, ∀ i, s * x i = 0 := by
  classical
  cases nonempty_fintype ι
  choose d hd using fun i => (IsLocalization.map_eq_zero_iff M T (x i)).1 (hx i)
  refine ⟨((∏ i, d i : M) : R), (∏ i, d i : M).2, fun i => ?_⟩
  have hfactor : ((∏ j, d j : M) : R) =
      (d i : R) * ∏ j ∈ Finset.univ.erase i, (d j : R) := by
    simpa using
      (Finset.mul_prod_erase (Finset.univ : Finset ι) (fun j => (d j : R))
        (Finset.mem_univ i)).symm
  rw [hfactor, mul_right_comm, hd i, zero_mul]

/-- A finite family of elements of a localization `T` of `R` becomes integral after multiplying
by a single element of the localizing submonoid. -/
private theorem exists_mem_forall_mul_eq_map {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (M : Submonoid R) [IsLocalization M T] {ι : Type*} [Finite ι] (x : ι → T) :
    ∃ s ∈ M, ∃ y : ι → R, ∀ i, x i * algebraMap R T s = algebraMap R T (y i) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M (S := T) x
  have hb' : ∀ i, ∃ z : R, algebraMap R T z = (b : R) • x i :=
    fun i => RingHom.mem_rangeS.mp (hb i)
  choose y hy using hb'
  exact ⟨(b : R), b.2, y, fun i => by rw [hy i, Algebra.smul_def, mul_comm]⟩

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- A finite family of polynomials over a localization `Rp` of `R` becomes a family of
polynomials over `R` after multiplying by a single element of the localizing submonoid. -/
private theorem exists_mem_forall_mul_C_eq_map {R Rp : Type*} [CommRing R] [CommRing Rp]
    [Algebra R Rp] (M : Submonoid R) [IsLocalization M Rp] {ι σ : Type*} [Finite ι]
    (f : ι → MvPolynomial σ Rp) :
    ∃ s ∈ M, ∃ g : ι → MvPolynomial σ R,
      ∀ i, f i * C (algebraMap R Rp s) = MvPolynomial.map (algebraMap R Rp) (g i) := by
  obtain ⟨sC, hs, y, hy⟩ := exists_mem_forall_mul_eq_map
    (M.map (C (σ := σ) : R →+* MvPolynomial σ R)) (T := MvPolynomial σ Rp) f
  obtain ⟨s₀, hs₀, hs₀eq⟩ := hs
  refine ⟨s₀, hs₀, y, fun i => ?_⟩
  have h := hy i
  rwa [← hs₀eq, MvPolynomial.algebraMap_def, MvPolynomial.map_C] at h

/-- If a polynomial over `R` lies in the ideal generated by a finite family `f` after passing to
a localization `Rp`, then some element of the localizing submonoid times it is already a
combination of the `f`. -/
private theorem exists_mem_and_C_mul_eq_sum {R Rp : Type*} [CommRing R] [CommRing Rp]
    [Algebra R Rp] (M : Submonoid R) [IsLocalization M Rp] {ι σ : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ R) (p : MvPolynomial σ R)
    (hp : MvPolynomial.map (algebraMap R Rp) p ∈
      Ideal.span (Set.range fun j => MvPolynomial.map (algebraMap R Rp) (f j))) :
    ∃ s ∈ M, ∃ g : ι → MvPolynomial σ R, (∑ j, g j * f j) = C s * p := by
  classical
  obtain ⟨α, hα⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  obtain ⟨d, hd, b, hb⟩ := exists_mem_forall_mul_C_eq_map (R := R) (Rp := Rp) M α
  have hmapW : MvPolynomial.map (algebraMap R Rp)
      ((∑ j, b j * f j) - C d * p) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_mul, MvPolynomial.map_C]
    have hsum : (∑ j, MvPolynomial.map (algebraMap R Rp) (b j) *
        MvPolynomial.map (algebraMap R Rp) (f j)) =
        ∑ j, (α j * C (algebraMap R Rp d)) *
          MvPolynomial.map (algebraMap R Rp) (f j) :=
      Finset.sum_congr rfl fun j _ => by rw [hb j]
    rw [hsum]
    calc
      (∑ j, (α j * C (algebraMap R Rp d)) * MvPolynomial.map (algebraMap R Rp) (f j)) -
            C (algebraMap R Rp d) * MvPolynomial.map (algebraMap R Rp) p =
          C (algebraMap R Rp d) * (∑ j, α j * MvPolynomial.map (algebraMap R Rp) (f j)) -
            C (algebraMap R Rp d) * MvPolynomial.map (algebraMap R Rp) p := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [hα]; ring
  have hcoeffzero : ∀ r : {r : R // r ∈ ((∑ j, b j * f j) - C d * p).coeffs},
      algebraMap R Rp r.val = 0 := by
    intro r
    obtain ⟨m, hm, hr⟩ := MvPolynomial.mem_coeffs_iff.mp r.property
    have hcoeff := congrArg (fun z : MvPolynomial σ Rp => z.coeff m) hmapW
    rw [hr]
    simpa only [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      using hcoeff
  obtain ⟨e, he, hecoeff⟩ := exists_mem_forall_mul_eq_zero (R := R) (T := Rp) M _ hcoeffzero
  have hW : C e * ((∑ j, b j * f j) - C d * p) = 0 := by
    ext m
    rw [MvPolynomial.coeff_C_mul]
    by_cases hm : ((∑ j, b j * f j) - C d * p).coeff m = 0
    · rw [hm, mul_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · simpa using hecoeff ⟨_, MvPolynomial.coeff_mem_coeffs m hm⟩
  refine ⟨e * d, M.mul_mem he hd, fun j => C e * b j, ?_⟩
  calc
    (∑ j, (C e * b j) * f j) = C e * (∑ j, b j * f j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = C e * (C d * p) := sub_eq_zero.mp (by rwa [← mul_sub])
    _ = C (e * d) * p := by rw [MvPolynomial.C_mul]; ring

/-! ### Homogenization in one extra variable -/

/-- The homogenization of `f ∈ R[x_1, …, x_n]` in one extra variable: the unique polynomial
`F ∈ R[x_1, …, x_{n + 1}]`, homogeneous of degree `deg f`, with
`F(x_1, …, x_n, 1) = f(x_1, …, x_n)`. -/
private noncomputable def homogenizeLast {R : Type*} [CommRing R] {n : ℕ}
    (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  ∑ m ∈ f.support,
    monomial (m.mapDomain Fin.castSucc +
      Finsupp.single (Fin.last n) (f.totalDegree - m.sum fun _ e => e)) (f.coeff m)

/-- Evaluating the homogenization at `(t · v_1, …, t · v_n, t)` gives `t ^ deg f` times the
value of `f` at `v`. -/
private theorem aeval_homogenizeLast {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (f : MvPolynomial (Fin n) R) (v : Fin n → S) (t : S) :
    aeval (Fin.snoc (fun i => t * v i) t) (homogenizeLast f) =
      t ^ f.totalDegree * aeval v f := by
  classical
  simp only [homogenizeLast, aeval_sum]
  have hEval : aeval v f = ∑ i ∈ f.support, aeval v (monomial i (f.coeff i)) := by
    calc
      aeval v f = aeval v (∑ i ∈ f.support, monomial i (f.coeff i)) :=
        congrArg (aeval v) f.as_sum
      _ = ∑ i ∈ f.support, aeval v (monomial i (f.coeff i)) := map_sum _ _ _
  rw [hEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hle : (m.sum fun _ e => e) ≤ f.totalDegree := MvPolynomial.le_totalDegree hm
  rw [Finsupp.prod_add_index' (by intro a; rw [pow_zero]) (by intro a b₁ b₂; rw [pow_add]),
    Finsupp.prod_mapDomain_index_inj (f := Fin.castSucc) (Fin.castSucc_injective n)]
  have hprod : m.prod (fun i e => (t * v i) ^ e) =
      t ^ (m.sum fun _ e => e) * m.prod (fun i e => v i ^ e) := by
    rw [show (fun i e => (t * v i) ^ e) = (fun i e => t ^ e * v i ^ e) by
        funext i e; rw [mul_pow],
      Finsupp.prod_mul, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum]
    simp [Finsupp.sum_fintype]
  simp only [Fin.snoc_castSucc]
  rw [hprod, Finsupp.prod_single_index (by simp [Fin.snoc_last])]
  simp only [Fin.snoc_last]
  calc
    (algebraMap R S (f.coeff m)) *
          ((t ^ (m.sum fun _ e => e) * m.prod (fun i e => v i ^ e)) *
            t ^ (f.totalDegree - m.sum fun _ e => e)) =
        (algebraMap R S (f.coeff m)) *
          ((t ^ (m.sum fun _ e => e) * t ^ (f.totalDegree - m.sum fun _ e => e)) *
            m.prod (fun i e => v i ^ e)) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hle]; ring

/-! ### Standard smooth presentations -/

/-- The Jacobian determinant of a family of polynomials over `R` and of the family obtained from
it by clearing a denominator `s` differ by `s ^ c`. -/
private theorem jacobianDet_map_eq_C_pow_mul {R Rp : Type*} [CommRing R] [CommRing Rp]
    [Algebra R Rp] {n c : ℕ} (hcn : c ≤ n) (s : R)
    (fR : Fin c → MvPolynomial (Fin n) R) (f : Fin c → MvPolynomial (Fin n) Rp)
    (hmap : ∀ j, f j * C (algebraMap R Rp s) = MvPolynomial.map (algebraMap R Rp) (fR j)) :
    MvPolynomial.map (algebraMap R Rp) (jacobianDet hcn fR) =
      C (algebraMap R Rp s) ^ c * jacobianDet hcn f := by
  classical
  let Jf : Matrix (Fin c) (Fin c) (MvPolynomial (Fin n) Rp) := fun i j =>
    MvPolynomial.pderiv (Fin.castLE hcn i) (f j)
  let Jg : Matrix (Fin c) (Fin c) (MvPolynomial (Fin n) Rp) := fun i j =>
    MvPolynomial.pderiv (Fin.castLE hcn i) (MvPolynomial.map (algebraMap R Rp) (fR j))
  have hmat : Jg = (C (algebraMap R Rp s) : MvPolynomial (Fin n) Rp) • Jf := by
    refine Matrix.ext fun i j => ?_
    dsimp [Jg, Jf]
    rw [← hmap j, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C]
    simp only [add_zero, mul_zero]
    exact mul_comm _ _
  have hdetmap : MvPolynomial.map (algebraMap R Rp) (jacobianDet hcn fR) = Matrix.det Jg := by
    rw [jacobianDet]
    let J0 : Matrix (Fin c) (Fin c) (MvPolynomial (Fin n) R) := fun i j =>
      MvPolynomial.pderiv (Fin.castLE hcn i) (fR j)
    have hmapMatrix : J0.map (MvPolynomial.map (algebraMap R Rp)) = Jg :=
      Matrix.ext fun i j => by
        change MvPolynomial.map (algebraMap R Rp)
            (MvPolynomial.pderiv (Fin.castLE hcn i) (fR j)) =
          MvPolynomial.pderiv (Fin.castLE hcn i) (MvPolynomial.map (algebraMap R Rp) (fR j))
        rw [← MvPolynomial.pderiv_map]
    calc
      _ = (J0.map (MvPolynomial.map (algebraMap R Rp))).det := by
        have hdet := RingHom.map_det (MvPolynomial.map (algebraMap R Rp)) J0
        rwa [RingHom.mapMatrix_apply] at hdet
      _ = Jg.det := congrArg Matrix.det hmapMatrix
  rw [hdetmap, hmat, Matrix.det_smul]
  simp [Jf, jacobianDet]

/-- Evaluating a polynomial over `R`, viewed over `A` with one more variable, at `snoc v x`
forgets the extra variable. -/
private theorem aeval_snoc_rename_map {R A Z : Type*} [CommRing R] [CommRing A] [CommRing Z]
    [Algebra R A] [Algebra A Z] [Algebra R Z] [IsScalarTower R A Z] {n : ℕ}
    (v : Fin (n + 1) → Z) (x : Z) (h : MvPolynomial (Fin (n + 1)) R) :
    aeval (Fin.snoc (α := fun _ => Z) v x)
        (rename Fin.castSucc (MvPolynomial.map (algebraMap R A) h)) = aeval v h := by
  rw [aeval_rename]
  have hvec : (Fin.snoc (α := fun _ => Z) v x : Fin (n + 2) → Z) ∘ Fin.castSucc = v := by
    funext i
    simp
  rw [hvec, MvPolynomial.aeval_map_algebraMap]

/-- Mathlib's `Algebra.IsStandardSmooth` provides a standard smooth presentation in the explicit
form of `Stacks.Smoothing.IsStandardSmoothRingMap`. -/
theorem isStandardSmoothRingMap_of_isStandardSmooth (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (hA : Algebra.IsStandardSmooth R A) : IsStandardSmoothRingMap R A := by
  classical
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hA.out
  let _ : Finite ι := hι
  let _ : Finite σ := hσ
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype σ := Fintype.ofFinite σ
  let E : Set ι := Set.range P.map
  let _ : Fintype E := Fintype.ofFinite E
  let _ : Fintype (Eᶜ : Set ι) := Fintype.ofFinite (Eᶜ : Set ι)
  let n := Fintype.card σ
  let m := Fintype.card (Eᶜ : Set ι)
  let eσ : Fin n ≃ σ := (Fintype.equivFin σ).symm
  let eRange : σ ≃ E := Equiv.ofInjective P.map P.map_inj
  let eFirst : Fin n ≃ E := eσ.trans eRange
  let eRest : Fin m ≃ (Eᶜ : Set ι) := (Fintype.equivFin (Eᶜ : Set ι)).symm
  let eFin : Fin (n + m) ≃ Fin n ⊕ Fin m :=
    (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).symm
  let e : Fin (n + m) ≃ ι :=
    eFin.trans ((Equiv.sumCongr eFirst eRest).trans (Equiv.Set.sumCompl E))
  have hefirst (i : Fin n) : e (Fin.castAdd m i) = P.map (eσ i) := by
    simp [e, eFin, eFirst, eRange, eσ, Equiv.ofInjective, E, Equiv.trans_apply]
  let P' := P.reindex e eσ
  have hmap (i : Fin n) : P'.map i = Fin.castAdd m i := by
    change e.symm (P.map (eσ i)) = Fin.castAdd m i
    simpa using (congrArg e.symm (hefirst i)).symm
  let frel : Fin n → MvPolynomial (Fin (n + m)) R := P'.relation
  let π : MvPolynomial (Fin (n + m)) R →ₐ[R] A := aeval P'.toPresentation.val
  have hsurj : Function.Surjective π := P'.toPresentation.toGenerators.aeval_val_surjective
  have hker : RingHom.ker π = Ideal.span (Set.range frel) :=
    P'.toPresentation.span_range_relation_eq_ker.symm
  have hdet : jacobianDet (Nat.le_add_right n m) frel = P'.jacobiMatrix.det := by
    refine congrArg Matrix.det ?_
    ext i j
    have hcast : Fin.castLE (Nat.le_add_right n m) i = Fin.castAdd m i := Fin.ext rfl
    simp [frel, P'.jacobiMatrix_apply, hmap, hcast]
  have hunitπ : IsUnit (π (jacobianDet (Nat.le_add_right n m) frel)) := by
    rw [hdet]
    have hπjac : π P'.jacobiMatrix.det = P'.jacobian := by
      rw [P'.jacobian_eq_jacobiMatrix_det]; rfl
    exact hπjac ▸ P'.jacobian_isUnit
  let eQuot : (MvPolynomial (Fin (n + m)) R ⧸ Ideal.span (Set.range frel)) ≃ₐ[R] A :=
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  have hquotUnit : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range frel))
      (jacobianDet (Nat.le_add_right n m) frel)) := by
    have h := hunitπ.map eQuot.symm.toRingHom
    have hmk : eQuot.symm (π (jacobianDet (Nat.le_add_right n m) frel)) =
        Ideal.Quotient.mk (Ideal.span (Set.range frel))
          (jacobianDet (Nat.le_add_right n m) frel) := by
      refine eQuot.injective ?_
      rw [eQuot.apply_symm_apply]
      change π (jacobianDet (Nat.le_add_right n m) frel) =
        ((Ideal.quotientEquivAlgOfEq R hker.symm).trans
          (Ideal.quotientKerAlgEquivOfSurjective hsurj))
          (Ideal.Quotient.mk (Ideal.span (Set.range frel))
            (jacobianDet (Nat.le_add_right n m) frel))
      simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
        Ideal.quotientKerAlgEquivOfSurjective_mk]
    change IsUnit (eQuot.symm (π (jacobianDet (Nat.le_add_right n m) frel))) at h
    rwa [hmk] at h
  exact ⟨n + m, n, Nat.le_add_right n m, frel, hquotUnit, ⟨eQuot.symm⟩⟩

/-- Inverting the Jacobian determinant of the first `c` of the relations of a presentation with
`c ≤ n` variables produces a smooth algebra: `(R[x_1, …, x_n]/(f_1, …, f_c))_Δ` is smooth over
`R`, where `Δ` is the image of `det(∂f_j/∂x_i)_{i, j ≤ c}`. -/
theorem smooth_localization_away_jacobianDet (R : Type*) [CommRing R] {n c : ℕ} (hcn : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) R) :
    Algebra.Smooth R
      (Localization.Away
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) (jacobianDet hcn f)) : Type _) := by
  classical
  let Q := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
  let Δ : Q := Ideal.Quotient.mk _ (jacobianDet hcn f)
  let Ppres : Algebra.Presentation R Q (Fin n) (Fin c) := Algebra.Presentation.naive (v := f)
  let P : Algebra.PreSubmersivePresentation R Q (Fin n) (Fin c) :=
    { toPresentation := Ppres
      map := Fin.castLE hcn
      map_inj := Fin.castLE_injective hcn }
  let T := Localization.Away Δ
  have hjac : P.jacobian = Δ := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have hmatrix : P.jacobiMatrix =
        (fun i j : Fin c => MvPolynomial.pderiv (Fin.castLE hcn i) (f j)) := by
      ext i j
      simp [P, Ppres, Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
        Algebra.Presentation.naive_relation_apply]
    rw [hmatrix]
    change Ideal.Quotient.mk _
        (Matrix.det (fun i j : Fin c => MvPolynomial.pderiv (Fin.castLE hcn i) (f j))) = Δ
    rfl
  let _ : IsLocalization.Away P.jacobian T :=
    IsLocalization.Away.of_associated (show Associated P.jacobian Δ by rw [hjac]).symm
  let Pcomp := (Algebra.PreSubmersivePresentation.localizationAway T P.jacobian).comp P
  have hcompUnit : IsUnit Pcomp.jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def, hjac]
    exact (IsLocalization.Away.algebraMap_isUnit Δ).mul
      (IsLocalization.Away.algebraMap_isUnit Δ)
  have hstandard : Algebra.IsStandardSmooth R T :=
    Algebra.SubmersivePresentation.isStandardSmooth
      { __ := Pcomp
        jacobian_isUnit := hcompUnit }
  let _ : Algebra.IsStandardSmooth R T := hstandard
  exact inferInstance

/-- Restriction of scalars of a polynomial evaluation map along `R → S`. -/
private noncomputable def restrictMvPolynomialAlgHom {R S T σ : Type*} [CommSemiring R]
    [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra S T] [Algebra R T]
    (h : ∀ r : R, algebraMap R T r = algebraMap S T (algebraMap R S r))
    (π : MvPolynomial σ S →ₐ[S] T) : MvPolynomial σ R →ₐ[R] T where
  toRingHom := π.toRingHom.comp (MvPolynomial.map (algebraMap R S))
  commutes' r := by
    change π (MvPolynomial.map (algebraMap R S) (C r)) = _
    rw [MvPolynomial.map_C]
    change π (algebraMap S (MvPolynomial σ S) (algebraMap R S r)) = _
    exact (π.commutes _).trans (h r).symm

/-- In a localization at a prime, the image of an element is a unit exactly when the element
avoids the prime. -/
private theorem notMem_of_isUnit_algebraMap {Λ : Type*} [CommRing Λ] (q : Ideal Λ) [q.IsPrime]
    (Λq : Type*) [CommRing Λq] [Algebra Λ Λq] [IsLocalization.AtPrime Λq q] {x : Λ}
    (hx : IsUnit (algebraMap Λ Λq x)) : x ∉ q :=
  (IsLocalization.AtPrime.isUnit_to_map_iff Λq q x).1 hx

/-! ### Spreading out -/

/-- **The spreading-out step.** Given generators `a` of `A` over `R` and a resolution of the
localized chain, there are polynomials `f_1, …, f_c` in `R[x_1, …, x_n]` with `c ≤ n`, a variable
`rep i` for each generator `a i`, an element `s ∈ R ∖ p` clearing both the denominators of the
`f_j` and the relations of `A`, and elements `λ_1, …, λ_n, t, λ_0` of `Λ` with `t, λ_0 ∉ q`, such
that the homogenizations of the `f_j` vanish at `(λ, t)` after multiplying by `λ_0`, the
`rep i`-th coordinate equals `a_i t` after multiplying by `λ_0`, and the homogenized Jacobian
determinant evaluates outside `q`. -/
private theorem exists_spreadOut_of_isResolvableAfterLocalizing
    (S : LocalSmoothingSituation.{u, v, w}) {nA : ℕ} (a : Fin nA → S.A)
    (hfg : (RingHom.ker (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A).toRingHom).FG)
    (hres : S.IsResolvableAfterLocalizing) :
    ∃ (n c : ℕ) (hcn : c ≤ n) (fR : Fin c → MvPolynomial (Fin n) S.R)
        (rep : Fin nA → Fin n) (s : S.R) (nums : Fin n → S.Λ) (t x0 : S.Λ),
      (∀ p : MvPolynomial (Fin nA) S.R,
          (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A) p = 0 →
            C s * rename rep p ∈ Ideal.span (Set.range fR)) ∧
        algebraMap S.R S.Λ s ∉ S.q ∧ t ∉ S.q ∧ x0 ∉ S.q ∧
        (∀ j, x0 * aeval (Fin.snoc nums t) (homogenizeLast (fR j)) = 0) ∧
        (∀ i, x0 * (nums (rep i) - algebraMap S.A S.Λ (a i) * t) = 0) ∧
        aeval (Fin.snoc nums t) (homogenizeLast (jacobianDet hcn fR)) ∉ S.q := by
  classical
  obtain ⟨Rp, iRp, aRpR, lRp, Ap, iAp, aApA, aApR, aApRp, lAp, tApRA, tApRp,
    Λq, iΛq, aΛqΛ, aΛqA, aΛqRp, aΛqAp, lΛq, tΛqAΛ, tΛqAAp, tΛqRpAp, hlocResolve⟩ := hres
  obtain ⟨B, iB, aRpB, aApB, aBΛq, tRpApB, tApBΛq, tRpBΛq, hBFP, -, hsingNotLe⟩ := hlocResolve
  have hΛqAt : IsLocalization.AtPrime Λq S.q := lΛq
  have hΛqLocal : IsLocalRing Λq := IsLocalization.AtPrime.isLocalRing Λq S.q
  have hqΛqmax : (Ideal.map (algebraMap S.Λ Λq) S.q).IsMaximal :=
    IsLocalization.AtPrime.isMaximal_map S.q Λq
  -- An element of the singular ideal of `B` over `Rp` that is invertible in `Λq`.
  have hsingNotMap : ¬ Ideal.map (algebraMap B Λq) (singularIdeal Rp B) ≤
      Ideal.map (algebraMap S.Λ Λq) S.q := fun h =>
    hsingNotLe (hqΛqmax.isPrime.radical_le_iff.2 h)
  obtain ⟨b', hb', hb'Not⟩ : ∃ b' : B, b' ∈ singularIdeal Rp B ∧
      algebraMap B Λq b' ∉ Ideal.map (algebraMap S.Λ Λq) S.q := by
    by_contra hcon
    refine hsingNotMap (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
    by_contra hnot
    exact hcon ⟨x, hx, hnot⟩
  have hb'Unit : IsUnit (algebraMap B Λq b') := by
    by_contra hnotunit
    refine hb'Not ?_
    have hmem : algebraMap B Λq b' ∈ IsLocalRing.maximalIdeal Λq := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact mem_nonunits_iff.2 hnotunit
    rwa [← IsLocalization.AtPrime.map_eq_maximalIdeal S.q Λq] at hmem
  -- `BL = B_{b'}` is smooth over `Rp`, and one of its standard opens `D` is standard smooth.
  let BL := Localization.Away b'
  let : Algebra B BL := inferInstance
  let : IsLocalization.Away b' BL := inferInstance
  have hBLsmooth : Algebra.Smooth Rp BL :=
    smooth_localization_away_of_mem_singularIdeal Rp B hb'
  let fBLΛq : BL →ₐ[B] Λq :=
    IsLocalization.Away.liftAlgHom (x := b') (A := B) (f := Algebra.ofId B Λq) hb'Unit
  obtain ⟨opens, hopens, hstandard⟩ :=
    Algebra.Smooth.exists_span_eq_top_isStandardSmooth Rp BL
  obtain ⟨g, hgopens, hgnotMax⟩ : ∃ g ∈ opens, fBLΛq g ∉ IsLocalRing.maximalIdeal Λq := by
    by_contra hcon
    have hle : Ideal.span opens ≤
        Ideal.comap (fBLΛq : BL →+* Λq) (IsLocalRing.maximalIdeal Λq) :=
      Ideal.span_le.mpr fun x hx => by
        by_contra hnot
        exact hcon ⟨x, hx, hnot⟩
    have hmem : (1 : BL) ∈ Ideal.span opens := by rw [hopens]; simp
    have hone : (1 : Λq) ∈ IsLocalRing.maximalIdeal Λq := by simpa using hle hmem
    exact (IsLocalRing.maximalIdeal.isMaximal Λq).ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  have hgUnit : IsUnit (fBLΛq g) := by
    by_contra hnotunit
    exact hgnotMax (mem_nonunits_iff.2 hnotunit)
  let D := Localization.Away g
  let : CommRing D := inferInstance
  let : Algebra BL D := inferInstance
  let : IsLocalization.Away g D := inferInstance
  let : Algebra BL Λq := fBLΛq.toRingHom.toAlgebra
  let fDΛq : D →ₐ[BL] Λq :=
    IsLocalization.Away.liftAlgHom (x := g) (A := BL) (f := Algebra.ofId BL Λq) hgUnit
  let : Algebra Rp BL := inferInstance
  let : Algebra Rp D := inferInstance
  let : IsScalarTower Rp BL D := inferInstance
  let : IsScalarTower Rp B BL := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra S.R BL := ((algebraMap Rp BL).comp (algebraMap S.R Rp)).toAlgebra
  let : IsScalarTower S.R Rp BL := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra S.R D := ((algebraMap BL D).comp (algebraMap S.R BL)).toAlgebra
  let : Algebra S.R Λq := ((algebraMap BL Λq).comp (algebraMap S.R BL)).toAlgebra
  have hDmap (r : S.R) : algebraMap S.R D r = algebraMap Rp D (algebraMap S.R Rp r) := by
    calc algebraMap S.R D r = algebraMap BL D (algebraMap S.R BL r) := rfl
      _ = algebraMap BL D (algebraMap Rp BL (algebraMap S.R Rp r)) := by
          rw [IsScalarTower.algebraMap_apply S.R Rp BL r]
      _ = algebraMap Rp D (algebraMap S.R Rp r) :=
          (IsScalarTower.algebraMap_apply Rp BL D _).symm
  have hSRmap (r : S.R) : algebraMap S.R Λq r = algebraMap S.Λ Λq (algebraMap S.R S.Λ r) := by
    calc algebraMap S.R Λq r = algebraMap BL Λq (algebraMap S.R BL r) := rfl
      _ = algebraMap BL Λq (algebraMap B BL (algebraMap Rp B (algebraMap S.R Rp r))) := by
          rw [IsScalarTower.algebraMap_apply S.R Rp BL r, IsScalarTower.algebraMap_apply Rp B BL]
      _ = algebraMap B Λq (algebraMap Rp B (algebraMap S.R Rp r)) := by
          change fBLΛq (algebraMap B BL (algebraMap Rp B (algebraMap S.R Rp r))) = _
          rw [AlgHom.map_algebraMap fBLΛq]
      _ = algebraMap Rp Λq (algebraMap S.R Rp r) := by
          rw [← IsScalarTower.algebraMap_apply Rp B Λq]
      _ = algebraMap Ap Λq (algebraMap Rp Ap (algebraMap S.R Rp r)) := by
          rw [IsScalarTower.algebraMap_apply Rp Ap Λq]
      _ = algebraMap Ap Λq (algebraMap S.R Ap r) := by
          rw [IsScalarTower.algebraMap_apply S.R Rp Ap]
      _ = algebraMap Ap Λq (algebraMap S.A Ap (algebraMap S.R S.A r)) := by
          rw [IsScalarTower.algebraMap_apply S.R S.A Ap]
      _ = algebraMap S.A Λq (algebraMap S.R S.A r) := by
          rw [← IsScalarTower.algebraMap_apply S.A Ap Λq]
      _ = algebraMap S.Λ Λq (algebraMap S.R S.Λ r) := by
          rw [IsScalarTower.algebraMap_apply S.R S.A S.Λ,
            IsScalarTower.algebraMap_apply S.A S.Λ Λq]
  let fDQ : D →ₐ[S.R] Λq :=
    { toRingHom := fDΛq.toRingHom
      commutes' r := by
        change fDΛq (algebraMap S.R D r) = algebraMap S.R Λq r
        rw [show algebraMap S.R D r = algebraMap BL D (algebraMap S.R BL r) from rfl,
          AlgHom.map_algebraMap fDΛq]
        rfl }
  -- A presentation of `D` over `Rp` whose first variables are the images of the `a i`.
  let fAD : S.A →+* D :=
    (algebraMap BL D).comp
      ((algebraMap B BL).comp ((algebraMap Ap B).comp (algebraMap S.A Ap)))
  let fADR : S.A →ₐ[S.R] D :=
    { toRingHom := fAD
      commutes' r := by
        change algebraMap BL D (algebraMap B BL
          (algebraMap Ap B (algebraMap S.A Ap (algebraMap S.R S.A r)))) = _
        calc _ = algebraMap BL D (algebraMap B BL
                (algebraMap Rp B (algebraMap S.R Rp r))) := by
              rw [← IsScalarTower.algebraMap_apply S.R S.A Ap r,
                IsScalarTower.algebraMap_apply S.R Rp Ap r,
                IsScalarTower.algebraMap_apply Rp Ap B]
          _ = algebraMap Rp D (algebraMap S.R Rp r) := by
              rw [← IsScalarTower.algebraMap_apply Rp B BL,
                ← IsScalarTower.algebraMap_apply Rp BL D]
          _ = algebraMap S.R D r := (hDmap r).symm }
  have hfADΛq (x : S.A) : fDΛq (fAD x) = algebraMap S.Λ Λq (algebraMap S.A S.Λ x) := by
    calc fDΛq (fAD x) = fDΛq (algebraMap BL D
            (algebraMap B BL (algebraMap Ap B (algebraMap S.A Ap x)))) := rfl
      _ = algebraMap BL Λq (algebraMap B BL (algebraMap Ap B (algebraMap S.A Ap x))) := by
          rw [AlgHom.map_algebraMap fDΛq]
      _ = algebraMap B Λq (algebraMap Ap B (algebraMap S.A Ap x)) := by
          change fBLΛq (algebraMap B BL (algebraMap Ap B (algebraMap S.A Ap x))) = _
          rw [AlgHom.map_algebraMap fBLΛq]
      _ = algebraMap Ap Λq (algebraMap S.A Ap x) := by
          rw [← IsScalarTower.algebraMap_apply Ap B Λq]
      _ = algebraMap S.A Λq x := by rw [← IsScalarTower.algebraMap_apply S.A Ap Λq]
      _ = algebraMap S.Λ Λq (algebraMap S.A S.Λ x) :=
          IsScalarTower.algebraMap_apply S.A S.Λ Λq x
  let genD : Fin nA → D := fun i => fAD (a i)
  let E : Finset D := Finset.univ.image genD
  obtain ⟨m, c, -, hcm, f, π, ⟨-, hπker⟩, hdetUnit, hEeq⟩ :=
    standardSmooth_presentation_with_prescribed_generators Rp D
      (isStandardSmoothRingMap_of_isStandardSmooth Rp D (hstandard g hgopens)) E E.card rfl
  have hrepGenEx (i : Fin nA) : ∃ j : Fin E.card, π (X (Fin.castAdd m j)) = genD i := by
    have hi : genD i ∈ (E : Set D) := by simp [E, genD]
    rwa [hEeq] at hi
  let repGen : Fin nA → Fin E.card := fun i => Classical.choose (hrepGenEx i)
  have hrepGen (i : Fin nA) : π (X (Fin.castAdd m (repGen i))) = genD i :=
    Classical.choose_spec (hrepGenEx i)
  let repCoord : Fin nA → Fin (E.card + m) := fun i => Fin.castAdd m (repGen i)
  let coordD : Fin (E.card + m) → D := fun i => π (X i)
  let πSR : MvPolynomial (Fin (E.card + m)) S.R →ₐ[S.R] D := restrictMvPolynomialAlgHom hDmap π
  have hπSR : πSR = aeval coordD := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [πSR, restrictMvPolynomialAlgHom, coordD]
  -- Clear the denominators of the relations.
  obtain ⟨sCoeff, hsCoeff, fR, hmapfR⟩ :=
    exists_mem_forall_mul_C_eq_map (R := S.R) (Rp := Rp) S.basePrime.primeCompl f
  have hspanfR : Ideal.span (Set.range fun j : Fin c =>
      MvPolynomial.map (algebraMap S.R Rp) (fR j)) = Ideal.span (Set.range f) := by
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨j, rfl⟩
      change MvPolynomial.map (algebraMap S.R Rp) (fR j) ∈ Ideal.span (Set.range f)
      rw [← hmapfR j]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨j, rfl⟩
      have hunit : IsUnit (C (algebraMap S.R Rp sCoeff) :
          MvPolynomial (Fin (E.card + m)) Rp) :=
        IsUnit.map C
          (IsLocalization.map_units (M := S.basePrime.primeCompl) Rp ⟨sCoeff, hsCoeff⟩)
      have hscale : f j = MvPolynomial.map (algebraMap S.R Rp) (fR j) * ↑hunit.unit⁻¹ := by
        calc f j = (f j * C (algebraMap S.R Rp sCoeff)) * ↑hunit.unit⁻¹ := by
              rw [mul_assoc, hunit.mul_val_inv, mul_one]
          _ = MvPolynomial.map (algebraMap S.R Rp) (fR j) * ↑hunit.unit⁻¹ := by rw [hmapfR j]
      rw [hscale]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hFRzero (j : Fin c) : πSR (fR j) = 0 := by
    change π (MvPolynomial.map (algebraMap S.R Rp) (fR j)) = 0
    have hfmem : f j ∈ RingHom.ker π.toRingHom := by
      rw [hπker]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hfzero : π (f j) = 0 := RingHom.mem_ker.mp hfmem
    rw [← hmapfR j]
    simp [hfzero]
  -- Clear the denominators of the relations of `A`.
  obtain ⟨ιA, hιA, relA0, hrelA0⟩ :
      ∃ (ιA : Type 0), ∃ (_ : Finite ιA), ∃ relA0 : ιA → MvPolynomial (Fin nA) S.R,
        Submodule.span (MvPolynomial (Fin nA) S.R) (Set.range relA0) =
          RingHom.ker (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A).toRingHom :=
    Submodule.fg_iff_exists_finite_generating_family.mp hfg
  let : Finite ιA := hιA
  let : Fintype ιA := Fintype.ofFinite ιA
  have hqmem (i : ιA) : MvPolynomial.map (algebraMap S.R Rp) (rename repCoord (relA0 i)) ∈
      Ideal.span (Set.range fun j : Fin c => MvPolynomial.map (algebraMap S.R Rp) (fR j)) := by
    have hzero : π (MvPolynomial.map (algebraMap S.R Rp) (rename repCoord (relA0 i))) = 0 := by
      change πSR (rename repCoord (relA0 i)) = 0
      rw [hπSR, aeval_rename]
      have hcoords : coordD ∘ repCoord = fun i => fADR (a i) := funext fun j => hrepGen j
      rw [hcoords, ← MvPolynomial.comp_aeval_apply (f := a) fADR (relA0 i)]
      have hirel : relA0 i ∈
          RingHom.ker (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A).toRingHom := by
        rw [← hrelA0]
        exact Ideal.subset_span ⟨i, rfl⟩
      have hi : (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A) (relA0 i) = 0 :=
        RingHom.mem_ker.mp hirel
      rw [hi, map_zero]
    rw [hspanfR, ← hπker]
    exact RingHom.mem_ker.mpr hzero
  choose sA hsmem gA hgA using fun i : ιA =>
    exists_mem_and_C_mul_eq_sum (R := S.R) (Rp := Rp) S.basePrime.primeCompl fR
      (rename repCoord (relA0 i)) (hqmem i)
  have hsAll : (∏ i : ιA, sA i) ∈ S.basePrime.primeCompl :=
    S.basePrime.primeCompl.prod_mem fun i _ => hsmem i
  have hrelCleared (i : ιA) :
      C (∏ k : ιA, sA k) * rename repCoord (relA0 i) ∈ Ideal.span (Set.range fR) := by
    have hprod : (∏ k : ιA, sA k) = (∏ k ∈ Finset.univ.erase i, sA k) * sA i := by
      rw [mul_comm]
      simpa using
        (Finset.mul_prod_erase (Finset.univ : Finset ιA) (fun k => sA k)
          (Finset.mem_univ i)).symm
    rw [hprod, MvPolynomial.C_mul, mul_assoc, ← hgA i, Finset.mul_sum]
    exact Ideal.sum_mem _ fun j _ =>
      Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))
  refine ⟨E.card + m, c, hcm, fR, repCoord, sCoeff * (∏ i : ιA, sA i), ?_⟩
  have hrelAll : ∀ p : MvPolynomial (Fin nA) S.R,
      (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A) p = 0 →
        C (sCoeff * (∏ i : ιA, sA i)) * rename repCoord p ∈ Ideal.span (Set.range fR) := by
    have key : ∀ x ∈ Submodule.span (MvPolynomial (Fin nA) S.R) (Set.range relA0),
        C (∏ i : ιA, sA i) * rename repCoord x ∈ Ideal.span (Set.range fR) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact hrelCleared i
      | zero => simp
      | add x y _ _ hx hy =>
          rw [map_add, mul_add]
          exact Ideal.add_mem _ hx hy
      | smul r x _ hx =>
          have hre : C (∏ i : ιA, sA i) * rename repCoord (r • x) =
              rename repCoord r * (C (∏ i : ιA, sA i) * rename repCoord x) := by
            rw [smul_eq_mul, map_mul]; ring
          rw [hre]
          exact Ideal.mul_mem_left _ _ hx
    intro p hp
    have hpmem : p ∈ Submodule.span (MvPolynomial (Fin nA) S.R) (Set.range relA0) := by
      rw [hrelA0]
      exact RingHom.mem_ker.mpr hp
    rw [MvPolynomial.C_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ (key p hpmem)
  -- The `Λ`-points of the presentation.
  obtain ⟨t, ht, nums, hnums⟩ :=
    exists_mem_forall_mul_eq_map (R := S.Λ) (T := Λq) S.q.primeCompl
      (fun i : Fin (E.card + m) => fDΛq (coordD i))
  let ψ : S.Λ →ₐ[S.R] Λq :=
    { toRingHom := algebraMap S.Λ Λq
      commutes' r := (hSRmap r).symm }
  have hvector : (fun i : Fin (E.card + m + 1) =>
        ψ ((Fin.snoc nums t : Fin (E.card + m + 1) → S.Λ) i)) =
      Fin.snoc (α := fun _ => Λq)
        (fun i => algebraMap S.Λ Λq t * fDΛq (coordD i)) (algebraMap S.Λ Λq t) := by
    funext i
    refine Fin.lastCases ?_ (fun l => ?_) i
    · change algebraMap S.Λ Λq
        ((Fin.snoc nums t : Fin (E.card + m + 1) → S.Λ) (Fin.last _)) = _
      rw [Fin.snoc_last, Fin.snoc_last]
    · change algebraMap S.Λ Λq
        ((Fin.snoc nums t : Fin (E.card + m + 1) → S.Λ) (Fin.castSucc l)) = _
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc, ← hnums l]
      ring
  have hpushΛ (h : MvPolynomial (Fin (E.card + m + 1)) S.R) :
      algebraMap S.Λ Λq (aeval (Fin.snoc nums t) h) =
        aeval (Fin.snoc (α := fun _ => Λq) (fun i => algebraMap S.Λ Λq t * fDΛq (coordD i))
          (algebraMap S.Λ Λq t)) h := by
    have hc := MvPolynomial.comp_aeval_apply (f := Fin.snoc nums t) ψ h
    rwa [hvector] at hc
  have hEvalQ (j : Fin c) : aeval (fun i => fDΛq (coordD i)) (fR j) = 0 := by
    have hc := MvPolynomial.comp_aeval_apply (f := coordD) fDQ (fR j)
    rw [← hπSR, hFRzero j, map_zero] at hc
    simpa [fDQ] using hc.symm
  have hbadzero : ∀ k : Fin (c + nA), algebraMap S.Λ Λq
      (Fin.addCases (fun j : Fin c => aeval (Fin.snoc nums t) (homogenizeLast (fR j)))
        (fun i : Fin nA => nums (repCoord i) - algebraMap S.A S.Λ (a i) * t) k) = 0 := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun i => ?_) k
    · rw [Fin.addCases_left, hpushΛ, aeval_homogenizeLast, hEvalQ j, mul_zero]
    · rw [Fin.addCases_right, map_sub, map_mul]
      have hgen : fDΛq (coordD (repCoord i)) =
          algebraMap S.Λ Λq (algebraMap S.A S.Λ (a i)) := by
        change fDΛq (π (X (Fin.castAdd m (repGen i)))) = _
        rw [hrepGen i]
        exact hfADΛq (a i)
      rw [← hnums (repCoord i), ← hgen]
      ring
  obtain ⟨x0, hx0, hx0bad⟩ :=
    exists_mem_forall_mul_eq_zero (R := S.Λ) (T := Λq) S.q.primeCompl _ hbadzero
  refine ⟨nums, t, x0, hrelAll, ?_, ht, hx0, ?_, ?_, ?_⟩
  · intro hs
    rw [map_mul] at hs
    rcases S.isPrimeQ.mem_or_mem hs with h | h
    · exact hsCoeff (Ideal.mem_comap.mpr h)
    · exact hsAll (Ideal.mem_comap.mpr h)
  · intro j
    simpa using hx0bad (Fin.castAdd nA j)
  · intro i
    simpa using hx0bad (Fin.natAdd c i)
  · refine notMem_of_isUnit_algebraMap S.q Λq ?_
    rw [hpushΛ, aeval_homogenizeLast]
    have htQUnit : IsUnit (algebraMap S.Λ Λq t) :=
      IsLocalization.map_units (M := S.q.primeCompl) Λq ⟨t, ht⟩
    refine (htQUnit.pow _).mul ?_
    have hsRpUnit : IsUnit (algebraMap Rp D (algebraMap S.R Rp sCoeff)) :=
      (IsLocalization.map_units (M := S.basePrime.primeCompl) Rp ⟨sCoeff, hsCoeff⟩).map
        (algebraMap Rp D)
    have hjacDUnit : IsUnit (π (MvPolynomial.map (algebraMap S.R Rp) (jacobianDet hcm fR))) := by
      rw [jacobianDet_map_eq_C_pow_mul hcm sCoeff fR f hmapfR, map_mul, map_pow,
        show π (C (algebraMap S.R Rp sCoeff)) = algebraMap Rp D (algebraMap S.R Rp sCoeff) by
          simp]
      exact (hsRpUnit.pow c).mul hdetUnit
    have hevalJac : aeval (fun i => fDΛq (coordD i)) (jacobianDet hcm fR) =
        fDΛq (π (MvPolynomial.map (algebraMap S.R Rp) (jacobianDet hcm fR))) := by
      have hc := MvPolynomial.comp_aeval_apply (f := coordD) fDQ (jacobianDet hcm fR)
      rw [← hπSR] at hc
      simpa [fDQ, πSR, restrictMvPolynomialAlgHom] using hc.symm
    rw [hevalJac]
    exact hjacDUnit.map fDΛq.toRingHom

/-- **The smooth model.** The polynomial algebra `R[x_1, …, x_n]/(f_1, …, f_c)` with the
Jacobian determinant and `s` inverted is a smooth `R`-algebra `E` carrying the coordinates
`x_i` and an `A`-point sending the generator `a i` to the `rep i`-th coordinate. It has the
universal property of that localization: any `R`-algebra with a solution of the `f_j` making
the Jacobian determinant and `s` invertible receives a map from `E`. -/
private theorem exists_smooth_model
    (S : LocalSmoothingSituation.{u, v, w}) {nA : ℕ} (a : Fin nA → S.A)
    (ha : Function.Surjective (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A))
    {n c : ℕ} (hcn : c ≤ n) (fR : Fin c → MvPolynomial (Fin n) S.R)
    (rep : Fin nA → Fin n) (s : S.R)
    (hrel : ∀ p : MvPolynomial (Fin nA) S.R,
      (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A) p = 0 →
        C s * rename rep p ∈ Ideal.span (Set.range fR)) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra S.R E) (coordE : Fin n → E)
        (fAE : S.A →ₐ[S.R] E),
      Algebra.Smooth S.R E ∧ (∀ i, fAE (a i) = coordE (rep i)) ∧
      (∀ j, (aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] E) (fR j) = 0) ∧
      IsUnit ((aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] E) (jacobianDet hcn fR)) ∧
      IsUnit (algebraMap S.R E s) ∧
      ∀ (W : Type (max u v w)) (_ : CommRing W) (_ : Algebra S.R W) (ww : Fin n → W),
        (∀ j, (aeval ww : MvPolynomial (Fin n) S.R →ₐ[S.R] W) (fR j) = 0) →
        IsUnit ((aeval ww : MvPolynomial (Fin n) S.R →ₐ[S.R] W) (jacobianDet hcn fR)) →
        IsUnit (algebraMap S.R W s) →
        ∃ ρ : E →ₐ[S.R] W, ∀ i, ρ (coordE i) = ww i := by
  classical
  let If : Ideal (MvPolynomial (Fin n) S.R) := Ideal.span (Set.range fR)
  let Qf := MvPolynomial (Fin n) S.R ⧸ If
  let δf : Qf := Ideal.Quotient.mk If (jacobianDet hcn fR)
  let Eδ := Localization.Away δf
  let : CommRing Eδ := inferInstance
  let : Algebra Qf Eδ := inferInstance
  let : IsLocalization.Away δf Eδ := inferInstance
  let : Algebra S.R Eδ := inferInstance
  let Em := Localization.Away (algebraMap S.R Eδ s)
  let : CommRing Em := inferInstance
  let : Algebra Eδ Em := inferInstance
  let : IsLocalization.Away (algebraMap S.R Eδ s) Em := inferInstance
  let : Algebra S.R Em := inferInstance
  have hSmoothEδ : Algebra.Smooth S.R Eδ := smooth_localization_away_jacobianDet S.R hcn fR
  have hSmoothEm : Algebra.Smooth S.R Em :=
    Algebra.Smooth.localization_away (algebraMap S.R Eδ s)
  let coordE : Fin n → Em := fun i => (Algebra.ofId Qf Em) (Ideal.Quotient.mkₐ S.R If (X i))
  have hcoordMap : (aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] Em) =
      ((Algebra.ofId Qf Em).restrictScalars S.R).comp (Ideal.Quotient.mkₐ S.R If) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, coordE, aeval_X]
  have hfREval (j : Fin c) :
      (aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] Em) (fR j) = 0 := by
    rw [hcoordMap]
    have hmk : Ideal.Quotient.mkₐ S.R If (fR j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
    simp [hmk]
  have hjacEm : (aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] Em) (jacobianDet hcn fR) =
      algebraMap Qf Em δf := by
    rw [hcoordMap]
    rfl
  have hsEmUnit : IsUnit (algebraMap S.R Em s) := by
    change IsUnit (algebraMap Eδ Em (algebraMap S.R Eδ s))
    exact IsLocalization.Away.algebraMap_isUnit _
  have hjacEmUnit :
      IsUnit ((aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] Em) (jacobianDet hcn fR)) := by
    rw [hjacEm]
    have hδ2 := (IsLocalization.Away.algebraMap_isUnit (S := Eδ) δf).map (algebraMap Eδ Em)
    rwa [← IsScalarTower.algebraMap_apply Qf Eδ Em δf] at hδ2
  -- The `A`-point of the smooth model.
  have hkerα : ∀ p : MvPolynomial (Fin nA) S.R,
      (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A) p = 0 →
        (aeval fun i => coordE (rep i) : MvPolynomial (Fin nA) S.R →ₐ[S.R] Em) p = 0 := by
    intro p hp
    have hle : Ideal.span (Set.range fR) ≤
        RingHom.ker (aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] Em).toRingHom :=
      Ideal.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact hfREval j)
    have h1 : (aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] Em) (C s * rename rep p) = 0 :=
      RingHom.mem_ker.mp (hle (hrel p hp))
    rw [map_mul, aeval_C, MvPolynomial.aeval_rename] at h1
    refine hsEmUnit.mul_left_cancel ?_
    rw [mul_zero]
    exact h1
  let Lα : (MvPolynomial (Fin nA) S.R ⧸
      RingHom.ker (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A).toRingHom) →ₐ[S.R] Em :=
    Ideal.Quotient.liftₐ _ (aeval fun i => coordE (rep i))
      fun x hx => hkerα x (RingHom.mem_ker.mp hx)
  have hLαcomp : Lα.comp (Ideal.Quotient.mkₐ S.R _) =
      (aeval fun i => coordE (rep i) : MvPolynomial (Fin nA) S.R →ₐ[S.R] Em) :=
    Ideal.Quotient.liftₐ_comp _ _ _
  let fAE : S.A →ₐ[S.R] Em :=
    Lα.comp (Ideal.quotientKerAlgEquivOfSurjective ha).symm.toAlgHom
  have hgenAE (i : Fin nA) : fAE (a i) = coordE (rep i) := by
    have hai : a i = (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A) (X i) := by simp
    change Lα ((Ideal.quotientKerAlgEquivOfSurjective ha).symm (a i)) = _
    rw [hai, Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    have h := AlgHom.congr_fun hLαcomp (X i)
    rwa [aeval_X] at h
  -- The universal property.
  refine ⟨Em, inferInstance, inferInstance, coordE, fAE, hSmoothEm, hgenAE, hfREval,
    hjacEmUnit, hsEmUnit, fun W iW aW ww hwFR hwJac hwS => ?_⟩
  let φpoly : MvPolynomial (Fin n) S.R →ₐ[S.R] W := aeval ww
  have hIfKer : ∀ y : MvPolynomial (Fin n) S.R, y ∈ If → φpoly y = 0 := fun y hy =>
    RingHom.mem_ker.mp (Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact hwFR j) hy)
  let φQ : Qf →ₐ[S.R] W := Ideal.Quotient.liftₐ If φpoly hIfKer
  have hφQcomp : φQ.comp (Ideal.Quotient.mkₐ S.R If) = φpoly :=
    Ideal.Quotient.liftₐ_comp If φpoly hIfKer
  have hφQmk (y : MvPolynomial (Fin n) S.R) : φQ (Ideal.Quotient.mkₐ S.R If y) = φpoly y :=
    AlgHom.congr_fun hφQcomp y
  have hδWUnit : IsUnit (φQ δf) := by
    change IsUnit (φQ (Ideal.Quotient.mkₐ S.R If (jacobianDet hcn fR)))
    rw [hφQmk]
    exact hwJac
  let : Algebra Qf W := φQ.toRingHom.toAlgebra
  let φEδ : Eδ →ₐ[Qf] W :=
    IsLocalization.Away.liftAlgHom (x := δf) (A := Qf) (f := Algebra.ofId Qf W) hδWUnit
  let : Algebra Eδ W := φEδ.toRingHom.toAlgebra
  have hbaseEδ (r : S.R) : φEδ (algebraMap S.R Eδ r) = algebraMap S.R W r := by
    rw [show algebraMap S.R Eδ r = algebraMap Qf Eδ (algebraMap S.R Qf r) from rfl,
      AlgHom.map_algebraMap]
    exact φQ.commutes r
  have hsEδUnit : IsUnit ((Algebra.ofId Eδ W) (algebraMap S.R Eδ s)) := by
    change IsUnit (φEδ (algebraMap S.R Eδ s))
    rw [hbaseEδ]
    exact hwS
  let φEm : Em →ₐ[Eδ] W :=
    IsLocalization.Away.liftAlgHom (x := algebraMap S.R Eδ s) (A := Eδ)
      (f := Algebra.ofId Eδ W) hsEδUnit
  have hbaseEm (r : S.R) : φEm (algebraMap S.R Em r) = algebraMap S.R W r := by
    rw [show algebraMap S.R Em r = algebraMap Eδ Em (algebraMap S.R Eδ r) from rfl,
      AlgHom.map_algebraMap]
    exact hbaseEδ r
  refine ⟨{ toRingHom := φEm.toRingHom, commutes' := hbaseEm }, fun i => ?_⟩
  change φEm (algebraMap Eδ Em (algebraMap Qf Eδ (Ideal.Quotient.mkₐ S.R If (X i)))) = ww i
  rw [AlgHom.map_algebraMap]
  change φEδ (algebraMap Qf Eδ (Ideal.Quotient.mkₐ S.R If (X i))) = ww i
  rw [AlgHom.map_algebraMap]
  change φQ (Ideal.Quotient.mkₐ S.R If (X i)) = ww i
  rw [hφQmk]
  change (aeval ww : MvPolynomial (Fin n) S.R →ₐ[S.R] W) (X i) = ww i
  rw [aeval_X]

/-- **The construction step.** From the data produced by the spreading-out step and a smooth
model, build a factorization `A → C → Λ` with `C` of finite presentation over `R` whose singular
ideal is not carried into `q`. The ring is
`C = A[x_0, …, x_{n+1}]/(x_0 F_j, x_0 (x_{rep i} - a_i x_{n+1}))`, and the element
`b = x_0 x_{n+1} s F(jacobian)` of `C` lies in the singular ideal because `C_b` is a retract of
the smooth algebra `E[y_0, y_1][1/(y_0 y_1)]`. -/
private theorem exists_finitePresentation_not_le_of_smoothModel
    (S : LocalSmoothingSituation.{u, v, w}) {nA : ℕ} (a : Fin nA → S.A)
    (ha : Function.Surjective (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A))
    {n c : ℕ} (hcn : c ≤ n) (fR : Fin c → MvPolynomial (Fin n) S.R)
    (rep : Fin nA → Fin n) (s : S.R) (nums : Fin n → S.Λ) (t x0 : S.Λ)
    (hs : algebraMap S.R S.Λ s ∉ S.q) (ht : t ∉ S.q) (hx0 : x0 ∉ S.q)
    (hbadF : ∀ j, x0 * aeval (Fin.snoc nums t) (homogenizeLast (fR j)) = 0)
    (hbadA : ∀ i, x0 * (nums (rep i) - algebraMap S.A S.Λ (a i) * t) = 0)
    (hjac : aeval (Fin.snoc nums t) (homogenizeLast (jacobianDet hcn fR)) ∉ S.q)
    (E : Type u) (iE : CommRing E) (aE : Algebra S.R E) (coordE : Fin n → E)
    (fAE : S.A →ₐ[S.R] E) (hEsm : Algebra.Smooth S.R E)
    (hgenAE : ∀ i, fAE (a i) = coordE (rep i))
    (hfRE : ∀ j, (aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] E) (fR j) = 0)
    (hjacE : IsUnit ((aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] E) (jacobianDet hcn fR)))
    (hsE : IsUnit (algebraMap S.R E s))
    (hliftE : ∀ (W : Type (max u v w)) (_ : CommRing W) (_ : Algebra S.R W) (ww : Fin n → W),
      (∀ j, (aeval ww : MvPolynomial (Fin n) S.R →ₐ[S.R] W) (fR j) = 0) →
      IsUnit ((aeval ww : MvPolynomial (Fin n) S.R →ₐ[S.R] W) (jacobianDet hcn fR)) →
      IsUnit (algebraMap S.R W s) →
      ∃ ρ : E →ₐ[S.R] W, ∀ i, ρ (coordE i) = ww i) :
    ∃ (Cr : Type (max u v w)) (_ : CommRing Cr) (_ : Algebra S.R Cr) (_ : Algebra S.A Cr)
        (_ : Algebra Cr S.Λ),
      IsScalarTower S.R S.A Cr ∧ IsScalarTower S.A Cr S.Λ ∧ IsScalarTower S.R Cr S.Λ ∧
        Algebra.FinitePresentation S.R Cr ∧
        ¬ Ideal.map (algebraMap Cr S.Λ) (singularIdeal S.R Cr) ≤ S.q := by
  classical
  -- The smooth algebra `V = E[y_0, y_1][1/(y_0 y_1)]`.
  let T := MvPolynomial (Fin 2) E
  have hSmoothT : Algebra.Smooth S.R T :=
    have : Algebra.Smooth S.R E := hEsm
    have : Algebra.Smooth E T := ⟨inferInstance, inferInstance⟩
    Algebra.Smooth.comp S.R E T
  let V := Localization.Away ((X 0 : T) * X 1)
  let : Algebra T V := inferInstance
  let : IsLocalization.Away ((X 0 : T) * X 1) V := inferInstance
  have hSmoothV : Algebra.Smooth S.R V := Algebra.Smooth.localization_away ((X 0 : T) * X 1)
  -- The finitely presented algebra `Cr` over `A`.
  let coordVar : Fin n → Fin (n + 2) := fun i => Fin.castSucc (Fin.castSucc i)
  let tVar : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let x0Var : Fin (n + 2) := Fin.last (n + 1)
  let P := MvPolynomial (Fin (n + 2)) S.A
  let jacHom : MvPolynomial (Fin (n + 1)) S.R := homogenizeLast (jacobianDet hcn fR)
  let jacHomA : P := rename Fin.castSucc (MvPolynomial.map (algebraMap S.R S.A) jacHom)
  let relF : Fin c → P := fun j =>
    X x0Var * rename Fin.castSucc
      (MvPolynomial.map (algebraMap S.R S.A) (homogenizeLast (fR j)))
  let relA : Fin nA → P := fun i => X x0Var * (X (coordVar (rep i)) - C (a i) * X tVar)
  let rel : Fin (c + nA) → P := Fin.addCases relF relA
  let J : Ideal P := Ideal.span (Set.range rel)
  let C0 := P ⧸ J
  let rawVals : Fin (n + 2) → S.Λ :=
    Fin.snoc (α := fun _ => S.Λ) (Fin.snoc (α := fun _ => S.Λ) nums t) x0
  let η : P →ₐ[S.A] S.Λ := aeval rawVals
  have hηX0 : η (X x0Var) = x0 := by
    change aeval rawVals (X x0Var) = x0
    rw [aeval_X]
    simp [rawVals, x0Var]
  have hηT : η (X tVar) = t := by
    change aeval rawVals (X tVar) = t
    rw [aeval_X]
    simp [rawVals, tVar]
  have hηCof (y : S.A) : η (C y) = algebraMap S.A S.Λ y := by
    change aeval rawVals (C y) = _
    rw [aeval_C]
  have hmapEvalΛ (h : MvPolynomial (Fin (n + 1)) S.R) :
      η (rename Fin.castSucc (MvPolynomial.map (algebraMap S.R S.A) h)) =
        aeval (Fin.snoc nums t) h := by
    exact aeval_snoc_rename_map (Fin.snoc nums t) x0 h
  have hηrel : ∀ k : Fin (c + nA), η (rel k) = 0 := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun i => ?_) k
    · rw [show rel (Fin.castAdd nA j) = relF j from by simp [rel]]
      change η (X x0Var * rename Fin.castSucc
        (MvPolynomial.map (algebraMap S.R S.A) (homogenizeLast (fR j)))) = 0
      rw [map_mul, hηX0, hmapEvalΛ]
      exact hbadF j
    · rw [show rel (Fin.natAdd c i) = relA i from by simp [rel]]
      change η (X x0Var * (X (coordVar (rep i)) - C (a i) * X tVar)) = 0
      rw [map_mul, map_sub, map_mul, hηX0, hηT, hηCof (a i),
        show η (X (coordVar (rep i))) = nums (rep i) from by
          change aeval rawVals (X (coordVar (rep i))) = _
          rw [aeval_X]
          simp [rawVals, coordVar]]
      exact hbadA i
  have hJker : J ≤ RingHom.ker η.toRingHom :=
    Ideal.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact hηrel k)
  let ηC0 : C0 →ₐ[S.A] S.Λ :=
    Ideal.Quotient.liftₐ J η fun x hx => RingHom.mem_ker.mp (hJker hx)
  have hJfg : J.FG := Submodule.fg_span (Set.finite_range rel)
  have hC0fp : Algebra.FinitePresentation S.A C0 := Algebra.FinitePresentation.quotient hJfg
  let Cr := ULift.{max u v w} C0
  let : CommRing Cr := inferInstance
  let : Algebra S.A Cr := inferInstance
  let : Algebra.FinitePresentation S.A Cr := hC0fp.equiv (ULift.algEquiv (R := S.A)).symm
  let ηC : Cr →ₐ[S.A] S.Λ := ηC0.comp (ULift.algEquiv (R := S.A)).toAlgHom
  let : Algebra S.R Cr := inferInstance
  let : IsScalarTower S.R S.A Cr := inferInstance
  let : Algebra Cr S.Λ := ηC.toRingHom.toAlgebra
  let eUL : C0 ≃ₐ[S.A] Cr := (ULift.algEquiv (R := S.A)).symm
  let mkPC : P →ₐ[S.A] Cr := eUL.toAlgHom.comp (Ideal.Quotient.mkₐ S.A J)
  have hηmkPC : ηC.comp mkPC = η := by
    refine MvPolynomial.algHom_ext fun i => ?_
    change ηC0 (Ideal.Quotient.mkₐ S.A J (X i)) = η (X i)
    exact congrArg (fun φ : P →ₐ[S.A] S.Λ => φ (X i))
      (Ideal.Quotient.liftₐ_comp J η fun x hx => RingHom.mem_ker.mp (hJker hx))
  have hηCmk (p : P) : ηC (mkPC p) = η p :=
    congrArg (fun φ : P →ₐ[S.A] S.Λ => φ p) hηmkPC
  have hηCcoeff (r : S.R) : ηC (algebraMap S.R Cr r) = algebraMap S.R S.Λ r := by
    rw [IsScalarTower.algebraMap_apply S.R S.A Cr r, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply S.R S.A S.Λ r]
  have hCfp : Algebra.FinitePresentation S.R Cr := Algebra.FinitePresentation.trans S.R S.A Cr
  have hmkPCsurj : Function.Surjective mkPC := by
    intro x
    obtain ⟨y, hy⟩ := eUL.surjective x
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨q, ?_⟩
    change eUL (Ideal.Quotient.mkₐ S.A J q) = x
    rw [← hy]
    exact congrArg eUL hq
  let b : Cr := mkPC (X x0Var) * mkPC (X tVar) * algebraMap S.R Cr s * mkPC jacHomA
  -- `Cr` maps to `V`.
  let fAtoV : S.A →ₐ[S.R] V := ((Algebra.ofId E V).restrictScalars S.R).comp fAE
  let : Algebra S.A V := fAtoV.toRingHom.toAlgebra
  let : IsScalarTower S.R S.A V := IsScalarTower.of_algHom fAtoV
  let x0V : V := algebraMap T V (X 0)
  let tV : V := algebraMap T V (X 1)
  let coordV : Fin n → V := fun i => algebraMap E V (coordE i)
  let rawV : Fin (n + 2) → V :=
    Fin.snoc (α := fun _ => V) (Fin.snoc (α := fun _ => V) (fun i => tV * coordV i) tV) x0V
  let ηV : P →ₐ[S.A] V := aeval rawV
  have hηVX0 : ηV (X x0Var) = x0V := by
    change aeval rawV (X x0Var) = x0V
    rw [aeval_X]
    simp [rawV, x0Var]
  have hηVT : ηV (X tVar) = tV := by
    change aeval rawV (X tVar) = tV
    rw [aeval_X]
    simp [rawV, tVar]
  have hηVcoord (i : Fin n) : ηV (X (coordVar i)) = tV * coordV i := by
    change aeval rawV (X (coordVar i)) = _
    rw [aeval_X]
    simp [rawV, coordVar]
  have hηVcof (y : S.A) : ηV (C y) = algebraMap S.A V y := by
    change aeval rawV (C y) = _
    rw [aeval_C]
  have hmapEvalV (h : MvPolynomial (Fin (n + 1)) S.R) :
      ηV (rename Fin.castSucc (MvPolynomial.map (algebraMap S.R S.A) h)) =
        aeval (Fin.snoc (α := fun _ => V) (fun i => tV * coordV i) tV) h := by
    exact aeval_snoc_rename_map (Fin.snoc (α := fun _ => V) (fun i => tV * coordV i) tV) x0V h
  have hpushV (h : MvPolynomial (Fin n) S.R) :
      (aeval coordV : MvPolynomial (Fin n) S.R →ₐ[S.R] V) h =
        algebraMap E V ((aeval coordE : MvPolynomial (Fin n) S.R →ₐ[S.R] E) h) :=
    (MvPolynomial.comp_aeval_apply (f := coordE)
      ((Algebra.ofId E V).restrictScalars S.R) h).symm
  have hfRV (j : Fin c) : (aeval coordV : MvPolynomial (Fin n) S.R →ₐ[S.R] V) (fR j) = 0 := by
    rw [hpushV, hfRE j, map_zero]
  have hηVrel : ∀ k : Fin (c + nA), ηV (rel k) = 0 := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun i => ?_) k
    · rw [show rel (Fin.castAdd nA j) = relF j from by simp [rel]]
      change ηV (X x0Var * rename Fin.castSucc
        (MvPolynomial.map (algebraMap S.R S.A) (homogenizeLast (fR j)))) = 0
      rw [map_mul, hmapEvalV, aeval_homogenizeLast, hfRV j, mul_zero, mul_zero]
    · rw [show rel (Fin.natAdd c i) = relA i from by simp [rel]]
      change ηV (X x0Var * (X (coordVar (rep i)) - C (a i) * X tVar)) = 0
      rw [map_mul, map_sub, map_mul, hηVT, hηVcoord, hηVcof (a i),
        show algebraMap S.A V (a i) = algebraMap E V (fAE (a i)) from rfl, hgenAE]
      change _ * (tV * coordV (rep i) - coordV (rep i) * tV) = 0
      ring
  have hkerηV : J ≤ RingHom.ker ηV.toRingHom :=
    Ideal.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact hηVrel k)
  let fCV : Cr →ₐ[S.A] V :=
    (Ideal.Quotient.liftₐ J ηV fun x hx =>
      RingHom.mem_ker.mp (hkerηV hx)).comp (ULift.algEquiv (R := S.A)).toAlgHom
  have hfCVmk (p : P) : fCV (mkPC p) = ηV p :=
    congrArg (fun φ : P →ₐ[S.A] V => φ p)
      (Ideal.Quotient.liftₐ_comp J ηV fun x hx => RingHom.mem_ker.mp (hkerηV hx))
  have hfCVbase (r : S.R) : fCV (algebraMap S.R Cr r) = algebraMap S.R V r := by
    rw [IsScalarTower.algebraMap_apply S.R S.A Cr r, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply S.R S.A V r]
  have hxtVUnit : IsUnit (x0V * tV) := by
    change IsUnit (algebraMap T V (X 0) * algebraMap T V (X 1))
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨hx0VUnit, htVUnit⟩ := IsUnit.mul_iff.mp hxtVUnit
  have hsVUnit : IsUnit (algebraMap S.R V s) := by
    have h := hsE.map (algebraMap E V)
    rwa [← IsScalarTower.algebraMap_apply S.R E V s] at h
  have hjacHomVUnit : IsUnit (ηV jacHomA) := by
    have hval : ηV jacHomA = tV ^ (jacobianDet hcn fR).totalDegree *
        aeval coordV (jacobianDet hcn fR) := by
      change ηV (rename Fin.castSucc (MvPolynomial.map (algebraMap S.R S.A) jacHom)) = _
      rw [hmapEvalV]
      exact aeval_homogenizeLast (jacobianDet hcn fR) coordV tV
    rw [hval, hpushV]
    exact (htVUnit.pow _).mul (hjacE.map (algebraMap E V))
  have hbV : IsUnit (fCV b) := by
    have hbval : fCV b = x0V * tV * algebraMap S.R V s * ηV jacHomA := by
      change fCV (mkPC (X x0Var) * mkPC (X tVar) * algebraMap S.R Cr s * mkPC jacHomA) = _
      rw [map_mul, map_mul, map_mul, hfCVmk, hfCVmk, hfCVmk, hfCVbase, hηVX0, hηVT]
    rw [hbval]
    exact ((hx0VUnit.mul htVUnit).mul hsVUnit).mul hjacHomVUnit
  -- `Cr_b` is a retract of `V`.
  let Cb := Localization.Away b
  let : Algebra Cr Cb := inferInstance
  let : IsLocalization.Away b Cb := inferInstance
  let : Algebra S.A Cb := ((algebraMap Cr Cb).comp (algebraMap S.A Cr)).toAlgebra
  let : Algebra S.R Cb := ((algebraMap Cr Cb).comp (algebraMap S.R Cr)).toAlgebra
  let : SMul Cr Cb := Algebra.toSMul
  let : SMul S.A Cb := Algebra.toSMul
  let : SMul S.R Cb := Algebra.toSMul
  let : SMul S.R Cr := Algebra.toSMul
  let : SMul S.A Cr := Algebra.toSMul
  let : IsScalarTower S.R Cr Cb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcoeffCb (r : S.R) : algebraMap S.A Cb (algebraMap S.R S.A r) = algebraMap S.R Cb r := by
    change algebraMap Cr Cb (algebraMap S.A Cr (algebraMap S.R S.A r)) =
      algebraMap Cr Cb (algebraMap S.R Cr r)
    rw [IsScalarTower.algebraMap_apply S.R S.A Cr r]
  let : IsScalarTower S.R S.A Cb := IsScalarTower.of_algebraMap_eq fun r => (hcoeffCb r).symm
  let x0Cb : Cb := algebraMap Cr Cb (mkPC (X x0Var))
  let tCb : Cb := algebraMap Cr Cb (mkPC (X tVar))
  let jacHomCb : Cb := algebraMap Cr Cb (mkPC jacHomA)
  have hbProduct : IsUnit (x0Cb * tCb * algebraMap S.R Cb s * jacHomCb) := by
    have hb := IsLocalization.Away.algebraMap_isUnit (S := Cb) b
    change IsUnit (algebraMap Cr Cb
      (mkPC (X x0Var) * mkPC (X tVar) * algebraMap S.R Cr s * mkPC jacHomA)) at hb
    rwa [map_mul, map_mul, map_mul] at hb
  obtain ⟨⟨hxtCbUnit, hsCbUnit⟩, hjacHomCbUnit⟩ :=
    (IsUnit.mul_iff.mp hbProduct).imp_left IsUnit.mul_iff.mp
  obtain ⟨hx0CbUnit, htCbUnit⟩ := IsUnit.mul_iff.mp hxtCbUnit
  let coordCb : Fin n → Cb := fun i =>
    algebraMap Cr Cb (mkPC (X (coordVar i))) * ↑htCbUnit.unit⁻¹
  have hmkRel (k : Fin (c + nA)) : mkPC (rel k) = 0 := by
    change eUL (Ideal.Quotient.mkₐ S.A J (rel k)) = 0
    rw [show Ideal.Quotient.mkₐ S.A J (rel k) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩), map_zero]
  let ηCb : P →ₐ[S.A] Cb :=
    { toRingHom := (algebraMap Cr Cb).comp mkPC.toRingHom
      commutes' _ := rfl }
  have hηCbX (i : Fin (n + 2)) : ηCb (X i) = algebraMap Cr Cb (mkPC (X i)) := rfl
  have hηCbcof (y : S.A) : ηCb (C y) = algebraMap S.A Cb y := ηCb.commutes y
  have hηCbcoord (i : Fin n) : ηCb (X (coordVar i)) = tCb * coordCb i := by
    rw [hηCbX]
    change algebraMap Cr Cb (mkPC (X (coordVar i))) =
      tCb * (algebraMap Cr Cb (mkPC (X (coordVar i))) * ↑htCbUnit.unit⁻¹)
    rw [mul_comm tCb, mul_assoc, htCbUnit.val_inv_mul, mul_one]
  have hηCbeq : ηCb = aeval (Fin.snoc (α := fun _ => Cb)
      (Fin.snoc (α := fun _ => Cb) (fun i => tCb * coordCb i) tCb) x0Cb) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hηCbX, aeval_X, Fin.snoc_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · rw [hηCbX, aeval_X, Fin.snoc_castSucc, Fin.snoc_last]
      · rw [aeval_X, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hηCbcoord k
  have hmapEvalCb (h : MvPolynomial (Fin (n + 1)) S.R) :
      ηCb (rename Fin.castSucc (MvPolynomial.map (algebraMap S.R S.A) h)) =
        aeval (Fin.snoc (α := fun _ => Cb) (fun i => tCb * coordCb i) tCb) h := by
    rw [hηCbeq]
    exact aeval_snoc_rename_map
      (Fin.snoc (α := fun _ => Cb) (fun i => tCb * coordCb i) tCb) x0Cb h
  have hEvalFR (j : Fin c) :
      (aeval coordCb : MvPolynomial (Fin n) S.R →ₐ[S.R] Cb) (fR j) = 0 := by
    have hz : ηCb (X x0Var * rename Fin.castSucc
        (MvPolynomial.map (algebraMap S.R S.A) (homogenizeLast (fR j)))) = 0 := by
      have hm : mkPC (relF j) = 0 := by
        have h := hmkRel (Fin.castAdd nA j)
        rwa [show rel (Fin.castAdd nA j) = relF j from by simp [rel]] at h
      change algebraMap Cr Cb (mkPC (relF j)) = 0
      rw [hm, map_zero]
    rw [map_mul, hmapEvalCb, aeval_homogenizeLast, hηCbX] at hz
    refine (hx0CbUnit.mul (htCbUnit.pow (fR j).totalDegree)).mul_left_cancel ?_
    rw [mul_zero, mul_assoc]
    exact hz
  have hjacCbUnit :
      IsUnit ((aeval coordCb : MvPolynomial (Fin n) S.R →ₐ[S.R] Cb) (jacobianDet hcn fR)) := by
    have hval : ηCb jacHomA = tCb ^ (jacobianDet hcn fR).totalDegree *
        aeval coordCb (jacobianDet hcn fR) := by
      change ηCb (rename Fin.castSucc (MvPolynomial.map (algebraMap S.R S.A) jacHom)) = _
      rw [hmapEvalCb]
      exact aeval_homogenizeLast (jacobianDet hcn fR) coordCb tCb
    have hunit : IsUnit (ηCb jacHomA) := hjacHomCbUnit
    rw [hval] at hunit
    exact (IsUnit.mul_iff.mp hunit).2
  have hcoordRep (i : Fin nA) : coordCb (rep i) = algebraMap S.A Cb (a i) := by
    have hz : ηCb (X x0Var * (X (coordVar (rep i)) - C (a i) * X tVar)) = 0 := by
      have hm : mkPC (relA i) = 0 := by
        have h := hmkRel (Fin.natAdd c i)
        rwa [show rel (Fin.natAdd c i) = relA i from by simp [rel]] at h
      change algebraMap Cr Cb (mkPC (relA i)) = 0
      rw [hm, map_zero]
    rw [map_mul, map_sub, map_mul, hηCbcoord, hηCbcof (a i), hηCbX x0Var, hηCbX tVar] at hz
    refine htCbUnit.mul_left_cancel ?_
    refine hx0CbUnit.mul_left_cancel ?_
    rw [mul_sub] at hz
    have h2 := sub_eq_zero.mp hz
    rw [h2]
    ring
  -- The retraction `V → Cr_b`.
  obtain ⟨ρ, hρ⟩ := hliftE Cb inferInstance inferInstance coordCb hEvalFR hjacCbUnit hsCbUnit
  let varsCb : Fin 2 → Cb := fun i => if i = 0 then x0Cb else tCb
  have hvars0 : varsCb 0 = x0Cb := by simp [varsCb]
  have hvars1 : varsCb 1 = tCb := by norm_num [varsCb]
  let : Algebra E Cb := ρ.toRingHom.toAlgebra
  let φT : T →ₐ[E] Cb := aeval varsCb
  have hlocT : IsUnit (φT ((X 0 : T) * X 1)) := by
    change IsUnit (aeval varsCb ((X 0 : T) * X 1))
    rw [map_mul, aeval_X, aeval_X, hvars0, hvars1]
    exact hxtCbUnit
  let : Algebra T Cb := φT.toRingHom.toAlgebra
  let φV : V →ₐ[T] Cb :=
    IsLocalization.Away.liftAlgHom (x := (X 0 : T) * X 1) (A := T)
      (f := Algebra.ofId T Cb) hlocT
  let rVCb : V →ₐ[S.R] Cb :=
    { toRingHom := φV.toRingHom
      commutes' r := by
        calc φV (algebraMap S.R V r) = φV (algebraMap T V (algebraMap S.R T r)) := by
              rw [IsScalarTower.algebraMap_apply S.R T V r]
          _ = algebraMap T Cb (algebraMap S.R T r) := by rw [AlgHom.map_algebraMap]
          _ = φT (algebraMap E T (algebraMap S.R E r)) := by
              rw [IsScalarTower.algebraMap_apply S.R E T r]
              rfl
          _ = algebraMap E Cb (algebraMap S.R E r) := by rw [AlgHom.map_algebraMap]
          _ = algebraMap S.R Cb r := ρ.commutes r }
  have hx0R : rVCb x0V = x0Cb := by
    change φV (algebraMap T V (X 0)) = x0Cb
    rw [AlgHom.map_algebraMap]
    change aeval varsCb (X 0) = x0Cb
    rw [aeval_X, hvars0]
  have htR : rVCb tV = tCb := by
    change φV (algebraMap T V (X 1)) = tCb
    rw [AlgHom.map_algebraMap]
    change aeval varsCb (X 1) = tCb
    rw [aeval_X, hvars1]
  have hcoordR (i : Fin n) : rVCb (coordV i) = coordCb i := by
    change φV (algebraMap E V (coordE i)) = coordCb i
    calc φV (algebraMap E V (coordE i))
        = algebraMap T Cb (algebraMap E T (coordE i)) := by
          rw [IsScalarTower.algebraMap_apply E T V (coordE i), AlgHom.map_algebraMap]
      _ = φT (C (coordE i)) := rfl
      _ = ρ (coordE i) := by
          change aeval varsCb (C (coordE i)) = _
          rw [aeval_C]
          rfl
      _ = coordCb i := hρ i
  have hAmap : ∀ x : S.A, rVCb (fAtoV x) = algebraMap S.A Cb x := by
    have hgen (i : Fin nA) : rVCb (fAtoV (a i)) = algebraMap S.A Cb (a i) := by
      change rVCb (algebraMap E V (fAE (a i))) = _
      rw [hgenAE i]
      change rVCb (coordV (rep i)) = _
      rw [hcoordR, hcoordRep]
    let aMapCb : S.A →ₐ[S.R] Cb :=
      { toRingHom := algebraMap S.A Cb
        commutes' := hcoeffCb }
    have hcomp : (rVCb.comp fAtoV).comp (aeval a : MvPolynomial (Fin nA) S.R →ₐ[S.R] S.A) =
        aMapCb.comp (aeval a) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp only [AlgHom.comp_apply, aeval_X]
      exact hgen i
    intro x
    obtain ⟨p, rfl⟩ := ha x
    exact AlgHom.congr_fun hcomp p
  have hcompC : ∀ x : Cr, rVCb (fCV x) = algebraMap Cr Cb x := by
    let gP : P →ₐ[S.A] Cb :=
      { toRingHom := rVCb.toRingHom.comp (fCV.toRingHom.comp mkPC.toRingHom)
        commutes' y := by
          change rVCb (fCV (mkPC (algebraMap S.A P y))) = algebraMap S.A Cb y
          rw [AlgHom.commutes, AlgHom.commutes]
          exact hAmap y }
    have hgP : gP = ηCb := by
      refine MvPolynomial.algHom_ext fun i => ?_
      change rVCb (fCV (mkPC (X i))) = ηCb (X i)
      rw [hfCVmk]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hηVX0, hx0R, hηCbX]
      · refine Fin.lastCases ?_ (fun k => ?_) j
        · rw [hηVT, htR, hηCbX]
        · have hk : (Fin.castSucc (Fin.castSucc k) : Fin (n + 2)) = coordVar k := rfl
          rw [hk, hηVcoord, map_mul, htR, hcoordR, hηCbcoord]
    intro x
    obtain ⟨p, rfl⟩ := hmkPCsurj x
    exact congrArg (fun φ : P →ₐ[S.A] Cb => φ p) hgP
  -- Formal smoothness of `Cr_b` by the retraction, hence `b` is in the singular ideal.
  let : Algebra Cr V := fCV.toRingHom.toAlgebra
  let fCVb : Cb →ₐ[Cr] V :=
    IsLocalization.Away.liftAlgHom (x := b) (A := Cr) (f := Algebra.ofId Cr V) hbV
  let iCbV : Cb →ₐ[S.R] V :=
    { toRingHom := fCVb.toRingHom
      commutes' r := by
        change fCVb (algebraMap Cr Cb (algebraMap S.R Cr r)) = algebraMap S.R V r
        rw [AlgHom.map_algebraMap]
        exact hfCVbase r }
  have hri : rVCb.comp iCbV = AlgHom.id S.R Cb := by
    refine AlgHom.toRingHom_injective ?_
    refine IsLocalization.ringHom_ext (Submonoid.powers b) (RingHom.ext fun x => ?_)
    change rVCb (fCVb (algebraMap Cr Cb x)) = algebraMap Cr Cb x
    rw [AlgHom.map_algebraMap]
    exact hcompC x
  have hFormalCb : Algebra.FormallySmooth S.R Cb :=
    have : Algebra.FormallySmooth S.R V := hSmoothV.formallySmooth
    Algebra.FormallySmooth.of_retract iCbV rVCb hri
  have hCbFP : Algebra.FinitePresentation S.R Cb :=
    have : Algebra.FinitePresentation Cr Cb := IsLocalization.Away.finitePresentation b
    have : Algebra.FinitePresentation S.R Cr := hCfp
    Algebra.FinitePresentation.trans S.R Cr Cb
  have hbSing : b ∈ singularIdeal S.R Cr :=
    mem_singularIdeal_of_smooth_of_isLocalizationAway S.R Cr Cb ⟨hFormalCb, hCbFP⟩
  -- The image of `b` in `Λ` avoids `q`.
  have hbΛ : ηC b = x0 * t * algebraMap S.R S.Λ s *
      aeval (Fin.snoc nums t) (homogenizeLast (jacobianDet hcn fR)) := by
    change ηC (mkPC (X x0Var) * mkPC (X tVar) * algebraMap S.R Cr s * mkPC jacHomA) = _
    rw [map_mul, map_mul, map_mul, hηCmk, hηCmk, hηCmk, hηCcoeff, hηX0, hηT, hmapEvalΛ]
  refine ⟨Cr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsScalarTower.of_algHom ηC, IsScalarTower.of_algHom (ηC.restrictScalars S.R), hCfp, ?_⟩
  intro hle
  have hbq : algebraMap Cr S.Λ b ∈ S.q := hle (Ideal.mem_map_of_mem _ hbSing)
  change ηC b ∈ S.q at hbq
  rw [hbΛ] at hbq
  exact S.isPrimeQ.mul_notMem
    (S.isPrimeQ.mul_notMem (S.isPrimeQ.mul_notMem hx0 ht) hs) hjac hbq

/-- **Stacks 07F9.** Let `R → A → Λ ⊃ q` be a local smoothing situation, `p = R ∩ q`. If `q` is
minimal over `𝔥_A` and the localized chain `R_p → A_p → Λ_q ⊃ q Λ_q` can be resolved, then there
is a factorization `A → C → Λ` with `C` of finite presentation over `R` and
`H_{C/R} Λ ⊄ q`. -/
@[stacks 07F9]
theorem exists_finitePresentation_factorization_singularIdeal_not_le
    (S : LocalSmoothingSituation.{u, v, w})
    (_hq : S.q ∈ S.radicalSingularIdealExtension.minimalPrimes)
    (hresolve : S.IsResolvableAfterLocalizing) :
    ∃ (Cr : Type (max u v w)) (_ : CommRing Cr) (_ : Algebra S.R Cr) (_ : Algebra S.A Cr)
        (_ : Algebra Cr S.Λ),
      IsScalarTower S.R S.A Cr ∧ IsScalarTower S.A Cr S.Λ ∧ IsScalarTower S.R Cr S.Λ ∧
        Algebra.FinitePresentation S.R Cr ∧
        ¬ Ideal.map (algebraMap Cr S.Λ) (singularIdeal S.R Cr) ≤ S.q := by
  obtain ⟨nA, πA, hsurj, hfg⟩ := Algebra.FinitePresentation.out (R := S.R) (A := S.A)
  have hπA : πA = aeval fun i => πA (X i) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp
  rw [hπA] at hsurj hfg
  obtain ⟨n, c, hcn, fR, rep, s, nums, t, x0, hrel, hs, ht, hx0, hbadF, hbadA, hjac⟩ :=
    exists_spreadOut_of_isResolvableAfterLocalizing S (fun i => πA (X i)) hfg hresolve
  obtain ⟨E, iE, aE, coordE, fAE, hEsm, hgenAE, hfRE, hjacE, hsE, hliftE⟩ :=
    exists_smooth_model S (fun i => πA (X i)) hsurj hcn fR rep s hrel
  exact exists_finitePresentation_not_le_of_smoothModel S (fun i => πA (X i)) hsurj hcn fR rep s
    nums t x0 hs ht hx0 hbadF hbadA hjac E iE aE coordE fAE hEsm hgenAE hfRE hjacE hsE hliftE

end Stacks.Smoothing

end
