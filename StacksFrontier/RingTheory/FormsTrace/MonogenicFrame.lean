module

public import StacksFrontier.RingTheory.FormsTrace.FramedCanonical
public import StacksCore.RingTheory.Polynomial.FreeQuotient
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection

/-!
# Monogenic frames

A finite free algebra with a power basis `1, x, …, x ^ (d - 1)` carries a canonical frame
(`Stacks.FormsTrace.ChartFrame`), with no localization: the syntomic-good element is the
*monogenicity determinant* `g_mono ∈ A_d`, the determinant of the coordinates of the powers
`e₁ ^ k` of the second universal basis vector.  On `D(g_mono)` the universal algebra is generated
by `e₁`, so it is `N[x]/(χ)` for a monic `χ`, a relative global complete intersection, hence
syntomic; and on a power basis the classifying map sends `g_mono` to `det 1 = 1`.

## Main definitions

* `Stacks.FormsTrace.monoDet`: the monogenicity determinant of a table.
* `Stacks.FormsTrace.monogenicGood`: the element `g_mono` of the universal ring.
* `Stacks.FormsTrace.monogenicFrame`: the frame of an algebra with a power basis.

## Main results

* `Stacks.FormsTrace.syntomic_of_isUnit_monoDet`: a table with unit monogenicity determinant is
  syntomic.
* `Stacks.FormsTrace.isSyntomicGood_monogenicGood`: `g_mono` is syntomic-good.

## References

* [Stacks Project, Tag 0FL4](https://stacks.math.columbia.edu/tag/0FL4)
* [Stacks Project, Tag 00SW](https://stacks.math.columbia.edu/tag/00SW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra Polynomial

universe u

namespace Stacks.FormsTrace

section Monogenic

/-- A monic monogenic algebra has a square presentation. -/
theorem exists_presentation_adjoinRoot (A : Type u) [CommRing A] (P : A[X]) :
    ∃ m : ℕ, Nonempty (Algebra.Presentation A (AdjoinRoot P) (Fin m) (Fin m)) := by
  let e : MvPolynomial (Fin 1) A ≃ₐ[A] A[X] := MvPolynomial.uniqueAlgEquiv A (Fin 1)
  refine ⟨1, ⟨(Algebra.Presentation.naive (v := fun _ : Fin 1 => e.symm P)).ofAlgEquiv
    (Ideal.quotientEquivAlg _ (Ideal.span {P}) e ?_)⟩⟩
  rw [Ideal.map_span]
  simp

/-- A finite algebra with a square presentation is a relative global complete intersection. -/
theorem isRelativeGlobalCompleteIntersection_of_presentation (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] {m : ℕ}
    (P : Algebra.Presentation A B (Fin m) (Fin m)) :
    Algebra.IsRelativeGlobalCompleteIntersection A B := by
  refine ⟨m, m, P, ⟨fun p _ _ => ?_⟩⟩
  have : Module.Finite p.ResidueField (p.Fiber B) := inferInstance
  have : IsArtinianRing (p.Fiber B) := IsArtinianRing.of_finite p.ResidueField _
  rw [ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance]
  simp

/-- `A[x]/(P)` is syntomic over `A` for a monic `P`. -/
theorem syntomic_adjoinRoot (A : Type u) [CommRing A] (P : A[X]) (hP : P.Monic) :
    Algebra.Syntomic A (AdjoinRoot P) := by
  have : Module.Finite A (AdjoinRoot P) := hP.finite_adjoinRoot
  obtain ⟨m, ⟨pres⟩⟩ := exists_presentation_adjoinRoot A P
  have := isRelativeGlobalCompleteIntersection_of_presentation A (AdjoinRoot P) pres
  exact Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A (AdjoinRoot P)

/-- An algebra with a power basis is syntomic. -/
theorem syntomic_of_powerBasis {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (pb : PowerBasis A B) : Algebra.Syntomic A B := by
  have := syntomic_adjoinRoot A pb.minpolyGen pb.minpolyGen_monic
  refine Stacks.SyntomicLocus.Algebra.Syntomic.of_algEquiv
    (AdjoinRoot.equiv' pb.minpolyGen pb ?_ pb.aeval_minpolyGen)
  rw [← pb.minpolyGen_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

end Monogenic

section Determinant

variable {d : ℕ} [NeZero d]

/-- **The monogenicity determinant** of a table `m` at `i`: the determinant of the coordinates
of the powers `e_i ^ k`, `k < d`, of the `i`-th basis vector of its algebra. -/
def monoDet {R : Type*} [CommRing R] (m : FiniteFreeAlgebra R d) (i : Fin d) : R :=
  (Matrix.of fun k l : Fin d => (Carrier.basisVector m i ^ (k : ℕ)) l).det

/-- Coordinates of powers of a basis vector commute with extension of scalars. -/
theorem map_basisVector_pow_apply {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : FiniteFreeAlgebra R d) (i : Fin d) (k : ℕ) (l : Fin d) :
    φ ((Carrier.basisVector m i ^ k) l) = (Carrier.basisVector (m.map φ) i ^ k) l := by
  induction k generalizing l with
  | zero =>
      rw [pow_zero, pow_zero, Carrier.one_apply, Carrier.one_apply]
      split <;> simp
  | succ k ih =>
      rw [pow_succ, pow_succ, Carrier.mul_apply, Carrier.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, map_mul, ih, Carrier.basisVector_apply, Carrier.basisVector_apply]
      simp only [FiniteFreeAlgebra.map_coeff]
      split <;> simp

/-- The monogenicity determinant commutes with extension of scalars. -/
theorem map_monoDet {R : Type*} {S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (m : FiniteFreeAlgebra R d) (i : Fin d) : φ (monoDet m i) = monoDet (m.map φ) i := by
  unfold monoDet
  rw [RingHom.map_det]
  congr 1
  ext k l
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply,
    map_basisVector_pow_apply]

/-- On the table of a basis, the monogenicity determinant is the determinant of the coordinates of
the powers of the `i`-th basis vector. -/
theorem monoDet_ofBasis {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) (i : Fin d) :
    monoDet (ofBasis b hb) i = (Matrix.of fun k l : Fin d => b.repr (b i ^ (k : ℕ)) l).det := by
  unfold monoDet
  congr 1
  ext k l
  have hi : algEquivCarrierOfBasis b hb (b i) = Carrier.basisVector (ofBasis b hb) i :=
    Carrier.ext fun j => by
      rw [Carrier.basisVector_apply]
      change b.repr (b i) j = _
      rw [b.repr_self_apply]
      exact if_congr eq_comm rfl rfl
  rw [Matrix.of_apply, Matrix.of_apply, ← hi, ← map_pow]
  rfl

/-- **A table with unit monogenicity determinant is syntomic**: the powers of `e_i` form a basis,
so the algebra is `R[x]/(χ)` for a monic `χ`. -/
theorem syntomic_of_isUnit_monoDet {R : Type u} [CommRing R] (m : FiniteFreeAlgebra R d)
    (i : Fin d) (h : IsUnit (monoDet m i)) : Algebra.Syntomic R (Carrier m) := by
  let e := Carrier.basis m
  let v : Fin d → Carrier m := fun k => Carrier.basisVector m i ^ (k : ℕ)
  have hdet : IsUnit (e.det v) := by
    rw [Module.Basis.det_apply]
    have ht : e.toMatrix v = (Matrix.of fun k l : Fin d =>
        (Carrier.basisVector m i ^ (k : ℕ)) l).transpose := by
      ext l k
      rw [Module.Basis.toMatrix_apply, Matrix.transpose_apply, Matrix.of_apply,
        Carrier.basis_repr_apply]
    rwa [ht, Matrix.det_transpose]
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det e).mpr hdet
  exact syntomic_of_powerBasis
    { gen := Carrier.basisVector m i
      dim := d
      basis := Module.Basis.mk hli hsp.ge
      basis_eq_pow := fun k => Module.Basis.mk_apply hli hsp.ge k }

variable (d) in
/-- **The monogenicity element** `g_mono ∈ A_d`: the monogenicity determinant, at the second basis
vector, of the universal table. -/
def monogenicGood : universalRing d :=
  monoDet (tableOfHom (RingHom.id (universalRing d))) 1

/-- The classifying map of a table sends `g_mono` to the monogenicity determinant of the table. -/
theorem classify_monogenicGood {R : Type*} [CommRing R] (m : FiniteFreeAlgebra R d) :
    m.classify (monogenicGood d) = monoDet m 1 := by
  rw [monogenicGood, map_monoDet, map_tableOfHom, RingHom.comp_id, tableOfHom_classify]

/-- **`g_mono` is syntomic-good**: over `A_d[1/g_mono]` the universal algebra has the power basis
`1, e₁, …, e₁ ^ (d - 1)`. -/
theorem isSyntomicGood_monogenicGood : IsSyntomicGood.{u} d (monogenicGood d) := by
  rw [isSyntomicGood_iff]
  refine syntomic_of_isUnit_monoDet _ 1 ?_
  have h := map_monoDet (universalChartBaseClassify.{u} (monogenicGood d))
    (tableOfHom (RingHom.id (universalRing d))) 1
  rw [map_tableOfHom, RingHom.comp_id] at h
  rw [← h]
  exact IsLocalization.Away.algebraMap_isUnit (ULift.up (monogenicGood d))

end Determinant

section Frame

variable {d : ℕ} [NeZero d] {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The basis of a power basis of dimension `d`, indexed by `Fin d`. -/
def powerBasisFin (pb : PowerBasis A B) (hd : pb.dim = d) : Module.Basis (Fin d) A B :=
  pb.basis.reindex (finCongr hd)

omit [NeZero d] in
/-- The `k`-th vector of `powerBasisFin pb hd` is `pb.gen ^ k`. -/
theorem powerBasisFin_apply (pb : PowerBasis A B) (hd : pb.dim = d) (k : Fin d) :
    powerBasisFin pb hd k = pb.gen ^ (k : ℕ) := by
  rw [powerBasisFin, Module.Basis.reindex_apply, pb.basis_eq_pow]
  rfl

/-- The `0`-th vector of `powerBasisFin pb hd` is `1`. -/
theorem powerBasisFin_zero (pb : PowerBasis A B) (hd : pb.dim = d) :
    powerBasisFin pb hd 0 = 1 := by
  rw [powerBasisFin_apply, Fin.val_zero, pow_zero]

/-- On a power basis of dimension at least two the classifying map sends `g_mono` to `1`. -/
theorem classify_monogenicGood_powerBasis (pb : PowerBasis A B) (hd : pb.dim = d) (h2 : 1 < d) :
    (ofBasis (powerBasisFin pb hd) (powerBasisFin_zero pb hd)).classify (monogenicGood d) = 1 := by
  rw [classify_monogenicGood, monoDet_ofBasis]
  have h1 : powerBasisFin pb hd 1 = pb.gen := by
    rw [powerBasisFin_apply, Fin.val_one', Nat.mod_eq_of_lt h2, pow_one]
  have hM : (Matrix.of fun k l : Fin d =>
      (powerBasisFin pb hd).repr (powerBasisFin pb hd 1 ^ (k : ℕ)) l) = 1 := by
    ext k l
    rw [Matrix.of_apply, h1, ← powerBasisFin_apply pb hd k, Module.Basis.repr_self,
      Finsupp.single_apply, Matrix.one_apply]
  rw [hM, Matrix.det_one]

/-- **The monogenic frame** of an algebra with a power basis of dimension `d ≥ 2`: the power
basis, with the syntomic-good element `g_mono`, whose classifying image is `1`. -/
def monogenicFrame (pb : PowerBasis A B) (hd : pb.dim = d) (h2 : 1 < d) : ChartFrame d A B where
  basis := powerBasisFin pb hd
  basis_zero := powerBasisFin_zero pb hd
  g := monogenicGood d
  good := isSyntomicGood_monogenicGood
  isUnit := by simp [classify_monogenicGood_powerBasis pb hd h2]

end Frame

end Stacks.FormsTrace
