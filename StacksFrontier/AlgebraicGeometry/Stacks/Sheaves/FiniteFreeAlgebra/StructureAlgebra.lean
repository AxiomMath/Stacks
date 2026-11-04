module

public import Mathlib.LinearAlgebra.StdBasis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Presheaf

/-!
# The algebra of a free algebra structure

A free `d`-dimensional algebra structure `m` over a commutative ring `R` is a table of
structure constants. This file turns it into a commutative `R`-algebra on the free module
`R ^ d` whose unit is the first standard basis vector, and identifies the isomorphisms of
free `d`-dimensional structures with the `R`-algebra isomorphisms of the resulting algebras.

The product is `(x * y) k = ∑ i, ∑ j, x i * y j * m.coeff i j k`, and an isomorphism of
structures acts on coordinates by multiplication by its matrix.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.Carrier`: the free module `R ^ d` carrying the
  multiplication given by the structure constants of `m`, with its commutative ring and
  `R`-algebra structure.
* `AlgebraicGeometry.FiniteFreeAlgebra.Carrier.basisVector` and
  `AlgebraicGeometry.FiniteFreeAlgebra.Carrier.basis`: the standard basis vectors, and the
  basis of the underlying module that they form.
* `AlgebraicGeometry.FiniteFreeAlgebra.StructureIso.toAlgEquiv` and
  `AlgebraicGeometry.FiniteFreeAlgebra.structureIsoOfAlgEquiv`: the algebra isomorphism given
  by the matrix of an isomorphism of structure constants, and its inverse construction.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.Carrier.basis`: the algebra of a free `d`-dimensional
  structure is free of rank `d` over the base ring.
* `AlgebraicGeometry.FiniteFreeAlgebra.structureIsoEquivAlgEquiv`: isomorphisms of free
  `d`-dimensional structures are exactly the `R`-algebra isomorphisms of the associated
  algebras.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R : Type*} [CommRing R] {d : ℕ} [NeZero d]

/-- Three nested finite sums may be rotated cyclically. -/
theorem sum_rotate3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- A product of two finite sums times a constant is the double sum of the products of their
terms times that constant. -/
theorem sum_mul_sum_mul_const {M α β : Type*} [CommRing M] [Fintype α] [Fintype β]
    (A : α → M) (B : β → M) (c : M) :
    (∑ a, A a) * (∑ b, B b) * c = ∑ a, ∑ b, A a * B b * c := by
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum, Finset.sum_mul]

omit [NeZero d] in
/-- A row of an invertible matrix paired against a column of its inverse. -/
theorem gl_mul_inv_sum (g : Matrix.GeneralLinearGroup (Fin d) R) (i j : Fin d) :
    (∑ k, (g : Matrix (Fin d) (Fin d) R) i k *
      (g⁻¹ : Matrix (Fin d) (Fin d) R) k j) = if i = j then 1 else 0 := by
  rw [← Matrix.mul_apply]
  simp [Matrix.one_apply]

omit [NeZero d] in
/-- A row of the inverse of an invertible matrix paired against a column of the matrix. -/
theorem gl_inv_mul_sum (g : Matrix.GeneralLinearGroup (Fin d) R) (i j : Fin d) :
    (∑ k, (g⁻¹ : Matrix (Fin d) (Fin d) R) i k *
      (g : Matrix (Fin d) (Fin d) R) k j) = if i = j then 1 else 0 := by
  rw [← Matrix.mul_apply]
  simp [Matrix.one_apply]

/-- The free module `R ^ d` equipped with the multiplication whose structure constants in the
standard basis are those of `m`. -/
def Carrier (_m : FiniteFreeAlgebra R d) : Type _ := Fin d → R

namespace Carrier

/-- Two elements are equal as soon as all their coordinates agree. -/
@[ext] theorem ext {m : FiniteFreeAlgebra R d} {x y : Carrier m}
    (h : ∀ k, x k = y k) : x = y := funext h

/-- The commutative ring structure on the algebra of `m`: coordinatewise addition, the product
with structure constants `m.coeff`, and the first standard basis vector as unit. -/
instance instCommRing (m : FiniteFreeAlgebra R d) : CommRing (Carrier m) where
  __ := show AddCommGroup (Carrier m) from inferInstanceAs (AddCommGroup (Fin d → R))
  mul x y := (fun k => ∑ i, ∑ j, x i * y j * m.coeff i j k : Fin d → R)
  one := (Pi.single (0 : Fin d) (1 : R) : Fin d → R)
  mul_comm x y := by
    refine ext fun k => ?_
    change (∑ i, ∑ j, x i * y j * m.coeff i j k) = ∑ i, ∑ j, y i * x j * m.coeff i j k
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [m.comm j i k]
    ring
  mul_assoc x y z := by
    refine ext fun k => ?_
    change (∑ l, ∑ q, (∑ i, ∑ j, x i * y j * m.coeff i j l) * z q * m.coeff l q k)
      = ∑ i, ∑ l, x i * (∑ j, ∑ q, y j * z q * m.coeff j q l) * m.coeff i l k
    calc
      (∑ l, ∑ q, (∑ i, ∑ j, x i * y j * m.coeff i j l) * z q * m.coeff l q k)
          = ∑ q, ∑ i, ∑ j, x i * y j * z q * (∑ l, m.coeff i j l * m.coeff l q k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [show (∑ l, (∑ i, ∑ j, x i * y j * m.coeff i j l) * z q * m.coeff l q k)
            = ∑ l, ∑ i, ∑ j, x i * y j * z q * (m.coeff i j l * m.coeff l q k) from
          Finset.sum_congr rfl fun l _ => by
            simp only [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring]
        rw [sum_rotate3 fun l i j => x i * y j * z q * (m.coeff i j l * m.coeff l q k)]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          (Finset.mul_sum _ _ _).symm
      _ = ∑ i, ∑ j, ∑ q, x i * y j * z q * (∑ l, m.coeff i j l * m.coeff l q k) :=
        sum_rotate3 fun q i j => x i * y j * z q * (∑ l, m.coeff i j l * m.coeff l q k)
      _ = ∑ i, ∑ j, ∑ q, x i * y j * z q * (∑ l, m.coeff j q l * m.coeff i l k) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun q _ => ?_
        rw [m.assoc i j q k]
        exact congrArg _ (Finset.sum_congr rfl fun l _ => mul_comm _ _)
      _ = ∑ i, ∑ l, x i * (∑ j, ∑ q, y j * z q * m.coeff j q l) * m.coeff i l k := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (∑ l, x i * (∑ j, ∑ q, y j * z q * m.coeff j q l) * m.coeff i l k)
            = ∑ l, ∑ j, ∑ q, x i * y j * z q * (m.coeff j q l * m.coeff i l k) from
          Finset.sum_congr rfl fun l _ => by
            simp only [Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by ring]
        rw [sum_rotate3 fun l j q => x i * y j * z q * (m.coeff j q l * m.coeff i l k)]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ =>
          Finset.mul_sum _ _ _
  one_mul x := by
    refine ext fun k => ?_
    change (∑ i, ∑ j, (Pi.single (0 : Fin d) (1 : R) : Fin d → R) i * x j * m.coeff i j k) = x k
    rw [Finset.sum_eq_single (0 : Fin d) (fun i _ hi => by simp [hi])
      (fun h => absurd (Finset.mem_univ (0 : Fin d)) h)]
    refine (Finset.sum_eq_single k (fun j _ hj => ?_)
      (fun h => absurd (Finset.mem_univ k) h)).trans ?_
    · rw [m.comm 0 j k, m.unit_coeff j k]
      simp [hj]
    · rw [m.comm 0 k k, m.unit_coeff k k]
      simp
  mul_one x := by
    refine ext fun k => ?_
    change (∑ i, ∑ j, x i * (Pi.single (0 : Fin d) (1 : R) : Fin d → R) j * m.coeff i j k) = x k
    have hinner (i : Fin d) :
        (∑ j, x i * (Pi.single (0 : Fin d) (1 : R) : Fin d → R) j * m.coeff i j k)
          = x i * (if i = k then 1 else 0) := by
      rw [Finset.sum_eq_single (0 : Fin d) (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_univ (0 : Fin d)) h)]
      rw [m.unit_coeff i k]
      simp
    rw [Finset.sum_congr rfl fun i _ => hinner i]
    rw [Finset.sum_eq_single k (fun i _ hi => by simp [hi])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp
  left_distrib x y z := by
    refine ext fun k => ?_
    change (∑ i, ∑ j, x i * (y j + z j) * m.coeff i j k)
      = (∑ i, ∑ j, x i * y j * m.coeff i j k) + ∑ i, ∑ j, x i * z j * m.coeff i j k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  right_distrib x y z := by
    refine ext fun k => ?_
    change (∑ i, ∑ j, (x i + y i) * z j * m.coeff i j k)
      = (∑ i, ∑ j, x i * z j * m.coeff i j k) + ∑ i, ∑ j, y i * z j * m.coeff i j k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  zero_mul x := by
    refine ext fun k => ?_
    change (∑ i, ∑ j, (0 : R) * x j * m.coeff i j k) = (0 : R)
    simp
  mul_zero x := by
    refine ext fun k => ?_
    change (∑ i, ∑ j, x i * (0 : R) * m.coeff i j k) = (0 : R)
    simp

variable {m n : FiniteFreeAlgebra R d}

/-- The coordinates of a product are the bilinear expression in the structure constants. -/
theorem mul_apply (x y : Carrier m) (k : Fin d) :
    (x * y) k = ∑ i, ∑ j, x i * y j * m.coeff i j k := rfl

/-- The unit of the algebra of `m` is the first standard basis vector. -/
theorem one_apply (k : Fin d) : (1 : Carrier m) k = if k = 0 then 1 else 0 := by
  change (Pi.single (0 : Fin d) (1 : R) : Fin d → R) k = _
  simp [Pi.single_apply]

/-- Addition is coordinatewise. -/
theorem add_apply (x y : Carrier m) (k : Fin d) : (x + y) k = x k + y k := rfl

/-- Zero is coordinatewise. -/
theorem zero_apply (k : Fin d) : (0 : Carrier m) k = 0 := rfl

/-- Sums are formed coordinatewise. -/
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Carrier m) (k : Fin d) :
    (∑ i ∈ s, f i) k = ∑ i ∈ s, f i k := Finset.sum_apply k s f

/-- The unit map of the algebra of `m`, sending `r` to `r` times the first basis vector. -/
def unitRingHom (m : FiniteFreeAlgebra R d) : R →+* Carrier m where
  toFun r := (Pi.single (0 : Fin d) r : Fin d → R)
  map_one' := rfl
  map_mul' r s := by
    refine ext fun k => ?_
    change (Pi.single (0 : Fin d) (r * s) : Fin d → R) k
      = ∑ i, ∑ j, (Pi.single (0 : Fin d) r : Fin d → R) i *
          (Pi.single (0 : Fin d) s : Fin d → R) j * m.coeff i j k
    rw [Finset.sum_eq_single (0 : Fin d) (fun i _ hi => by simp [hi])
      (fun h => absurd (Finset.mem_univ (0 : Fin d)) h)]
    rw [Finset.sum_eq_single (0 : Fin d) (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ (0 : Fin d)) h)]
    rw [m.unit_coeff 0 k]
    simp [Pi.single_apply, eq_comm]
  map_zero' := by
    refine ext fun k => ?_
    change (Pi.single (0 : Fin d) (0 : R) : Fin d → R) k = (0 : R)
    simp
  map_add' r s := by
    refine ext fun k => ?_
    change (Pi.single (0 : Fin d) (r + s) : Fin d → R) k
      = (Pi.single (0 : Fin d) r : Fin d → R) k + (Pi.single (0 : Fin d) s : Fin d → R) k
    simp only [Pi.single_apply]
    split <;> simp

/-- The `R`-algebra structure on the algebra of `m`, with structure map `unitRingHom m`. -/
instance instAlgebra (m : FiniteFreeAlgebra R d) : Algebra R (Carrier m) :=
  (unitRingHom m).toAlgebra

/-- The coordinates of the image of a scalar under the unit map. -/
@[simp] theorem unitRingHom_coord (r : R) (k : Fin d) :
    (unitRingHom m r) k = if k = 0 then r else 0 := by
  change (Pi.single (0 : Fin d) r : Fin d → R) k = _
  simp [Pi.single_apply]

/-- The structure map of the algebra of `m` is its unit map. -/
theorem algebraMap_eq (m : FiniteFreeAlgebra R d) :
    algebraMap R (Carrier m) = unitRingHom m :=
  RingHom.algebraMap_toAlgebra (unitRingHom m)

/-- The structure map sends `r` to `r` times the first basis vector. -/
@[simp] theorem algebraMap_coord (r : R) (k : Fin d) :
    (algebraMap R (Carrier m) r) k = if k = 0 then r else 0 := by
  rw [algebraMap_eq, unitRingHom_coord]

/-- Scalars act coordinatewise. -/
theorem smul_apply (r : R) (x : Carrier m) (k : Fin d) : (r • x) k = r * x k := by
  rw [Algebra.smul_def, mul_apply]
  simp only [algebraMap_coord]
  rw [Fintype.sum_eq_single (0 : Fin d) (fun i hi => by simp [hi]),
    Fintype.sum_eq_single k (fun j hj => by rw [m.comm 0 j k, m.unit_coeff j k]; simp [hj]),
    m.comm 0 k k, m.unit_coeff k k]
  simp

/-- The `i`th standard basis vector of the module underlying the algebra of `m`. -/
def basisVector (m : FiniteFreeAlgebra R d) (i : Fin d) : Carrier m :=
  (Pi.single i (1 : R) : Fin d → R)

/-- The `k`th coordinate of the `i`th standard basis vector is `1` if `k = i` and `0`
otherwise. -/
@[simp] theorem basisVector_apply (i k : Fin d) :
    basisVector m i k = if k = i then 1 else 0 := by
  change (Pi.single i (1 : R) : Fin d → R) k = _
  simp [Pi.single_apply]

/-- The unit of the algebra of `m` is the zeroth basis vector. -/
theorem basisVector_zero : basisVector m 0 = 1 := rfl

/-- The product of two basis vectors reads off a row of the structure constants. -/
theorem basisVector_mul_basisVector (i j : Fin d) :
    basisVector m i * basisVector m j = (fun k => m.coeff i j k : Fin d → R) := by
  refine ext fun k => ?_
  rw [mul_apply, Fintype.sum_eq_single i (fun p hp => by simp [hp]),
    Fintype.sum_eq_single j (fun q hq => by simp [hq])]
  simp

/-- An element is the combination of the basis vectors with its own coordinates. -/
theorem sum_smul_basisVector (x : Carrier m) : (∑ i, x i • basisVector m i) = x := by
  refine ext fun k => ?_
  rw [sum_apply, Fintype.sum_eq_single k
    (fun i hi => by rw [smul_apply, basisVector_apply]; simp [Ne.symm hi]),
    smul_apply, basisVector_apply]
  simp

/-- The coordinates of an element, as an `R`-linear equivalence with `R ^ d`. -/
def coordLinearEquiv (m : FiniteFreeAlgebra R d) : Carrier m ≃ₗ[R] (Fin d → R) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    refine funext fun k => ?_
    rw [RingHom.id_apply]
    exact smul_apply r x k

/-- The module underlying the algebra of `m` is free over `R`. -/
instance instFree (m : FiniteFreeAlgebra R d) : Module.Free R (Carrier m) :=
  Module.Free.of_equiv (coordLinearEquiv m).symm

/-- The module underlying the algebra of `m` is finitely generated over `R`. -/
instance instFinite (m : FiniteFreeAlgebra R d) : Module.Finite R (Carrier m) :=
  Module.Finite.equiv (coordLinearEquiv m).symm

/-- The module underlying the algebra of a free `d`-dimensional structure is free with basis the
`d` standard basis vectors. -/
@[stacks 05YQ "the module underlying the algebra of a free `d`-dimensional structure is free \
of rank `d`, the affine core of the degree-`d` clause for the relative spectrum of `m`"]
noncomputable def basis (m : FiniteFreeAlgebra R d) : Module.Basis (Fin d) R (Carrier m) :=
  (Pi.basisFun R (Fin d)).map (coordLinearEquiv m).symm

/-- The `i`th vector of the basis `basis m` is the standard basis vector `basisVector m i`. -/
@[simp] theorem basis_apply (i : Fin d) : basis m i = basisVector m i := by
  simp only [basis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

/-- The coordinates of an element of the algebra of a free `d`-dimensional structure in the
standard basis are its own coordinates. -/
theorem basis_repr_apply (m : FiniteFreeAlgebra R d) (x : Carrier m) (l : Fin d) :
    (basis m).repr x l = x l := rfl

/-- An `R`-linear map out of the algebra of `m` is determined on coordinates by its values on
the standard basis vectors. -/
theorem linearMap_apply_coord (ψ : Carrier m →ₗ[R] Carrier n) (x : Carrier m) (k : Fin d) :
    ψ x k = ∑ i, x i * (ψ (basisVector m i)) k := by
  conv_lhs => rw [← sum_smul_basisVector x]
  rw [map_sum, sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_apply]

/-- The coordinates of an `R`-algebra isomorphism, read off the standard basis vectors. -/
theorem algEquiv_apply_coord (ψ : Carrier m ≃ₐ[R] Carrier n) (x : Carrier m) (k : Fin d) :
    ψ x k = ∑ i, x i * (ψ (basisVector m i)) k :=
  linearMap_apply_coord ψ.toLinearMap x k

end Carrier

open Carrier

/-- The matrix of an isomorphism of free `d`-dimensional structures fixes every multiple of
the first standard basis vector. -/
theorem StructureIso.matrix_mul_single {m n : FiniteFreeAlgebra R d} (e : StructureIso m n)
    (r : R) (k : Fin d) :
    (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i *
        (Pi.single (0 : Fin d) r : Fin d → R) i)
      = (Pi.single (0 : Fin d) r : Fin d → R) k := by
  rw [Fintype.sum_eq_single (0 : Fin d) (fun i hi => by simp [hi]), e.map_unit k]
  simp [Pi.single_apply]

/-- The `R`-algebra isomorphism of the associated algebras given by the matrix of an
isomorphism of free `d`-dimensional structures. -/
noncomputable def StructureIso.toAlgEquiv {m n : FiniteFreeAlgebra R d}
    (e : StructureIso m n) :
    Carrier m ≃ₐ[R] Carrier n where
  toFun x := (fun k => ∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * x i : Fin d → R)
  invFun y := (fun k => ∑ i, (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) k i * y i : Fin d → R)
  left_inv x := by
    refine Carrier.ext fun k => ?_
    change (∑ i, (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) k i *
        ∑ j, (e.matrix : Matrix (Fin d) (Fin d) R) i j * x j) = x k
    calc
      (∑ i, (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) k i *
            ∑ j, (e.matrix : Matrix (Fin d) (Fin d) R) i j * x j)
          = ∑ i, ∑ j, (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) k i *
              (e.matrix : Matrix (Fin d) (Fin d) R) i j * x j :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
      _ = ∑ j, (∑ i, (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) k i *
            (e.matrix : Matrix (Fin d) (Fin d) R) i j) * x j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ = x k := by
        simp only [gl_inv_mul_sum]
        rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj])
          (fun h => absurd (Finset.mem_univ k) h)]
        simp
  right_inv y := by
    refine Carrier.ext fun k => ?_
    change (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i *
        ∑ j, (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) i j * y j) = y k
    calc
      (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i *
            ∑ j, (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) i j * y j)
          = ∑ i, ∑ j, (e.matrix : Matrix (Fin d) (Fin d) R) k i *
              (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) i j * y j :=
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
      _ = ∑ j, (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i *
            (e.matrix⁻¹ : Matrix (Fin d) (Fin d) R) i j) * y j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ = y k := by
        simp only [gl_mul_inv_sum]
        rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj])
          (fun h => absurd (Finset.mem_univ k) h)]
        simp
  map_mul' x y := by
    refine Carrier.ext fun k => ?_
    change (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * ∑ p, ∑ q,
        x p * y q * m.coeff p q i)
      = ∑ u, ∑ v, (∑ a, (e.matrix : Matrix (Fin d) (Fin d) R) u a * x a) *
          (∑ b, (e.matrix : Matrix (Fin d) (Fin d) R) v b * y b) * n.coeff u v k
    calc
      (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * ∑ p, ∑ q, x p * y q * m.coeff p q i)
          = ∑ p, ∑ q, x p * y q * (∑ i, m.coeff p q i *
              (e.matrix : Matrix (Fin d) (Fin d) R) k i) := by
        rw [show (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i *
              ∑ p, ∑ q, x p * y q * m.coeff p q i)
            = ∑ i, ∑ p, ∑ q, x p * y q *
              (m.coeff p q i * (e.matrix : Matrix (Fin d) (Fin d) R) k i) from
          Finset.sum_congr rfl fun i _ => by
            simp only [Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring]
        rw [sum_rotate3 fun i p q => x p * y q *
          (m.coeff p q i * (e.matrix : Matrix (Fin d) (Fin d) R) k i)]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
          (Finset.mul_sum _ _ _).symm
      _ = ∑ p, ∑ q, x p * y q * (∑ u, ∑ v, (e.matrix : Matrix (Fin d) (Fin d) R) u p *
            (e.matrix : Matrix (Fin d) (Fin d) R) v q * n.coeff u v k) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
          congrArg _ (e.map_mul p q k)
      _ = ∑ p, ∑ u, ∑ v, ∑ q, x p * y q *
            ((e.matrix : Matrix (Fin d) (Fin d) R) u p *
              (e.matrix : Matrix (Fin d) (Fin d) R) v q * n.coeff u v k) :=
        Finset.sum_congr rfl fun p _ => by
          rw [show (∑ q, x p * y q * (∑ u, ∑ v,
                (e.matrix : Matrix (Fin d) (Fin d) R) u p *
                  (e.matrix : Matrix (Fin d) (Fin d) R) v q * n.coeff u v k))
              = ∑ q, ∑ u, ∑ v, x p * y q *
                ((e.matrix : Matrix (Fin d) (Fin d) R) u p *
                  (e.matrix : Matrix (Fin d) (Fin d) R) v q * n.coeff u v k) from
            Finset.sum_congr rfl fun q _ => by simp only [Finset.mul_sum]]
          exact sum_rotate3 fun q u v => x p * y q *
            ((e.matrix : Matrix (Fin d) (Fin d) R) u p *
              (e.matrix : Matrix (Fin d) (Fin d) R) v q * n.coeff u v k)
      _ = ∑ u, ∑ v, (∑ a, (e.matrix : Matrix (Fin d) (Fin d) R) u a * x a) *
            (∑ b, (e.matrix : Matrix (Fin d) (Fin d) R) v b * y b) * n.coeff u v k := by
        rw [sum_rotate3 fun p u v => ∑ q, x p * y q *
          ((e.matrix : Matrix (Fin d) (Fin d) R) u p *
            (e.matrix : Matrix (Fin d) (Fin d) R) v q * n.coeff u v k)]
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [sum_mul_sum_mul_const (fun a => (e.matrix : Matrix (Fin d) (Fin d) R) u a * x a)
          (fun b => (e.matrix : Matrix (Fin d) (Fin d) R) v b * y b) (n.coeff u v k)]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  map_add' x y := by
    refine Carrier.ext fun k => ?_
    change (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * (x i + y i))
      = (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * x i) +
        ∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * y i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  commutes' r := Carrier.ext fun k => StructureIso.matrix_mul_single e r k

/-- The matrix, in the standard bases, of an `R`-algebra isomorphism between the algebras of
two free `d`-dimensional structures. -/
def algEquivMatrixVal {m n : FiniteFreeAlgebra R d} (ψ : Carrier m ≃ₐ[R] Carrier n) :
    Matrix (Fin d) (Fin d) R :=
  Matrix.of fun k i => (ψ (basisVector m i)) k

/-- The entries of the matrix of an algebra isomorphism are the coordinates of the images of
the standard basis vectors. -/
theorem algEquivMatrixVal_apply {m n : FiniteFreeAlgebra R d} (ψ : Carrier m ≃ₐ[R] Carrier n)
    (k i : Fin d) : algEquivMatrixVal ψ k i = (ψ (basisVector m i)) k := rfl

/-- The matrices of an algebra isomorphism and of its inverse multiply to the identity. -/
theorem algEquivMatrixVal_mul_symm {m n : FiniteFreeAlgebra R d}
    (ψ : Carrier m ≃ₐ[R] Carrier n) :
    algEquivMatrixVal ψ * algEquivMatrixVal ψ.symm = 1 := by
  refine Matrix.ext fun k i => ?_
  have h := algEquiv_apply_coord ψ (ψ.symm (basisVector n i)) k
  rw [ψ.apply_symm_apply, basisVector_apply] at h
  rw [Matrix.mul_apply, Matrix.one_apply, h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The matrix of an `R`-algebra isomorphism, as an invertible matrix. -/
def algEquivGL {m n : FiniteFreeAlgebra R d} (ψ : Carrier m ≃ₐ[R] Carrier n) :
    Matrix.GeneralLinearGroup (Fin d) R where
  val := algEquivMatrixVal ψ
  inv := algEquivMatrixVal ψ.symm
  val_inv := algEquivMatrixVal_mul_symm ψ
  inv_val := by
    have h := algEquivMatrixVal_mul_symm ψ.symm
    rwa [ψ.symm_symm] at h

/-- The matrix of the algebra isomorphism attached to an isomorphism of structures is the
matrix of that isomorphism. -/
theorem algEquivMatrixVal_toAlgEquiv {m n : FiniteFreeAlgebra R d} (e : StructureIso m n) :
    algEquivMatrixVal e.toAlgEquiv = (e.matrix : Matrix (Fin d) (Fin d) R) := by
  refine Matrix.ext fun k i => ?_
  change ∑ j, (e.matrix : Matrix (Fin d) (Fin d) R) k j * (Pi.single i (1 : R) : Fin d → R) j = _
  rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
  simp

/-- The isomorphism of free `d`-dimensional structures underlying an `R`-algebra isomorphism
of the two associated algebras: its matrix in the standard bases. -/
def structureIsoOfAlgEquiv {m n : FiniteFreeAlgebra R d} (ψ : Carrier m ≃ₐ[R] Carrier n) :
    StructureIso m n where
  matrix := algEquivGL ψ
  map_unit k := by
    change (ψ (basisVector m 0)) k = _
    rw [basisVector_zero, map_one, one_apply]
  map_mul i j k := by
    change (∑ l, m.coeff i j l * (ψ (basisVector m l)) k)
      = ∑ p, ∑ q, (ψ (basisVector m i)) p * (ψ (basisVector m j)) q * n.coeff p q k
    have h := algEquiv_apply_coord ψ (basisVector m i * basisVector m j) k
    rw [map_mul, mul_apply, basisVector_mul_basisVector] at h
    exact h.symm

/-- The isomorphisms of two free `d`-dimensional structures over a ring are exactly the
`R`-algebra isomorphisms of the two associated algebras. -/
@[stacks 05YQ "clause (a) of the proof, in algebraic form: the isomorphisms of two free \
`d`-dimensional structures are exactly the algebra isomorphisms of the associated algebras"]
noncomputable def structureIsoEquivAlgEquiv (m n : FiniteFreeAlgebra R d) :
    StructureIso m n ≃ (Carrier m ≃ₐ[R] Carrier n) where
  toFun e := e.toAlgEquiv
  invFun ψ := structureIsoOfAlgEquiv ψ
  left_inv e := StructureIso.ext (Units.ext (algEquivMatrixVal_toAlgEquiv e))
  right_inv ψ := by
    refine AlgEquiv.ext fun x => Carrier.ext fun k => ?_
    have h : ((structureIsoOfAlgEquiv ψ).toAlgEquiv x) k
        = ∑ i, (ψ (basisVector m i)) k * x i := rfl
    rw [h]
    exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans
      (algEquiv_apply_coord ψ x k).symm

end AlgebraicGeometry.FiniteFreeAlgebra

end
