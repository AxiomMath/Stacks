module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalClassify
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSyntomicOpen
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalTable

/-!
# The functor of points of the universal finite free family and of its syntomic locus

The total space `Y_d` of the universal finite free family `pi_d : Y_d ⟶ X_d` of rank `d`
(Tag 0FKZ) is the spectrum of the free carrier `B_d`, so a point of `Y_d` over a ring `R` is a
ring map `B_d → R`. Such a map is the same datum as a multiplication table on `R ^ d` together
with the coordinates of a section of the algebra that table defines. Consequently a point of
`V_d = pi_d^{-1}(U_d)`, where `U_d` is the open of Tag 0FL0 over which the family is syntomic, is
a multiplication table whose classifying morphism factors through `U_d` together with a section
of the resulting algebra.

## Main definitions

* `AlgebraicGeometry.PointedFiniteFreeAlgebra`: a multiplication table together with the
  coordinates of a section of its algebra.
* `AlgebraicGeometry.PointedFiniteFreeAlgebra.sec`: the section itself.
* `AlgebraicGeometry.universalSyntomicPreimage`: the open subscheme `V_d = pi_d^{-1}(U_d)`.

## Main results

* `AlgebraicGeometry.universalCarrierHomEquiv`: ring maps out of `B_d` are multiplication tables
  with a section.
* `AlgebraicGeometry.pointedFamilyEquiv`: the functor of points of `Y_d`.
* `AlgebraicGeometry.pointedSyntomicEquiv`: the functor of points of `V_d`.

## Implementation notes

A ring map `B_d → R` restricts along `A_d → B_d` to a ring map `c : A_d → R`, which is the
classifying map of the table of its values on the universal structure constants
(`AlgebraicGeometry.FiniteFreeAlgebra.classify_tableOfHom`), and it is determined by `c` together
with its values on the distinguished basis vectors, because `B_d` is free on them over `A_d`
(`AlgebraicGeometry.universalCarrier_eq_sum`). Those values are the coordinates of a section
exactly because the basis vectors multiply by the table. The ring map is reassembled as the
composite of the coordinatewise classifying map `B_d → Carrier m` of Tag 05YQ with the section,
which is where the multiplicativity computation happens once and for all.

At the level of schemes the identification is the `Γ`–`Spec` adjunction, in the form
`AlgebraicGeometry.eq_toSpecΓ_comp`: a morphism to an affine scheme is recovered from its map on
global sections. The table attached to a point of `Y_d` is the point of `X_d` below it under the
representability of Tag 05YM, and the coordinates are its values on the coordinate basis of
`Y_d`.

## References

* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
  AlgebraicGeometry.FiniteFreeAlgebra

open scoped BigOperators

universe u

namespace AlgebraicGeometry

/-- A multiplication table on a free module of rank `d` over `R`, together with the coordinates
of a section of the algebra it defines. -/
structure PointedFiniteFreeAlgebra (R : Type*) [CommRing R] (d : ℕ) [NeZero d] where
  /-- The multiplication table. -/
  table : FiniteFreeAlgebra R d
  /-- The image of the `i`th basis vector under the section. -/
  coord : Fin d → R
  /-- The section sends the unit, the zeroth basis vector, to the unit. -/
  coord_zero : coord 0 = 1
  /-- The section is multiplicative on the basis vectors. -/
  coord_mul : ∀ i j, coord i * coord j = ∑ k, table.coeff i j k * coord k

namespace PointedFiniteFreeAlgebra

/-- A pointed table is determined by its table and the coordinates of its section. -/
@[ext] theorem ext {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    {p q : PointedFiniteFreeAlgebra R d} (ht : p.table = q.table)
    (hc : p.coord = q.coord) : p = q := by
  cases p
  cases q
  subst ht
  subst hc
  rfl

/-- Extension of scalars of a pointed table along a ring map. -/
def map {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S)
    (p : PointedFiniteFreeAlgebra R d) : PointedFiniteFreeAlgebra S d where
  table := FiniteFreeAlgebra.map f p.table
  coord i := f (p.coord i)
  coord_zero := by rw [p.coord_zero, map_one]
  coord_mul i j := by
    rw [← map_mul, p.coord_mul i j, map_sum]
    exact Finset.sum_congr rfl fun k _ => map_mul f _ _

/-- The table of the extension of scalars of a pointed table is the extended table. -/
@[simp] theorem map_table {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (p : PointedFiniteFreeAlgebra R d) :
    (p.map f).table = FiniteFreeAlgebra.map f p.table := rfl

/-- The coordinates of the extension of scalars of a pointed table are the images of the
coordinates. -/
@[simp] theorem map_coord {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (p : PointedFiniteFreeAlgebra R d) (i : Fin d) :
    (p.map f).coord i = f (p.coord i) := rfl

section Sec

variable {R : Type*} [CommRing R] {d : ℕ} [NeZero d]

/-- The section of the algebra of the table that a pointed table carries: the `R`-algebra map
reading off the combination of the coordinates. -/
def sec (p : PointedFiniteFreeAlgebra R d) : Carrier p.table →ₐ[R] R where
  toFun x := ∑ i, x i * p.coord i
  map_one' := by
    simp only [Carrier.one_apply]
    rw [Fintype.sum_eq_single (0 : Fin d) fun i hi => by simp [hi]]
    simp [p.coord_zero]
  map_mul' x y := by
    have hterm : ∀ k : Fin d, (x * y) k * p.coord k =
        ∑ i, ∑ j, x i * y j * (p.table.coeff i j k * p.coord k) := by
      intro k
      rw [Carrier.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    calc ∑ k, (x * y) k * p.coord k
        = ∑ k, ∑ i, ∑ j, x i * y j * (p.table.coeff i j k * p.coord k) :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = ∑ i, ∑ j, ∑ k, x i * y j * (p.table.coeff i j k * p.coord k) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, x i * y j * (p.coord i * p.coord j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, ← p.coord_mul i j]
      _ = (∑ i, x i * p.coord i) * ∑ j, y j * p.coord j := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  map_zero' := by simp [Carrier.zero_apply]
  map_add' x y := by
    change ∑ i, (x + y) i * p.coord i = (∑ i, x i * p.coord i) + ∑ i, y i * p.coord i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Carrier.add_apply, add_mul]
  commutes' r := by
    change ∑ i, (algebraMap R (Carrier p.table) r) i * p.coord i = r
    simp only [Carrier.algebraMap_coord]
    rw [Fintype.sum_eq_single (0 : Fin d) fun i hi => by simp [hi]]
    simp [p.coord_zero]

/-- The section sends an element to the combination of the coordinates with its coefficients. -/
@[simp] theorem sec_apply (p : PointedFiniteFreeAlgebra R d) (x : Carrier p.table) :
    p.sec x = ∑ i, x i * p.coord i := rfl

/-- The section reads off the coordinates on the standard basis vectors. -/
@[simp] theorem sec_basisVector (p : PointedFiniteFreeAlgebra R d) (i : Fin d) :
    p.sec (Carrier.basisVector p.table i) = p.coord i := by
  rw [sec_apply]
  simp only [Carrier.basisVector_apply]
  rw [Fintype.sum_eq_single i fun j hj => by simp [hj]]
  simp

end Sec

/-- An algebra that is free on a basis whose first vector is the unit, together with a section of
it, is a pointed table. -/
def ofBasisSection {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ} [NeZero d]
    (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) (τ : A →ₐ[R] R) :
    PointedFiniteFreeAlgebra R d where
  table := FiniteFreeAlgebra.ofBasis b hb
  coord i := τ (b i)
  coord_zero := by rw [hb, map_one]
  coord_mul i j := by
    rw [← map_mul]
    conv_lhs => rw [← b.sum_repr (b i * b j)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [FiniteFreeAlgebra.ofBasis_coeff, Algebra.smul_def, map_mul, AlgHom.commutes]
    simp

/-- The table of `ofBasisSection b hb τ` is the multiplication table of the basis `b`. -/
@[simp] theorem ofBasisSection_table {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {d : ℕ} [NeZero d] (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) (τ : A →ₐ[R] R) :
    (ofBasisSection b hb τ).table = FiniteFreeAlgebra.ofBasis b hb := rfl

/-- The coordinates of `ofBasisSection b hb τ` are the values of `τ` on the basis `b`. -/
@[simp] theorem ofBasisSection_coord {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {d : ℕ} [NeZero d] (b : Module.Basis (Fin d) R A) (hb : b 0 = 1) (τ : A →ₐ[R] R)
    (i : Fin d) : (ofBasisSection b hb τ).coord i = τ (b i) := rfl

end PointedFiniteFreeAlgebra

namespace FiniteFreeAlgebra

variable {R : Type*} [CommRing R] {d : ℕ} [NeZero d]

/-- The first standard basis vector of the algebra of a table is its unit. -/
theorem Carrier.basis_zero (m : FiniteFreeAlgebra R d) : Carrier.basis m 0 = 1 := by
  rw [Carrier.basis_apply]
  exact Carrier.basisVector_zero

/-- The multiplication table of the standard basis of the algebra of a table is that table. -/
theorem ofBasis_carrierBasis (m : FiniteFreeAlgebra R d) :
    ofBasis (Carrier.basis m) (Carrier.basis_zero m) = m := by
  refine ext_coeff fun i j k => ?_
  rw [ofBasis_coeff, Carrier.basis_repr_apply, Carrier.basis_apply, Carrier.basis_apply,
    Carrier.basisVector_mul_basisVector]

/-- The multiplication table of the values of a ring map out of the universal coefficient ring on
the universal structure constants. -/
def tableOfHom (c : universalRing d →+* R) : FiniteFreeAlgebra R d where
  coeff i j k := c (universalStructureConstant d i j k)
  assoc i j k n := by
    simpa only [map_sum, map_mul] using congrArg c (universalStructureConstant_assoc d i j k n)
  comm i j k := congrArg c (universalStructureConstant_comm d i j k)
  unit_coeff i j := by
    rw [show c (universalStructureConstant d i 0 j) = c (if i = j then 1 else 0) from
      congrArg c (universalStructureConstant_unit d i j), apply_ite c, map_one, map_zero]

/-- The coefficients of `tableOfHom c` are the values of `c` on the structure constants. -/
@[simp] theorem tableOfHom_coeff (c : universalRing d →+* R) (i j k : Fin d) :
    (tableOfHom c).coeff i j k = c (universalStructureConstant d i j k) := rfl

/-- Every ring map out of the universal coefficient ring is the classifying map of the table of
its values on the universal structure constants. -/
theorem classify_tableOfHom (c : universalRing d →+* R) : (tableOfHom c).classify = c := by
  refine Ideal.Quotient.ringHom_ext ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
  · change (tableOfHom c).classify (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      c (Ideal.Quotient.mk _ (MvPolynomial.C r))
    rw [show (MvPolynomial.C r : MvPolynomial (CoeffIndex d) ℤ) =
      (r : MvPolynomial (CoeffIndex d) ℤ) from
        (map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial (CoeffIndex d) ℤ) r).symm]
    simp
  · change (tableOfHom c).classify (universalStructureConstant d q.1 q.2.1 q.2.2) =
      c (universalStructureConstant d q.1 q.2.1 q.2.2)
    rw [classify_universalStructureConstant, tableOfHom_coeff]

/-- Two ring maps out of the universal coefficient ring with the same table agree. -/
theorem hom_ext_of_tableOfHom_eq {c c' : universalRing d →+* R}
    (h : tableOfHom c = tableOfHom c') : c = c' := by
  rw [← classify_tableOfHom c, ← classify_tableOfHom c', h]

end FiniteFreeAlgebra

section Carrier

variable {R : Type*} [CommRing R] {d : ℕ} [NeZero d]

/-- A coordinate of a sum in the universal free carrier is the sum of the coordinates. -/
theorem universalCarrier_sum_coeff (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    {ι : Type*} (t : Finset ι) (f : ι → UniversalFiniteFreeModule d) (k : Fin d) :
    letI := s.ring
    (∑ i ∈ t, f i).coeff k = ∑ i ∈ t, (f i).coeff k := by
  let := s.ring
  exact map_sum
    ({ toFun := fun x : UniversalFiniteFreeModule d => x.coeff k
       map_zero' := s.zero_coeff k
       map_add' := fun x y => s.add_coeff x y k } : UniversalFiniteFreeModule d →+ universalRing d)
    f t

/-- A coordinate of a product in the universal free carrier is the sum over the structure
constants. -/
private theorem universalCarrier_mul_coeff (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (x y : letI := s.ring; UniversalFiniteFreeModule d) (k : Fin d) :
    letI := s.ring
    (x * y).coeff k = ∑ p, ∑ q, x.coeff p * y.coeff q * universalStructureConstant d p q k := by
  let := s.ring
  exact congrArg (·.coeff k) (s.mul_eq x y)

/-- A scalar multiple of a distinguished basis vector of the universal free carrier has that
scalar in the corresponding coordinate. -/
theorem universalCarrier_algebraMap_mul_basisVector_coeff (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) (a : universalRing d) (i k : Fin d) :
    letI := s.ring
    letI := s.algebra
    (algebraMap (universalRing d) (UniversalFiniteFreeModule d) a *
      universalBasisVector d i).coeff k = a * (if i = k then 1 else 0) := by
  classical
  let := s.ring
  let := s.algebra
  simp [universalCarrier_mul_coeff d s, universalBasisVector, s.algebraMap_coeff,
    universalStructureConstant_zero_left]

/-- The product of two distinguished basis vectors of the universal free carrier has the
universal structure constants as its coordinates. -/
theorem universalCarrier_basisVector_mul_coeff (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) (i j k : Fin d) :
    letI := s.ring
    (universalBasisVector d i * universalBasisVector d j).coeff k =
      universalStructureConstant d i j k := by
  classical
  let := s.ring
  simp [universalCarrier_mul_coeff d s, universalBasisVector]

/-- An element of the universal free carrier is the combination of the distinguished basis
vectors with its own coordinates. -/
theorem universalCarrier_eq_sum (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (x : UniversalFiniteFreeModule d) :
    letI := s.ring
    letI := s.algebra
    x = ∑ i, algebraMap (universalRing d) (UniversalFiniteFreeModule d) (x.coeff i) *
      universalBasisVector d i := by
  classical
  let := s.ring
  let := s.algebra
  refine (universalCarrier_ext fun k => ?_).symm
  rw [universalCarrier_sum_coeff d s, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    universalCarrier_algebraMap_mul_basisVector_coeff d s (x.coeff i) i k,
    Fintype.sum_eq_single k fun i hi => by simp [hi]]
  simp

/-- The coordinatewise classifying ring map of the universal free carrier onto the algebra of a
multiplication table: the base change of the universal family along the classifying map. -/
def universalCarrierClassify (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (m : FiniteFreeAlgebra R d) :
    letI := s.ring
    UniversalFiniteFreeModule d →+* Carrier m := by
  letI := s.ring
  refine
    { toFun := fun x => (fun k => m.classify (x.coeff k) : Carrier m)
      map_one' := Carrier.ext fun k => ?_
      map_mul' := fun x y => Carrier.ext fun k => ?_
      map_zero' := Carrier.ext fun k => ?_
      map_add' := fun x y => Carrier.ext fun k => ?_ }
  · change m.classify ((1 : UniversalFiniteFreeModule d).coeff k) = (1 : Carrier m) k
    rw [Carrier.one_apply, s.one_eq]
    change m.classify (if (0 : Fin d) = k then 1 else 0) = _
    rw [apply_ite m.classify, map_one, map_zero]
    exact if_congr eq_comm rfl rfl
  · change m.classify ((x * y).coeff k) =
      ∑ i, ∑ j, m.classify (x.coeff i) * m.classify (y.coeff j) * m.coeff i j k
    rw [s.mul_eq]
    change m.classify (∑ i, ∑ j, x.coeff i * y.coeff j * universalStructureConstant d i j k) =
      ∑ i, ∑ j, m.classify (x.coeff i) * m.classify (y.coeff j) * m.coeff i j k
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, classify_universalStructureConstant]
  · change m.classify ((0 : UniversalFiniteFreeModule d).coeff k) = (0 : R)
    rw [s.zero_coeff k, map_zero]
  · change m.classify ((x + y).coeff k) = m.classify (x.coeff k) + m.classify (y.coeff k)
    rw [s.add_coeff, map_add]

/-- The coordinatewise classifying map classifies each coordinate. -/
@[simp] theorem universalCarrierClassify_apply (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) (m : FiniteFreeAlgebra R d)
    (x : letI := s.ring; UniversalFiniteFreeModule d) (k : Fin d) :
    letI := s.ring
    universalCarrierClassify d s m x k = m.classify (x.coeff k) := rfl

/-- The coordinatewise classifying map carries a scalar to its classified image. -/
theorem universalCarrierClassify_algebraMap (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (m : FiniteFreeAlgebra R d) (a : universalRing d) :
    letI := s.ring
    letI := s.algebra
    universalCarrierClassify d s m
        (algebraMap (universalRing d) (UniversalFiniteFreeModule d) a) =
      algebraMap R (Carrier m) (m.classify a) := by
  let := s.ring
  let := s.algebra
  refine Carrier.ext fun k => ?_
  rw [universalCarrierClassify_apply, s.algebraMap_coeff, Carrier.algebraMap_coord,
    apply_ite m.classify, map_zero]

/-- The coordinatewise classifying map carries a distinguished basis vector to the standard
one. -/
theorem universalCarrierClassify_basisVector (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (m : FiniteFreeAlgebra R d) (i : Fin d) :
    letI := s.ring
    universalCarrierClassify d s m (universalBasisVector d i) = Carrier.basisVector m i := by
  let := s.ring
  refine Carrier.ext fun k => ?_
  rw [universalCarrierClassify_apply, Carrier.basisVector_apply]
  change m.classify (if i = k then 1 else 0) = _
  rw [apply_ite m.classify, map_one, map_zero]
  exact if_congr eq_comm rfl rfl

/-- The ring map out of the universal free carrier determined by a pointed table: the
coordinatewise classifying map of the table followed by the section. -/
def universalCarrierSectionHom (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (p : PointedFiniteFreeAlgebra R d) :
    letI := s.ring
    UniversalFiniteFreeModule d →+* R :=
  letI := s.ring
  (p.sec : Carrier p.table →+* R).comp (universalCarrierClassify d s p.table)

/-- The ring map determined by a pointed table carries a scalar to its image under the classifying
map of the table. -/
theorem universalCarrierSectionHom_algebraMap (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) (p : PointedFiniteFreeAlgebra R d) (a : universalRing d) :
    letI := s.ring
    letI := s.algebra
    universalCarrierSectionHom d s p
        (algebraMap (universalRing d) (UniversalFiniteFreeModule d) a) =
      p.table.classify a := by
  let := s.ring
  let := s.algebra
  change p.sec (universalCarrierClassify d s p.table _) = _
  rw [universalCarrierClassify_algebraMap, AlgHom.commutes]
  simp

/-- The ring map determined by a pointed table carries a distinguished basis vector to the
corresponding coordinate. -/
theorem universalCarrierSectionHom_basisVector (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) (p : PointedFiniteFreeAlgebra R d) (i : Fin d) :
    letI := s.ring
    universalCarrierSectionHom d s p (universalBasisVector d i) = p.coord i := by
  let := s.ring
  change p.sec (universalCarrierClassify d s p.table _) = _
  rw [universalCarrierClassify_basisVector, PointedFiniteFreeAlgebra.sec_basisVector]

/-- A ring map out of the universal free carrier is determined by its restriction along the
universal family and its values on the distinguished basis vectors. -/
theorem universalCarrierHom_ext (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    {ψ χ : letI := s.ring; UniversalFiniteFreeModule d →+* R}
    (ha : letI := s.ring; letI := s.algebra; ∀ a : universalRing d,
      ψ (algebraMap (universalRing d) (UniversalFiniteFreeModule d) a) =
        χ (algebraMap (universalRing d) (UniversalFiniteFreeModule d) a))
    (hb : letI := s.ring; ∀ i, ψ (universalBasisVector d i) = χ (universalBasisVector d i)) :
    ψ = χ := by
  let := s.ring
  let := s.algebra
  refine RingHom.ext fun x => ?_
  conv_lhs => rw [universalCarrier_eq_sum d s x]
  conv_rhs => rw [universalCarrier_eq_sum d s x]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul, ha, hb]

/-- The pointed table of a ring map out of the universal free carrier. -/
def pointedOfUniversalCarrierHom (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (ψ : letI := s.ring; UniversalFiniteFreeModule d →+* R) :
    PointedFiniteFreeAlgebra R d :=
  letI := s.ring
  letI := s.algebra
  { table := tableOfHom (ψ.comp (algebraMap (universalRing d) (UniversalFiniteFreeModule d)))
    coord := fun i => ψ (universalBasisVector d i)
    coord_zero := by
      show ψ (universalBasisVector d 0) = 1
      rw [← universalUnit, ← s.one_eq, map_one]
    coord_mul := by
      intro i j
      have hmul : (universalBasisVector d i * universalBasisVector d j :
          UniversalFiniteFreeModule d) =
          ∑ k, algebraMap (universalRing d) (UniversalFiniteFreeModule d)
            (universalStructureConstant d i j k) * universalBasisVector d k := by
        refine (universalCarrier_eq_sum d s _).trans (Finset.sum_congr rfl fun k _ => ?_)
        exact congrArg
          (fun z => algebraMap (universalRing d) (UniversalFiniteFreeModule d) z *
            universalBasisVector d k)
          (universalCarrier_basisVector_mul_coeff d s i j k)
      rw [← map_mul, hmul, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_mul]; rfl }

/-- The coefficients of the table of a ring map out of the universal free carrier are its values
on the universal structure constants. -/
@[simp] theorem pointedOfUniversalCarrierHom_table_coeff (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) (ψ : letI := s.ring; UniversalFiniteFreeModule d →+* R)
    (i j k : Fin d) :
    letI := s.ring
    letI := s.algebra
    (pointedOfUniversalCarrierHom d s ψ).table.coeff i j k =
      ψ (algebraMap (universalRing d) (UniversalFiniteFreeModule d)
        (universalStructureConstant d i j k)) := rfl

/-- The coordinates of the pointed table of a ring map out of the universal free carrier are its
values on the distinguished basis vectors. -/
@[simp] theorem pointedOfUniversalCarrierHom_coord (d : ℕ) [NeZero d]
    (s : UniversalAlgebraStructure d) (ψ : letI := s.ring; UniversalFiniteFreeModule d →+* R)
    (i : Fin d) :
    letI := s.ring
    (pointedOfUniversalCarrierHom d s ψ).coord i = ψ (universalBasisVector d i) := rfl

/-- **Ring maps out of the universal free carrier `B_d` are multiplication tables with a
section.** This is the functor of points of the total space `Y_d` of the universal finite free
family, in its affine form. -/
def universalCarrierHomEquiv (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d)
    (R : Type*) [CommRing R] :
    letI := s.ring
    (UniversalFiniteFreeModule d →+* R) ≃ PointedFiniteFreeAlgebra R d := by
  letI := s.ring
  letI := s.algebra
  refine
    { toFun := fun ψ => pointedOfUniversalCarrierHom d s ψ
      invFun := fun p => universalCarrierSectionHom d s p
      left_inv := ?_
      right_inv := ?_ }
  · intro ψ
    refine (universalCarrierHom_ext d s (fun a => ?_) (fun i => ?_)).symm
    · rw [universalCarrierSectionHom_algebraMap]
      change _ = (tableOfHom (ψ.comp
        (algebraMap (universalRing d) (UniversalFiniteFreeModule d)))).classify a
      rw [classify_tableOfHom]
      rfl
    · rw [universalCarrierSectionHom_basisVector]
      rfl
  · intro p
    refine PointedFiniteFreeAlgebra.ext (ext_coeff fun i j k => ?_) (funext fun i => ?_)
    · rw [pointedOfUniversalCarrierHom_table_coeff, universalCarrierSectionHom_algebraMap,
        classify_universalStructureConstant]
    · rw [pointedOfUniversalCarrierHom_coord, universalCarrierSectionHom_basisVector]

end Carrier

section Scheme

/-- A morphism to an affine scheme is recovered from its map on global sections: the `Γ`–`Spec`
adjunction with the opposite-category bookkeeping discharged. -/
@[ega "I 2.2.4" "partial"]
theorem eq_toSpecΓ_comp {T : Scheme.{u}} {B : CommRingCat.{u}} (a : T ⟶ Spec B) :
    a = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso B).inv ≫ a.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality a, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Two morphisms to an affine scheme that agree on global sections agree. -/
theorem hom_ext_of_appTop {T : Scheme.{u}} {B : CommRingCat.{u}} {a c : T ⟶ Spec B}
    (h : (Scheme.ΓSpecIso B).inv ≫ a.appTop = (Scheme.ΓSpecIso B).inv ≫ c.appTop) : a = c := by
  rw [eq_toSpecΓ_comp a, eq_toSpecΓ_comp c, h]

/-- The map on global sections of the morphism to an affine scheme built from a ring map. -/
theorem appTop_toSpecΓ_comp {T : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(T, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ (T.toSpecΓ ≫ Spec.map φ).appTop = φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {d : ℕ} [NeZero d]

/-- The ring map out of the universal free carrier `B_d` attached to a point of `Y_d`. -/
def universalTotalPointHom (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) :
    letI := (universalAlgebraStructure d).ring
    UniversalFiniteFreeModule d →+* Γ(T, ⊤) :=
  letI := (universalAlgebraStructure d).ring
  (((Scheme.ΓSpecIso (CommRingCat.of
      (ULift.{u} (UniversalFiniteFreeModule d)))).inv ≫ a.appTop).hom).comp
    (ULift.ringEquiv (R := UniversalFiniteFreeModule d)).symm.toRingHom

/-- The ring map attached to a point `a` of `Y_d` is the map of `a` on global sections, composed
with the inverse of the `Γ`–`Spec` isomorphism. -/
theorem universalTotalPointHom_apply (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d))
    (x : letI := (universalAlgebraStructure d).ring; UniversalFiniteFreeModule d) :
    letI := (universalAlgebraStructure d).ring
    universalTotalPointHom.{u} d a x =
      a.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
        (ULift.{u} (UniversalFiniteFreeModule d)))).inv.hom (ULift.up x)) := rfl

/-- The value of a point of `Y_d` on a distinguished basis vector is its value on the
corresponding vector of the coordinate basis of `Y_d`. -/
theorem universalTotalPointHom_basisVector (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) (i : Fin d) :
    letI := (universalAlgebraStructure d).ring
    universalTotalPointHom.{u} d a (universalBasisVector d i) =
      a.appTop.hom (universalTotalGammaBasis.{u} d i) := by
  rw [universalTotalGammaBasis_apply.{u} d i]
  rfl

/-- The restriction of a point of `Y_d` along the universal family is the corresponding point of
`X_d`. -/
theorem universalTotalPointHom_algebraMap (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) (x : universalRing d) :
    letI := (universalAlgebraStructure d).ring
    letI := (universalAlgebraStructure d).algebra
    universalTotalPointHom.{u} d a
        (algebraMap (universalRing d) (UniversalFiniteFreeModule d) x) =
      pointRingHom d (a ≫ universalFamily.{u} d (universalAlgebraStructure d)) x := by
  let := (universalAlgebraStructure d).ring
  let := (universalAlgebraStructure d).algebra
  set ρ : CommRingCat.of (ULift.{u} (universalRing d)) ⟶
      CommRingCat.of (ULift.{u} (UniversalFiniteFreeModule d)) :=
    CommRingCat.ofHom (RingHom.ulift
      (algebraMap (universalRing d) (UniversalFiniteFreeModule d)))
  have hnat := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality ρ)
  change a.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
      (ULift.{u} (UniversalFiniteFreeModule d)))).inv.hom
        (ρ.hom (ULift.up x))) = _
  change _ = a.appTop.hom ((Spec.map ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
      (ULift.{u} (universalRing d)))).inv.hom (ULift.up x)))
  exact congrArg a.appTop.hom (DFunLike.congr_fun hnat (ULift.up x))

/-- The pointed table of a point of `Y_d` over a scheme: the point of `X_d` below it, together
with its values on the coordinate basis of `Y_d`. -/
def pointedFamilyTable (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) :
    PointedFiniteFreeAlgebra Γ(T, ⊤) d :=
  universalCarrierHomEquiv d (universalAlgebraStructure d) Γ(T, ⊤)
    (universalTotalPointHom.{u} d a)

/-- The coordinates of the pointed table of a point of `Y_d` are its values on the coordinate
basis of `Y_d`. -/
@[simp] theorem pointedFamilyTable_coord (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) (i : Fin d) :
    (pointedFamilyTable.{u} d a).coord i = a.appTop.hom (universalTotalGammaBasis.{u} d i) := by
  rw [← universalTotalPointHom_basisVector.{u} d a i]
  rfl

/-- The table of the pointed table of a point of `Y_d` is the point of `X_d` below it. -/
theorem pointedFamilyTable_table (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) :
    (pointedFamilyTable.{u} d a).table =
      (representation.{u} d).equiv T
        (a ≫ universalFamily.{u} d (universalAlgebraStructure d)) := by
  let := (universalAlgebraStructure d).ring
  let := (universalAlgebraStructure d).algebra
  refine ext_coeff fun i j k => ?_
  rw [representation_equiv_coeff, ← universalTotalPointHom_algebraMap.{u} d a]
  rfl

/-- The morphism to `Y_d` determined by a pointed table over the global sections of a scheme. -/
def pointedFamilyHom (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (p : PointedFiniteFreeAlgebra Γ(T, ⊤) d) :
    T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d) :=
  letI := (universalAlgebraStructure d).ring
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((universalCarrierSectionHom d (universalAlgebraStructure d) p).comp
      (ULift.ringEquiv (R := UniversalFiniteFreeModule d)).toRingHom))

/-- The ring map attached to the morphism determined by a pointed table is the ring map determined
by that table. -/
theorem universalTotalPointHom_pointedFamilyHom (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (p : PointedFiniteFreeAlgebra Γ(T, ⊤) d) :
    letI := (universalAlgebraStructure d).ring
    universalTotalPointHom.{u} d (pointedFamilyHom.{u} d p) =
      universalCarrierSectionHom d (universalAlgebraStructure d) p := by
  let := (universalAlgebraStructure d).ring
  refine RingHom.ext fun x => ?_
  have h := congrArg CommRingCat.Hom.hom (appTop_toSpecΓ_comp (T := T)
    (CommRingCat.ofHom
      ((universalCarrierSectionHom d (universalAlgebraStructure d) p).comp
        (ULift.ringEquiv (R := UniversalFiniteFreeModule d)).toRingHom)))
  exact DFunLike.congr_fun h (ULift.up x)

/-- The pointed table of the morphism to `Y_d` determined by a pointed table is that table. -/
@[simp] theorem pointedFamilyTable_pointedFamilyHom (d : ℕ) [NeZero d] {T : Scheme.{u}}
    (p : PointedFiniteFreeAlgebra Γ(T, ⊤) d) :
    pointedFamilyTable.{u} d (pointedFamilyHom.{u} d p) = p := by
  rw [pointedFamilyTable, universalTotalPointHom_pointedFamilyHom.{u} d p]
  exact (universalCarrierHomEquiv d (universalAlgebraStructure d) Γ(T, ⊤)).apply_symm_apply p

/-- A point of `Y_d` is determined by its pointed table. -/
theorem universalTotal_hom_ext (d : ℕ) [NeZero d] {T : Scheme.{u}}
    {a c : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)}
    (h : pointedFamilyTable.{u} d a = pointedFamilyTable.{u} d c) : a = c := by
  let := (universalAlgebraStructure d).ring
  let := (universalAlgebraStructure d).algebra
  have hψ : universalTotalPointHom.{u} d a = universalTotalPointHom.{u} d c :=
    (universalCarrierHomEquiv d (universalAlgebraStructure d) Γ(T, ⊤)).injective h
  refine hom_ext_of_appTop (CommRingCat.hom_ext (RingHom.ext fun y => ?_))
  exact DFunLike.congr_fun hψ y.down

/-- **The functor of points of `Y_d`.** A point of the total space of the universal finite free
family of rank `d` over a scheme `T` is a multiplication table over the global sections of `T`
together with the coordinates of a section of the algebra it defines. -/
def pointedFamilyEquiv (d : ℕ) [NeZero d] (T : Scheme.{u}) :
    (T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) ≃
      PointedFiniteFreeAlgebra Γ(T, ⊤) d where
  toFun := pointedFamilyTable.{u} d
  invFun := pointedFamilyHom.{u} d
  left_inv a :=
    universalTotal_hom_ext.{u} d
      (pointedFamilyTable_pointedFamilyHom.{u} d (pointedFamilyTable.{u} d a))
  right_inv p := pointedFamilyTable_pointedFamilyHom.{u} d p

/-- The open `V_d` of Stacks 0FL3: the preimage under the universal finite free family of rank
`d` of the open `U_d` of Tag 0FL0 over which that family is syntomic. -/
def universalSyntomicPreimage (d : ℕ) [NeZero d] :
    (universalTotalScheme.{u} d (universalAlgebraStructure d)).Opens :=
  universalFamily.{u} d (universalAlgebraStructure d) ⁻¹ᵁ universalSyntomicOpen.{u} d

/-- Morphisms to an open subscheme are the morphisms to the ambient scheme whose image lies in
the open. -/
def openImmersionHomEquiv {X : Scheme.{u}} (U : X.Opens) (T : Scheme.{u}) :
    (T ⟶ U.toScheme) ≃ {a : T ⟶ X // Set.range a.base ⊆ Set.range U.ι.base} where
  toFun g := ⟨g ≫ U.ι, by
    rintro _ ⟨t, rfl⟩
    exact ⟨g.base t, by simp⟩⟩
  invFun a := IsOpenImmersion.lift U.ι a.1 a.2
  left_inv g := (cancel_mono U.ι).1 (IsOpenImmersion.lift_fac _ _ _)
  right_inv a := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

/-- A morphism to `Y_d` has image in `V_d` exactly when its composite with the universal family
factors through the open `U_d` of Tag 0FL0. -/
theorem range_subset_universalSyntomicPreimage_iff (d : ℕ) [NeZero d] (T : Scheme.{u})
    (a : T ⟶ universalTotalScheme.{u} d (universalAlgebraStructure d)) :
    Set.range a.base ⊆ Set.range (universalSyntomicPreimage.{u} d).ι.base ↔
      ∃ ĝ : T ⟶ (universalSyntomicOpen.{u} d).toScheme,
        ĝ ≫ (universalSyntomicOpen.{u} d).ι =
          a ≫ universalFamily.{u} d (universalAlgebraStructure d) := by
  have hmem : ∀ t : T, (a.base t ∈ (universalSyntomicPreimage.{u} d : Set _)) ↔
      ((a ≫ universalFamily.{u} d (universalAlgebraStructure d)).base t ∈
        (universalSyntomicOpen.{u} d : Set _)) := fun t => by
    simp [universalSyntomicPreimage]
  rw [Scheme.Opens.range_ι, Set.range_subset_iff]
  constructor
  · intro h
    refine ⟨IsOpenImmersion.lift (universalSyntomicOpen.{u} d).ι _ ?_,
      IsOpenImmersion.lift_fac _ _ _⟩
    rw [Scheme.Opens.range_ι, Set.range_subset_iff]
    exact fun t => (hmem t).mp (h t)
  · rintro ⟨ĝ, hĝ⟩ t
    refine (hmem t).mpr ?_
    have ht : (a ≫ universalFamily.{u} d (universalAlgebraStructure d)).base t ∈
        Set.range (universalSyntomicOpen.{u} d).ι.base :=
      ⟨ĝ.base t, by simpa using congrArg (fun k : T ⟶ _ => k.base t) hĝ⟩
    simpa only [Scheme.Opens.range_ι] using ht

/-- **The functor of points of `V_d = pi_d^{-1}(U_d)`.** A point of `V_d` over a scheme `T` is a
multiplication table over the global sections of `T` whose classifying morphism factors through
the open `U_d` of Tag 0FL0, together with the coordinates of a section of the algebra the table
defines. -/
def pointedSyntomicEquiv (d : ℕ) [NeZero d] (T : Scheme.{u}) :
    (T ⟶ (universalSyntomicPreimage.{u} d).toScheme) ≃
      {p : PointedFiniteFreeAlgebra Γ(T, ⊤) d //
        ∃ ĝ : T ⟶ (universalSyntomicOpen.{u} d).toScheme,
          ĝ ≫ (universalSyntomicOpen.{u} d).ι =
            pointedFamilyHom.{u} d p ≫
              universalFamily.{u} d (universalAlgebraStructure d)} :=
  (openImmersionHomEquiv.{u} (universalSyntomicPreimage.{u} d) T).trans
    (Equiv.subtypeEquiv (pointedFamilyEquiv.{u} d T) fun a => by
      rw [range_subset_universalSyntomicPreimage_iff.{u} d T a,
        show pointedFamilyHom.{u} d (pointedFamilyEquiv.{u} d T a) = a from
          (pointedFamilyEquiv.{u} d T).symm_apply_apply a])

end Scheme

end AlgebraicGeometry

end
