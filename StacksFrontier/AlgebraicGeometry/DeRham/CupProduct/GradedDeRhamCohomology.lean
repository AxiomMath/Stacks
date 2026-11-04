module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Ring.NegOnePow
public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProductUnit

/-!
# The graded de Rham cohomology ring

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex of `φ`. The cup product of Section 50.4 makes

`H^*_{dR} = ⨁_{n ∈ 𝐙} H^n_{dR}`

a `𝐙`-graded ring: it is associative and graded commutative by Tag 0FM3, and the class of the
global section `1` of `Ω^0` is a two-sided unit. This file builds that ring as the direct sum of
the de Rham cohomology modules in all degrees, with its grading by the summands, and proves the
Koszul sign rule `a ∪ b = (-1)^{ij} b ∪ a` for homogeneous `a` of degree `i` and `b` of degree
`j`. Over a commutative ring `R` acting on the global sections of the base ring sheaf it is a
graded `R`-algebra.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamGRing`: the graded ring structure on the family
  `n ↦ H^n_{dR}`, the product being the cup product.
* `AlgebraicGeometry.SheafOfModules.gradedDeRhamCohomology`: **the ring `H^*_{dR}`**.
* `AlgebraicGeometry.SheafOfModules.deRhamGAlgebra`: the graded algebra structure over a
  commutative ring `R` mapping to the global sections of the base ring sheaf.

## Main results

* `AlgebraicGeometry.SheafOfModules.gradedDeRhamCohomology_of_mul_of`: the product of two
  homogeneous classes is their cup product.
* `AlgebraicGeometry.SheafOfModules.gradedDeRhamCohomology_mul_comm`: **the Koszul sign rule**.

## References

* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace DirectSum

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The family `n ↦ H^n_{dR}` of de Rham cohomology groups in every degree. -/
abbrev deRhamPiece (n : ℤ) : Type u :=
  deRhamCohomology B D n

/-- A pair of a degree and a de Rham class in that degree is determined by the class read in any
equal degree. -/
theorem gradedMonoid_mk_reindex {m n : ℤ} (h : m = n) (x : deRhamCohomology B D m) :
    (GradedMonoid.mk m x : GradedMonoid (deRhamPiece B D)) =
      GradedMonoid.mk n (reindexDeRhamCohomology B D h x) := by
  subst h
  rfl

/-- The cup product with a fixed class on the right, as an additive map in the left variable. -/
def deRhamCupLeftHom (i j : ℤ) (y : deRhamCohomology B D j) :
    deRhamCohomology B D i →+ deRhamCohomology B D (i + j) :=
  AddMonoidHom.mk' (fun x => deRhamCohomologyCup B D i j x y)
    (fun x x' => deRhamCohomologyCup_add_left B D i j x x' y)

/-- The cup product with a fixed class on the left, as an additive map in the right variable. -/
def deRhamCupRightHom (i j : ℤ) (x : deRhamCohomology B D i) :
    deRhamCohomology B D j →+ deRhamCohomology B D (i + j) :=
  AddMonoidHom.mk' (fun y => deRhamCohomologyCup B D i j x y)
    (fun y y' => deRhamCohomologyCup_add_right B D i j x y y')

/-- The graded unit of `n ↦ H^n_{dR}`: the class of the global section `1` in degree `0`. -/
instance deRhamGOne : GradedMonoid.GOne (deRhamPiece B D) where
  one := deRhamOneClass B D

/-- The graded multiplication on `n ↦ H^n_{dR}`, given by the cup product. -/
instance deRhamGMul : GradedMonoid.GMul (deRhamPiece B D) where
  mul {i j} x y := deRhamCohomologyCup B D i j x y

/-- The graded multiplication of two de Rham classes is their cup product. -/
theorem deRham_gMul_eq {i j : ℤ} (x : deRhamPiece B D i) (y : deRhamPiece B D j) :
    GradedMonoid.GMul.mul x y = deRhamCohomologyCup B D i j x y :=
  rfl

/-- The graded unit is the class of the global section `1` in degree `0`. -/
theorem deRham_gOne_eq : (GradedMonoid.GOne.one : deRhamPiece B D 0) = deRhamOneClass B D :=
  rfl

/-- Graded pairs are equal if the classes agree after reading in the equal degree. -/
private theorem gradedMonoid_mk_eq_of_reindex {m n : ℤ} (h : m = n) {x : deRhamCohomology B D m}
    {y : deRhamCohomology B D n} (hxy : reindexDeRhamCohomology B D h x = y) :
    (GradedMonoid.mk m x : GradedMonoid (deRhamPiece B D)) = GradedMonoid.mk n y :=
  (gradedMonoid_mk_reindex B D h x).trans (congrArg _ hxy)

/-- The unit class is a left identity for the cup product on graded pairs. -/
theorem deRham_gradedMonoid_one_mul (a : GradedMonoid (deRhamPiece B D)) : 1 * a = a := by
  obtain ⟨i, x⟩ := a
  exact gradedMonoid_mk_eq_of_reindex B D (zero_add i) (deRhamCohomologyCup_one_left B D i x)

/-- The unit class is a right identity for the cup product on graded pairs. -/
theorem deRham_gradedMonoid_mul_one (a : GradedMonoid (deRhamPiece B D)) : a * 1 = a := by
  obtain ⟨i, x⟩ := a
  exact gradedMonoid_mk_eq_of_reindex B D (add_zero i) (deRhamCohomologyCup_one_right B D i x)

/-- The cup product on graded pairs is associative. -/
theorem deRham_gradedMonoid_mul_assoc (a b c : GradedMonoid (deRhamPiece B D)) :
    a * b * c = a * (b * c) := by
  obtain ⟨i, x⟩ := a
  obtain ⟨j, y⟩ := b
  obtain ⟨k, z⟩ := c
  exact gradedMonoid_mk_eq_of_reindex B D (add_assoc i j k)
    (deRhamCohomologyCup_assoc B D i j k x y z)

/-- **The graded ring `n ↦ H^n_{dR}`**: the product is the cup product, the unit the class of the
global section `1`; it is associative by Tag 0FM3. -/
instance deRhamGRing : DirectSum.GRing (deRhamPiece B D) where
  mul_zero {i j} x := (deRhamCupRightHom B D i j x).map_zero
  zero_mul {i j} y := (deRhamCupLeftHom B D i j y).map_zero
  mul_add {i j} x y y' := deRhamCohomologyCup_add_right B D i j x y y'
  add_mul {i j} x x' y := deRhamCohomologyCup_add_left B D i j x x' y
  one_mul := deRham_gradedMonoid_one_mul B D
  mul_one := deRham_gradedMonoid_mul_one B D
  mul_assoc := deRham_gradedMonoid_mul_assoc B D
  natCast n := (n : ℤ) • deRhamOneClass B D
  natCast_zero := by simp
  natCast_succ n := by
    change ((n + 1 : ℕ) : ℤ) • deRhamOneClass B D = (n : ℤ) • deRhamOneClass B D + _
    rw [Nat.cast_succ, add_smul, one_smul]
    rfl
  intCast z := z • deRhamOneClass B D
  intCast_ofNat _ := rfl
  intCast_negSucc_ofNat n := by
    change Int.negSucc n • deRhamOneClass B D = -(((n + 1 : ℕ) : ℤ) • deRhamOneClass B D)
    rw [Int.negSucc_eq, neg_smul]
    push_cast
    rfl

/-- **The de Rham cohomology ring** `H^*_{dR} = ⨁_{n ∈ 𝐙} H^n_{dR}`, with the cup product. -/
abbrev gradedDeRhamCohomology : Type u :=
  DirectSum ℤ (deRhamPiece B D)

/-- The product of two homogeneous classes is their cup product. -/
theorem gradedDeRhamCohomology_of_mul_of {i j : ℤ} (x : deRhamCohomology B D i)
    (y : deRhamCohomology B D j) :
    (DirectSum.of (deRhamPiece B D) i x * DirectSum.of (deRhamPiece B D) j y :
        gradedDeRhamCohomology B D) =
      DirectSum.of (deRhamPiece B D) (i + j) (deRhamCohomologyCup B D i j x y) :=
  DirectSum.of_mul_of (A := deRhamPiece B D) x y

/-- The unit of `H^*_{dR}` is the class of the global section `1` in degree `0`. -/
theorem gradedDeRhamCohomology_one :
    (1 : gradedDeRhamCohomology B D) = DirectSum.of (deRhamPiece B D) 0 (deRhamOneClass B D) :=
  rfl

/-- The inclusions of the summands, read in equal degrees, agree. -/
theorem of_reindexDeRhamCohomology {m n : ℤ} (h : m = n) (x : deRhamCohomology B D m) :
    DirectSum.of (deRhamPiece B D) n (reindexDeRhamCohomology B D h x) =
      DirectSum.of (deRhamPiece B D) m x := by
  subst h
  rfl

/-- **The Koszul sign rule on homogeneous generators**: `x ∪ y = (-1)^{ij} y ∪ x` in
`H^*_{dR}` for `x` of degree `i` and `y` of degree `j` (Tag 0FM3). -/
theorem gradedDeRhamCohomology_of_mul_of_comm {i j : ℤ} (x : deRhamCohomology B D i)
    (y : deRhamCohomology B D j) :
    (DirectSum.of (deRhamPiece B D) i x * DirectSum.of (deRhamPiece B D) j y :
        gradedDeRhamCohomology B D) =
      ((i * j).negOnePow : ℤ) •
        (DirectSum.of (deRhamPiece B D) j y * DirectSum.of (deRhamPiece B D) i x) := by
  rw [gradedDeRhamCohomology_of_mul_of, gradedDeRhamCohomology_of_mul_of,
    deRhamCohomologyCup_comm, map_zsmul, of_reindexDeRhamCohomology]

/-! ### The grading -/

/-- The degree-`n` part `H^n_{dR}` of `H^*_{dR}`, over a ring `R` acting on every `H^n_{dR}`. -/
abbrev deRhamGrade (R : Type*) [CommRing R] [∀ n, Module R (deRhamCohomology B D n)] (n : ℤ) :
    Submodule R (gradedDeRhamCohomology B D) :=
  DirectSum.rangeGrading R (deRhamPiece B D) n

/-- **The Koszul sign rule** on `H^*_{dR}`: `a ∪ b = (-1)^{ij} b ∪ a` for `a` homogeneous of
degree `i` and `b` homogeneous of degree `j`. -/
theorem gradedDeRhamCohomology_mul_comm (R : Type*) [CommRing R]
    [∀ n, Module R (deRhamCohomology B D n)] (i j : ℤ) (a b : gradedDeRhamCohomology B D)
    (ha : a ∈ deRhamGrade B D R i) (hb : b ∈ deRhamGrade B D R j) :
    a * b = ((i * j).negOnePow : ℤ) • (b * a) := by
  obtain ⟨x, rfl⟩ := (DirectSum.mem_rangeGrading R _ i a).1 ha
  obtain ⟨y, rfl⟩ := (DirectSum.mem_rangeGrading R _ j b).1 hb
  exact gradedDeRhamCohomology_of_mul_of_comm B D x y

/-! ### Scalars -/

section Algebra

variable {R : Type*} [CommRing R] [∀ n, Module R (deRhamCohomology B D n)]
  (hl : ∀ (r : R) (i j : ℤ) (x : deRhamCohomology B D i) (y : deRhamCohomology B D j),
    deRhamCohomologyCup B D i j (r • x) y = r • deRhamCohomologyCup B D i j x y)
  (hr : ∀ (r : R) (i j : ℤ) (x : deRhamCohomology B D i) (y : deRhamCohomology B D j),
    deRhamCohomologyCup B D i j x (r • y) = r • deRhamCohomologyCup B D i j x y)

/-- Reading a de Rham class in an equal degree commutes with scalar multiplication by `R`. -/
theorem reindexDeRhamCohomology_smul' {m n : ℤ} (h : m = n) (r : R)
    (x : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D h (r • x) = r • reindexDeRhamCohomology B D h x := by
  subst h
  rfl

include hl in
/-- The cup product of `r • 1` with a class `x` of degree `i` is `r • x`, as graded pairs. -/
theorem gradedMonoid_mk_smul_one_cup (r : R) {i : ℤ} (x : deRhamCohomology B D i) :
    (GradedMonoid.mk (0 + i) (deRhamCohomologyCup B D 0 i (r • deRhamOneClass B D) x) :
        GradedMonoid (deRhamPiece B D)) = GradedMonoid.mk i (r • x) := by
  rw [hl, gradedMonoid_mk_reindex B D (zero_add i), reindexDeRhamCohomology_smul',
    deRhamCohomologyCup_one_left]

include hr in
/-- The cup product of a class `x` of degree `i` with `r • 1` is `r • x`, as graded pairs. -/
theorem gradedMonoid_mk_cup_smul_one (r : R) {i : ℤ} (x : deRhamCohomology B D i) :
    (GradedMonoid.mk (i + 0) (deRhamCohomologyCup B D i 0 x (r • deRhamOneClass B D)) :
        GradedMonoid (deRhamPiece B D)) = GradedMonoid.mk i (r • x) := by
  rw [hr, gradedMonoid_mk_reindex B D (add_zero i), reindexDeRhamCohomology_smul',
    deRhamCohomologyCup_one_right]

include hl hr in
/-- **`H^*_{dR}` is a graded `R`-algebra** for a commutative ring `R` acting on every `H^n_{dR}`
compatibly with the cup product in both variables: the structure map sends `r` to `r • 1`. -/
@[instance_reducible]
def deRhamGAlgebra : DirectSum.GAlgebra R (deRhamPiece B D) where
  toFun :=
    { toFun := fun r => r • deRhamOneClass B D
      map_zero' := zero_smul R _
      map_add' := fun r s => add_smul r s _ }
  map_one := one_smul R _
  map_mul r s := by
    change GradedMonoid.mk (A := deRhamPiece B D) 0 ((r * s) • deRhamOneClass B D) =
      GradedMonoid.mk (A := deRhamPiece B D) (0 + 0)
        (deRhamCohomologyCup B D 0 0 (r • deRhamOneClass B D)
          (s • deRhamOneClass B D))
    rw [gradedMonoid_mk_smul_one_cup B D hl, mul_smul]
  commutes r x := by
    obtain ⟨i, x⟩ := x
    change GradedMonoid.mk (A := deRhamPiece B D) (0 + i)
        (deRhamCohomologyCup B D 0 i (r • deRhamOneClass B D) x) =
      GradedMonoid.mk (A := deRhamPiece B D) (i + 0)
        (deRhamCohomologyCup B D i 0 x (r • deRhamOneClass B D))
    rw [gradedMonoid_mk_smul_one_cup B D hl, gradedMonoid_mk_cup_smul_one B D hr]
  smul_def r x := by
    obtain ⟨i, x⟩ := x
    change GradedMonoid.mk (A := deRhamPiece B D) i (r • x) =
      GradedMonoid.mk (A := deRhamPiece B D) (0 + i)
        (deRhamCohomologyCup B D 0 i (r • deRhamOneClass B D) x)
    rw [gradedMonoid_mk_smul_one_cup B D hl]

end Algebra

end AlgebraicGeometry.SheafOfModules

end
