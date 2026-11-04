module

public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclicGeneral

/-! # Modules with a basis of closed homogeneous elements are orthogonal to the acyclic modules

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `M` be a right
differential graded `A`-module. Suppose `M` has a *basis of closed homogeneous elements*: a family
`(e j)` of elements, `e j` homogeneous of degree `k j` and killed by the differential, such that
every element of `M` is uniquely a finite sum `∑ e j · a j` with `a j ∈ A`, and such that
`∑ e j · a j` is homogeneous of degree `n` only when every `a j` is homogeneous of degree
`n - k j`. Then `M`
is a direct sum of shifts of the regular module, and so lies in the left orthogonal of the
acyclic objects of the homotopy category (Tag 09K1 summand by summand).

This is the form in which the modules of sections of a free differential graded module over a
sheaf of differential graded algebras are recognized: their bases are the generators, which are
closed by construction, and no isomorphism with a bundled direct sum of shifts has to be written
down.

## Main definitions

* `DifferentialGradedModule.rightMulMap`: right multiplication by a fixed element, as a right
  `A`-linear map out of the algebra.
* `DifferentialGradedModule.basisMap`: the right `A`-linear map `⨁ j, A ⟶ M`,
  `(a j) ↦ ∑ e j · a j`, attached to a family of elements.
* `DifferentialGradedModule.IsClosedBasis`: the family `e` is a basis of closed homogeneous
  elements of degrees `k`.

## Main results

* `DifferentialGradedModule.General.leftOrthogonal_acyclic_of_isClosedBasis`: a differential
  graded module with a basis of closed homogeneous elements lies in the left orthogonal of the
  acyclic objects, at independent universes for the algebra, the module and the index set.
* `DifferentialGradedModule.leftOrthogonal_acyclic'_of_isClosedBasis`: the same at a single
  universe, for the class `DifferentialGradedModule.acyclic'`.
* `DifferentialGradedModule.IsClosedBasis.shift`: a basis of closed homogeneous elements of `M`
  is one of every shift of `M`, in the shifted degrees.

## Implementation notes

The proof is `DifferentialGradedModule.General.isNullHomotopic_of_directSum` applied to the
presentation of `M` as `⨁ j, A[-k j]` given by the basis map, each summand contributing a
null-homotopy by `DifferentialGradedModule.General.isNullHomotopic_of_acyclic`. The summand
`A[-k j]` maps to `M` by `a ↦ e j · a`; that this commutes with the differentials is the Leibniz
rule together with `d (e j) = 0`, the sign `(-1)^{-k j}` of the shift being the sign `(-1)^{k j}`
the Leibniz rule produces.

## References

* [Stacks Project, Tag 09K1](https://stacks.math.columbia.edu/tag/09K1)
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

namespace DifferentialGradedModule

universe u v w w'

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

/-- Right multiplication by a fixed element of a right differential graded module, as a map of
right `A`-modules out of the algebra. -/
def rightMulMap {N : DifferentialGradedModule.{u, v, w} A} (y : N.M) :
    A.A →ₗ[MulOpposite A.A] N.M where
  toFun a := MulOpposite.op a • y
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' c a := by
    change MulOpposite.op (a * c.unop) • y = c • (MulOpposite.op a • y)
    rw [MulOpposite.op_mul, MulOpposite.op_unop, mul_smul]

/-- The map `rightMulMap y` sends `a` to `y · a`. -/
@[simp] theorem rightMulMap_apply {N : DifferentialGradedModule.{u, v, w} A} (y : N.M)
    (a : A.A) : rightMulMap y a = MulOpposite.op a • y := rfl

/-- Right multiplication by a fixed element of a right differential graded module, as an
`R`-linear map out of the algebra. -/
def rightMulLinear {N : DifferentialGradedModule.{u, v, w} A} (y : N.M) : A.A →ₗ[R] N.M where
  toFun a := MulOpposite.op a • y
  map_add' a b := by rw [MulOpposite.op_add, add_smul]
  map_smul' r a := by
    change MulOpposite.op (r • a) • y = r • (MulOpposite.op a • y)
    rw [MulOpposite.op_smul, smul_assoc]

/-- The map `rightMulLinear y` sends `a` to `y · a`. -/
@[simp] theorem rightMulLinear_apply {N : DifferentialGradedModule.{u, v, w} A} (y : N.M)
    (a : A.A) : rightMulLinear y a = MulOpposite.op a • y := rfl

/-- The right `A`-linear map `⨁ j, A ⟶ M`, `(a j) ↦ ∑ e j · a j`, attached to a family `e` of
elements of `M`. -/
def basisMap (M : DifferentialGradedModule.{u, v, w} A) {ι : Type w'} [DecidableEq ι]
    (e : ι → M.M) : (⨁ _ : ι, A.A) →ₗ[MulOpposite A.A] M.M :=
  DirectSum.toModule (MulOpposite A.A) ι M.M fun j => rightMulMap (e j)

/-- The map `basisMap M e` sends the element `a` in the summand indexed by `j` to `e j · a`. -/
@[simp] theorem basisMap_of (M : DifferentialGradedModule.{u, v, w} A) {ι : Type w'}
    [DecidableEq ι] (e : ι → M.M) (j : ι) (a : A.A) :
    basisMap M e (DirectSum.of (fun _ : ι => A.A) j a) = MulOpposite.op a • e j :=
  DirectSum.toModule_lof (MulOpposite A.A) (M := fun _ : ι => A.A) j a

/-- **A basis of closed homogeneous elements.** The family `e` of elements of `M` is a basis of
`M` as a right `A`-module, each `e j` is homogeneous of degree `k j` and closed, and an element
`∑ e j · a j` is homogeneous of degree `n` only when every coefficient `a j` is homogeneous of
degree `n - k j`. -/
structure IsClosedBasis (M : DifferentialGradedModule.{u, v, w} A) {ι : Type w'}
    [DecidableEq ι] (k : ι → ℤ) (e : ι → M.M) : Prop where
  /-- Each basis element is homogeneous of its degree. -/
  mem : ∀ j, e j ∈ M.grading (k j)
  /-- Each basis element is closed. -/
  d_eq_zero : ∀ j, M.d (e j) = 0
  /-- Every element is uniquely a combination of the basis elements. -/
  bijective : Function.Bijective (basisMap M e)
  /-- A homogeneous combination has homogeneous coefficients. -/
  mem_of_mem : ∀ (n : ℤ) (z : ⨁ _ : ι, A.A), basisMap M e z ∈ M.grading n →
    ∀ j, z j ∈ A.grading (n - k j)

namespace IsClosedBasis

variable {M : DifferentialGradedModule.{u, v, w} A} {ι : Type w'} [DecidableEq ι]
  {k : ι → ℤ} {e : ι → M.M}

/-- The homomorphism `A[-k j] ⟶ M`, `a ↦ e j · a`, out of the shift of the regular module by
minus the degree of a basis element. -/
def inj (h : IsClosedBasis M k e) (j : ι) : Hom (shift (regularModule A) (-k j)) M where
  toFun := rightMulLinear (e j)
  map_smul := fun (x a : A.A) => by
    change MulOpposite.op (x * a) • e j = MulOpposite.op a • (MulOpposite.op x • e j)
    rw [MulOpposite.op_mul, mul_smul]
  map_grading := fun n (x : A.A) hx => by
    have hx' : x ∈ A.grading (n + -k j) := hx
    exact mem_grading_congr (by ring) (M.smul_mem (k j) (n + -k j) (e j) x (h.mem j) hx')
  map_d := LinearMap.ext fun (a : A.A) => by
    change MulOpposite.op (((-k j).negOnePow : ℤ) • A.d a) • e j =
      M.d (MulOpposite.op a • e j)
    rw [leibniz_apply M (k j) (e j) (h.mem j) a, h.d_eq_zero j, smul_zero, zero_add,
      Int.negOnePow_neg, MulOpposite.op_smul, smul_assoc]

/-- The homomorphism `h.inj j` sends `a` to `e j · a`. -/
@[simp] theorem inj_toFun (h : IsClosedBasis M k e) (j : ι) (a : A.A) :
    (h.inj j).toFun a = MulOpposite.op (show A.A from a) • e j := rfl

/-- **A basis of closed homogeneous elements of `M` is one of every shift of `M`**, the degree of
each basis element moving down by the shift. The shift has the same underlying module and right
action, so the basis map is unchanged. -/
theorem shift (h : IsClosedBasis M k e) (c : ℤ) :
    IsClosedBasis (DifferentialGradedModule.shift M c) (fun j => k j - c) e where
  mem j := by
    change e j ∈ M.grading (k j - c + c)
    rw [sub_add_cancel]
    exact h.mem j
  d_eq_zero j := by
    change (c.negOnePow • M.d) (e j) = 0
    rw [LinearMap.smul_apply, h.d_eq_zero j, smul_zero]
  bijective := h.bijective
  mem_of_mem n z hz j := by
    have := h.mem_of_mem (n + c) z hz j
    rwa [show n + c - k j = n - (k j - c) by ring] at this

end IsClosedBasis

/-- **A differential graded module with a basis of closed homogeneous elements lies in the left
orthogonal of the acyclic objects of the homotopy category**, at independent universes for the
algebra, the module and the index set of the basis. The basis map presents the module as the
direct sum of the shifts `A[-k j]`, and a homomorphism out of each of them into an acyclic module
is null-homotopic by Tag 09K1. -/
theorem General.leftOrthogonal_acyclic_of_isClosedBasis
    {M : DifferentialGradedModule.{u, v, w} A} {ι : Type w'} [DecidableEq ι] {k : ι → ℤ}
    {e : ι → M.M} (h : IsClosedBasis M k e) :
    (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj M) := by
  rw [General.leftOrthogonal_acyclic_iff]
  intro N hN f
  rw [← General.isNullHomotopic_iff_homotopic_zero]
  refine General.isNullHomotopic_of_directSum
    (X := fun j => shift (regularModule A) (-k j)) h.inj
    (LinearEquiv.ofBijective (basisMap M e) h.bijective)
    (fun j x => basisMap_of M e j x) (fun n z hz j => ?_) f
    (fun j => General.isNullHomotopic_of_acyclic hN (-k j) _)
  have := h.mem_of_mem n z hz j
  rwa [sub_eq_add_neg] at this

/-- **A differential graded module with a basis of closed homogeneous elements lies in the left
orthogonal of the acyclic objects**, at a single universe. -/
theorem leftOrthogonal_acyclic'_of_isClosedBasis {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra.{u, u} R} {M : DifferentialGradedModule.{u, u, u} A}
    {ι : Type w'} [DecidableEq ι] {k : ι → ℤ} {e : ι → M.M} (h : IsClosedBasis M k e) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) :=
  General.leftOrthogonal_acyclic_of_isClosedBasis h

/-- At a single universe the class `DifferentialGradedModule.acyclic'` of the acyclic objects is
the universe-polymorphic class `DifferentialGradedModule.acyclic`. -/
theorem acyclic'_eq_acyclic {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, u} R) :
    acyclic' A = acyclic.{u, u, u} A := rfl

end DifferentialGradedModule

end
