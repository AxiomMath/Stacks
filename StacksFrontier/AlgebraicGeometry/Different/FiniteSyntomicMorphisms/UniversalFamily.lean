module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Scheme

open AlgebraicGeometry.FiniteFreeAlgebra

/-!
# The universal finite free family

For a positive integer `d` the scheme `X_d` of multiplication tables on a free module of rank `d`
carries a universal family: the free module `B_d` of rank `d` over the universal coefficient ring
`A_d`, with the multiplication prescribed by the universal structure constants and the first
basis vector as unit. Its spectrum `Y_d` maps to `X_d`, and that map is the universal finite free
family of rank `d`.

## Main definitions

* `AlgebraicGeometry.universalStructureConstant` is the image in `A_d` of a universal structure
  constant.
* `AlgebraicGeometry.UniversalFiniteFreeModule` is the free carrier `B_d`.
* `AlgebraicGeometry.universalBasisVector`, `AlgebraicGeometry.universalUnit` and
  `AlgebraicGeometry.universalMultiplication` are its prescribed operations.
* `AlgebraicGeometry.UniversalAlgebraStructure` packages a commutative-algebra structure on the
  carrier realizing those operations.
* `AlgebraicGeometry.universalTotalScheme` and `AlgebraicGeometry.universalFamily` are `Y_d` and
  the morphism `Y_d ⟶ X_d`.

## Implementation notes

Forming `Spec(B_d)` requires the algebra axioms for the prescribed multiplication table, so the
total scheme and its morphism take a compatible commutative-ring and algebra structure as a
parameter. Packaging it as `UniversalAlgebraStructure` rather than as instances keeps the
coordinate formulas available.

The universal ring is lifted into the universe of the test schemes before applying `Spec`, as for
the base scheme, so that the family lives in any scheme universe.

## References

* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
-/

@[expose] public noncomputable section

open scoped BigOperators
open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

add_to_stacks 0FKZ "universal_finite_free_family" universalRing
add_to_stacks 0FKZ "universal_finite_free_family" scheme

/-- The image in `A_d` of the universal structure constant `aᵏᵢⱼ`. -/
def universalStructureConstant (d : ℕ) [NeZero d] (i j k : Fin d) :
    universalRing d :=
  Ideal.Quotient.mk (Ideal.span (universalRelations d)) (universalCoeff d i j k)

/-- Every universal relation vanishes in the universal ring. -/
private theorem mk_eq_zero_of_mem_universalRelations (d : ℕ) [NeZero d] {r : MvPolynomial _ ℤ}
    (hr : r ∈ universalRelations d) :
    Ideal.Quotient.mk (Ideal.span (universalRelations d)) r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hr)

/-- The universal structure constants satisfy the associativity relation. -/
lemma universalStructureConstant_assoc (d : ℕ) [NeZero d] (i j k m : Fin d) :
    ∑ l, universalStructureConstant d i j l * universalStructureConstant d l k m =
      ∑ l, universalStructureConstant d i l m * universalStructureConstant d j k l := by
  apply sub_eq_zero.mp
  simpa only [universalStructureConstant, map_sub, map_sum, map_mul] using
    mk_eq_zero_of_mem_universalRelations d (Or.inl (Or.inl ⟨i, j, k, m, rfl⟩))

/-- The universal structure constants are symmetric in their first two indices. -/
lemma universalStructureConstant_comm (d : ℕ) [NeZero d] (i j k : Fin d) :
    universalStructureConstant d i j k = universalStructureConstant d j i k := by
  apply sub_eq_zero.mp
  simpa only [universalStructureConstant, map_sub] using
    mk_eq_zero_of_mem_universalRelations d (Or.inl (Or.inr ⟨i, j, k, rfl⟩))

/-- The first basis vector is a unit for the universal structure constants. -/
lemma universalStructureConstant_unit (d : ℕ) [NeZero d] (i j : Fin d) :
    universalStructureConstant d i 0 j = if i = j then 1 else 0 := by
  apply sub_eq_zero.mp
  simpa [universalStructureConstant] using
    mk_eq_zero_of_mem_universalRelations d (Or.inr ⟨i, j, rfl⟩)

/-- The unit relation for the universal structure constants, in the first index. -/
lemma universalStructureConstant_zero_left (d : ℕ) [NeZero d] (j k : Fin d) :
    universalStructureConstant d 0 j k = if j = k then 1 else 0 := by
  rw [universalStructureConstant_comm, universalStructureConstant_unit]

/-- The free carrier `B_d`, written using its coefficients in the distinguished basis. -/
@[stacks 0FKZ "universal_finite_free_family"]
structure UniversalFiniteFreeModule (d : ℕ) [NeZero d] where
  /-- The coefficient of each distinguished basis vector. -/
  coeff : Fin d →
    universalRing d

/-- The distinguished basis vector `e_i`. -/
@[stacks 0FKZ "universal_finite_free_family"]
def universalBasisVector (d : ℕ) [NeZero d] (i : Fin d) :
    UniversalFiniteFreeModule d where
  coeff j := if i = j then 1 else 0

/-- The prescribed unit `e_1` (indexed by `0` in `Fin d`). -/
@[stacks 0FKZ "universal_finite_free_family"]
def universalUnit (d : ℕ) [NeZero d] : UniversalFiniteFreeModule d :=
  universalBasisVector d 0

/-- Multiplication on `B_d` prescribed by the universal structure constants. -/
@[stacks 0FKZ "universal_finite_free_family"]
def universalMultiplication (d : ℕ) [NeZero d]
    (x y : UniversalFiniteFreeModule d) : UniversalFiniteFreeModule d where
  coeff k := ∑ i : Fin d, ∑ j : Fin d,
    x.coeff i * y.coeff j * universalStructureConstant d i j k

/-- A commutative algebra structure on the free carrier which realizes its prescribed
coordinatewise additive structure, unit, multiplication table, and scalar embedding. -/
structure UniversalAlgebraStructure (d : ℕ) [NeZero d] where
  /-- The commutative-ring structure on the free carrier. -/
  ring : CommRing (UniversalFiniteFreeModule d)
  /-- The `A_d`-algebra structure on the free carrier. -/
  algebra : letI := ring;
    Algebra
      (universalRing d)
      (UniversalFiniteFreeModule d)
  /-- Zero has vanishing coefficients. -/
  zero_coeff : letI := ring;
    ∀ i, (0 : UniversalFiniteFreeModule d).coeff i = 0
  /-- Addition is coordinatewise. -/
  add_coeff : letI := ring;
    ∀ x y i, (x + y : UniversalFiniteFreeModule d).coeff i = x.coeff i + y.coeff i
  /-- Negation is coordinatewise. -/
  neg_coeff : letI := ring;
    ∀ x i, (-x : UniversalFiniteFreeModule d).coeff i = -x.coeff i
  /-- The unit is the prescribed one. -/
  one_eq : letI := ring; (1 : UniversalFiniteFreeModule d) = universalUnit d
  /-- Multiplication is the prescribed one. -/
  mul_eq : letI := ring; ∀ x y, x * y = universalMultiplication d x y
  /-- The scalar embedding places a scalar in the first coordinate. -/
  algebraMap_coeff : letI := ring; letI := algebra;
    ∀ (a :
      universalRing d) (i : Fin d),
      (algebraMap
        (universalRing d)
        (UniversalFiniteFreeModule d) a).coeff i = if i = 0 then a else 0

/-- The affine total space `Y_d = Spec(B_d)`, after equipping the prescribed
multiplication table with its commutative-ring structure. -/
@[stacks 0FKZ "universal_finite_free_family"]
def universalTotalScheme (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d) :
    Scheme.{u} :=
  letI := s.ring
  Spec (.of (ULift.{u} (UniversalFiniteFreeModule d)))

/-- The affine morphism `pi_d : Y_d ⟶ X_d` induced by the universal algebra map. -/
@[stacks 0FKZ "universal_finite_free_family"]
def universalFamily (d : ℕ) [NeZero d] (s : UniversalAlgebraStructure d) :
    universalTotalScheme.{u} d s ⟶
      scheme.{u} d := by
  letI := s.ring
  letI := s.algebra
  exact Scheme.Spec.map (CommRingCat.ofHom
    (RingHom.ulift (algebraMap (universalRing d) (UniversalFiniteFreeModule d)))).op

end AlgebraicGeometry
