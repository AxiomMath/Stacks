module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.Algebra.GradedModule.ExternalShift
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.PoincareDuality
public import StacksCore.Tactic.StacksAttribute

/-!
# Poincaré duality and the pushforward of a Weil cohomology theory

A contravariant, multiplicative, integer-graded cohomology theory on the smooth projective
varieties over a field `k`, with coefficients in a field `F`, satisfies *Poincaré duality* when
each cohomology group is finite dimensional, vanishes outside the range `[0, 2d]`, and the cup
product in complementary degrees followed by the trace map `∫_X` is a perfect pairing. This file
packages that data and those axioms — the data `(D1)` and `(D3)` of Section 45.9 together with
axiom `(A)` — and constructs the pushforward they determine:

`f_* : H^{2d - i}(X) ⟶ H^{2e - i}(Y)` is the contragredient of `f^* : H^i(Y) ⟶ H^i(X)`,
characterised by `∫_X f^*b ∪ a = ∫_Y b ∪ f_*a` for all `b ∈ H^i(Y)`.

## Main definitions

* `ExternallyGradedAlgebra.IsGradedCommutative`: graded commutativity of an externally graded
  algebra, i.e. `a ∪ b = (-1)^{ij} b ∪ a` for homogeneous `a`, `b` of degrees `i`, `j`.
* `ExternallyGradedAlgebra.tracePairing`: the pairing `(a, b) ↦ ∫ a ∪ b` in complementary
  degrees.
* `Stacks.WeilCohomology.SmoothProjective`: smooth projective varieties over `k`, as an object
  property of schemes over `k`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup`: the cohomology theory together with
  the Poincaré duality axioms.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.pushforward`: the pushforward adjoint
  to pullback.

## Main results

* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.integration_pullback_mul`: the
  defining trace equation `∫_X f^*b ∪ a = ∫_Y b ∪ f_*a`.
* `Stacks.WeilCohomology.PoincareDualityPushforwardSetup.eq_pushforward_iff`: that equation
  characterises the pushforward uniquely.

## References

* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

/-- An externally graded algebra is *graded commutative* when homogeneous elements commute up to
the Koszul sign: `a ∪ b = (-1)^{ij} b ∪ a` for `a` of degree `i` and `b` of degree `j`. -/
structure ExternallyGradedAlgebra.IsGradedCommutative {R : Type v} [CommRing R]
    (A : ExternallyGradedAlgebra.{v, w} R) : Prop where
  /-- Homogeneous elements commute up to the Koszul sign. -/
  graded_comm : ∀ (i j : ℤ) (a : A.piece i) (b : A.piece j),
    A.mul i j a b ≍ DifferentialGraded.gradedSign R (i * j) • A.mul j i b a

/-- The trace pairing `(a, b) ↦ ∫ a ∪ b` of an externally graded algebra in complementary
degrees `i` and `2d - i`, for a chosen linear functional `∫` on the top piece. -/
def ExternallyGradedAlgebra.tracePairing {F : Type v} [Field F]
    (A : ExternallyGradedAlgebra.{v, w} F) (d : ℕ)
    (integration : A.piece (2 * (d : ℤ)) →ₗ[F] F) (i : ℤ) :
    A.piece i →ₗ[F] A.piece (2 * (d : ℤ) - i) →ₗ[F] F :=
  (A.mul i (2 * (d : ℤ) - i)).compr₂
    (integration.comp (ExternallyGraded.degreeCast (R := F) (X := A.piece) (by omega)))

namespace Stacks.WeilCohomology

/-- Smooth projective varieties over a field `k`, as an object property of the category of
schemes over `k`: the structure morphism makes the scheme a smooth variety and is projective. -/
def SmoothProjective (k : Type u) [Field k] : ObjectProperty (Over (Spec (.of k))) :=
  fun X => IsSmoothVariety k X.hom ∧ IsProjectiveMorphism X.hom

/-- The data `(D1)` and `(D3)` of a classical Weil cohomology theory over an algebraically closed
field `k` with coefficients in a field `F` of characteristic zero, together with axiom `(A)`,
Poincaré duality: a contravariant multiplicative graded-commutative cohomology theory on the
smooth projective varieties over `k` whose groups are finite dimensional, vanish outside
`[0, 2d]`, and whose cup-product trace pairings in complementary degrees are perfect. -/
structure PoincareDualityPushforwardSetup (k : Type u) [Field k] [IsAlgClosed k]
    (F : Type v) [Field F] [CharZero F] where
  /-- The graded cohomology algebra of a smooth projective variety. -/
  H : (SmoothProjective k).FullSubcategory → ExternallyGradedAlgebra.{v, w} F
  /-- Cup product is graded commutative. -/
  gradedComm : ∀ X, (H X).IsGradedCommutative
  /-- The dimension of a smooth projective variety. -/
  dimension : (SmoothProjective k).FullSubcategory → ℕ
  /-- The chosen dimension is the topological dimension of the underlying space. -/
  dimension_eq : ∀ X, topologicalKrullDim X.obj.left = (dimension X : WithBot ℕ∞)
  /-- Cohomological pullback along a morphism of smooth projective varieties. -/
  pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory},
    (X ⟶ Y) → ∀ i : ℤ, (H Y).piece i →ₗ[F] (H X).piece i
  /-- Pullback along an identity is the identity. -/
  pullback_id : ∀ (X) (i : ℤ), pullback (𝟙 X) i = LinearMap.id
  /-- Pullback is contravariantly functorial. -/
  pullback_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (i : ℤ),
    pullback (f ≫ g) i = (pullback f i).comp (pullback g i)
  /-- Pullback preserves the unit class. -/
  pullback_one : ∀ {X Y} (f : X ⟶ Y), pullback f 0 (H Y).one = (H X).one
  /-- Pullback is multiplicative for the cup product. -/
  pullback_mul : ∀ {X Y} (f : X ⟶ Y) (i j : ℤ) (a : (H Y).piece i) (b : (H Y).piece j),
    pullback f (i + j) ((H Y).mul i j a b) =
      (H X).mul i j (pullback f i a) (pullback f j b)
  /-- The trace map `∫_X : H^{2d}(X) ⟶ F`, an isomorphism. -/
  integration : ∀ X, (H X).piece (2 * (dimension X : ℤ)) ≃ₗ[F] F
  /-- Every cohomology group is finite dimensional. -/
  finite : ∀ X i, FiniteDimensional F ((H X).piece i)
  /-- The cup-product trace pairing in complementary degrees is perfect. -/
  perfect : ∀ X i,
    ((H X).tracePairing (dimension X) (integration X).toLinearMap i).IsPerfPair
  /-- Cohomology vanishes outside the range `[0, 2d]`. -/
  bounded : ∀ X i, (i < 0 ∨ 2 * (dimension X : ℤ) < i) → ∀ a : (H X).piece i, a = 0

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (S : PoincareDualityPushforwardSetup.{u, v, w} k F)
  {X Y : (SmoothProjective k).FullSubcategory}

/-- The pushforward `f_* : H^{2d - i}(X) ⟶ H^{2e - i}(Y)` determined by Poincaré duality: the
contragredient of `f^* : H^i(Y) ⟶ H^i(X)` with respect to the cup-product trace pairings. -/
noncomputable def PoincareDualityPushforwardSetup.pushforward (f : X ⟶ Y) (i : ℤ) :
    (S.H X).piece (2 * (S.dimension X : ℤ) - i) →ₗ[F]
      (S.H Y).piece (2 * (S.dimension Y : ℤ) - i) :=
  haveI := S.perfect Y i
  Stacks.WeilCohomology.poincareDualPushforward
    ((S.H X).tracePairing (S.dimension X) (S.integration X).toLinearMap i)
    ((S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i)
    (S.pullback f i)

/-- The trace equation `∫_X f^*b ∪ a = ∫_Y b ∪ f_*a` defining the pushforward. -/
theorem PoincareDualityPushforwardSetup.integration_pullback_mul (f : X ⟶ Y) (i : ℤ)
    (b : (S.H Y).piece i) (a : (S.H X).piece (2 * (S.dimension X : ℤ) - i)) :
    (S.H X).tracePairing (S.dimension X) (S.integration X).toLinearMap i (S.pullback f i b) a =
      (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i b
        (S.pushforward f i a) :=
  have := S.perfect Y i
  Stacks.WeilCohomology.poincareDualPushforward_pairing
    ((S.H X).tracePairing (S.dimension X) (S.integration X).toLinearMap i)
    ((S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i)
    (S.pullback f i) b a

/-- A linear map is the Poincaré-duality pushforward exactly when it satisfies the trace equation
against every class of complementary degree; in particular the equation determines it. -/
theorem PoincareDualityPushforwardSetup.eq_pushforward_iff (f : X ⟶ Y) (i : ℤ)
    (g : (S.H X).piece (2 * (S.dimension X : ℤ) - i) →ₗ[F]
      (S.H Y).piece (2 * (S.dimension Y : ℤ) - i)) :
    g = S.pushforward f i ↔
      ∀ (b : (S.H Y).piece i) (a : (S.H X).piece (2 * (S.dimension X : ℤ) - i)),
        (S.H X).tracePairing (S.dimension X) (S.integration X).toLinearMap i
            (S.pullback f i b) a =
          (S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i b (g a) :=
  have := S.perfect Y i
  Stacks.WeilCohomology.eq_poincareDualPushforward_iff
    ((S.H X).tracePairing (S.dimension X) (S.integration X).toLinearMap i)
    ((S.H Y).tracePairing (S.dimension Y) (S.integration Y).toLinearMap i)
    (S.pullback f i) g

end Stacks.WeilCohomology

end
