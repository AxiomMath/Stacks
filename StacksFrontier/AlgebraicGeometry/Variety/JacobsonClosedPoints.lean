module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksCore.Tactic.StacksAttribute

/-!
# Schemes locally of finite type over a field

Let `k` be a field and let `X` be a scheme locally of finite type over `k`. Two facts hold with
no further hypothesis: the residue field at a closed point of `X` is an algebraic extension of
`k`, and `X` is a Jacobson scheme, that is, the closed points of every closed subset of `X` are
dense in it.

## Main results

* `AlgebraicGeometry.isAlgebraic_residueField_of_isClosed`: the residue field at a closed point
  of a scheme locally of finite type over `k` is algebraic over `k`.
* `AlgebraicGeometry.isAlgebraic_residueField_and_jacobsonSpace`: the residue fields at closed
  points are algebraic over `k`, and `X` is a Jacobson scheme.

## Implementation notes

The `k`-algebra structure on `κ(x)` is not an instance: it is the one attached to the ring
homomorphism `k ⟶ Γ(X, ⊤) ⟶ κ(x)` built from the structure morphism and evaluation at `x`, and
each statement introduces it by a `letI`.

Being a Jacobson scheme ([Stacks, Tag 01P2]) is `JacobsonSpace` of the underlying space.

## References

* [Stacks Project, Tag 0478](https://stacks.math.columbia.edu/tag/0478)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The residue field at a closed point of a scheme locally of finite type over a field is
algebraic over that field. -/
public theorem isAlgebraic_residueField_of_isClosed (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] {x : X} (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.IsAlgebraic k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    have := isClosed_singleton_iff_isClosedImmersion.mp hx
    inferInstance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ p) := inferInstance
  rw [← p.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have : Algebra.FiniteType k (X.residueField x) := by
    show RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  have : Module.Finite k (X.residueField x) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Algebra.IsAlgebraic.of_finite k (X.residueField x)

/-- Let `X` be a scheme locally of finite type over a field `k`. Then (1) for every closed point
`x` of `X` the extension `κ(x)/k` is algebraic, and (2) `X` is a Jacobson scheme, that is, its
underlying space is a Jacobson space. -/
@[stacks 0478, sga "4 VIII 3.13" "partial"]
public theorem isAlgebraic_residueField_and_jacobsonSpace (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] :
    (∀ x : X, IsClosed ({x} : Set X) →
        letI : Algebra k (X.residueField x) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom.toAlgebra
        Algebra.IsAlgebraic k (X.residueField x)) ∧ JacobsonSpace X :=
  ⟨fun _ hx ↦ isAlgebraic_residueField_of_isClosed p hx, LocallyOfFiniteType.jacobsonSpace p⟩

end AlgebraicGeometry

end
