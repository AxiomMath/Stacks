module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The nondegenerate quadratic relation on a two-dimensional cotangent space

Let `(A, 𝔪)` be a local ring with residue field `κ` and cotangent space `𝔪/𝔪²`. A *nodal
quadratic relation* on `A` is a symmetric tensor `q ∈ Sym²_κ(𝔪/𝔪²)` of the shape
`a x² + b x y + c y²` for a basis `x, y` of `𝔪/𝔪²` lifted to `x, y ∈ 𝔪`, whose discriminant
`4ac - b²` is a unit of `κ` and whose lift `a x² + b x y + c y²` lies in `𝔪³`.

## Main definitions

* `Stacks.Curves.BinaryIndex` — a two-element index type in the universe of the residue field.
* `Stacks.Curves.binaryQuadraticTensor` — the symmetric tensor `a X₀² + b X₀X₁ + c X₁²`.
* `Stacks.Curves.IsNodalQuadraticRelation` — the predicate above on a symmetric tensor.
* `Stacks.Curves.HasNodalQuadraticRelation` — the existence of such a tensor.

## Main results

* `Stacks.Curves.hasNodalQuadraticRelation_iff_exists_basis` — the intrinsic tensor condition is
  equivalent to its expression in lifted cotangent-space coordinates.

## References

* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- A two-element index type lifted to the universe of the coefficient field. -/
public abbrev BinaryIndex (_K : Type u) := ULift.{u} (Fin 2)

/-- The symmetric tensor `a X₀² + b X₀X₁ + c X₁²` in a module with basis `e`. -/
public noncomputable def binaryQuadraticTensor {K : Type u} [Field K] {V : Type v}
    [AddCommGroup V] [Module K V] (e : Module.Basis (BinaryIndex K) K V) (a b c : K) :
    SymmetricPower K (BinaryIndex K) V :=
  a • SymmetricPower.tprod K (fun _ ↦ e ⟨0⟩) +
    b • SymmetricPower.tprod K (fun i ↦ e ((Equiv.swap (⟨0⟩ : BinaryIndex K) ⟨1⟩) i)) +
    c • SymmetricPower.tprod K (fun _ ↦ e ⟨1⟩)

/-- A symmetric quadratic tensor on the cotangent space which is nondegenerate and maps to
zero in `𝔪² / 𝔪³`.

The elements `x` and `y` lift the basis used to write the tensor. The coefficients are chosen
in the local ring, and their images in the residue field are its coefficients. -/
public def IsNodalQuadraticRelation (A : Type v) [CommRing A] [IsLocalRing A]
    (q : SymmetricPower (ResidueField A) (BinaryIndex (ResidueField A))
      (CotangentSpace A)) : Prop :=
  ∃ (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (a b c : A),
    e ⟨0⟩ = (maximalIdeal A).toCotangent x ∧
      e ⟨1⟩ = (maximalIdeal A).toCotangent y ∧
      q = binaryQuadraticTensor e (residue A a) (residue A b) (residue A c) ∧
      residue A (4 * a * c - b ^ 2) ≠ 0 ∧
      a * x.1 ^ 2 + b * x.1 * y.1 + c * y.1 ^ 2 ∈ (maximalIdeal A) ^ 3

/-- The two-dimensional cotangent space carries a nondegenerate symmetric quadratic tensor
which maps to zero in `𝔪² / 𝔪³`. -/
public def HasNodalQuadraticRelation (A : Type v) [CommRing A] [IsLocalRing A] : Prop :=
  ∃ q : SymmetricPower (ResidueField A) (BinaryIndex (ResidueField A))
      (CotangentSpace A),
    IsNodalQuadraticRelation A q

/-- The intrinsic symmetric-tensor condition is equivalent to its expression in lifted
cotangent-space coordinates. -/
public theorem hasNodalQuadraticRelation_iff_exists_basis (A : Type v) [CommRing A]
    [IsLocalRing A] :
    HasNodalQuadraticRelation A ↔
      ∃ (x y : maximalIdeal A)
        (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
        (a b c : A),
        e ⟨0⟩ = (maximalIdeal A).toCotangent x ∧
          e ⟨1⟩ = (maximalIdeal A).toCotangent y ∧
          residue A (4 * a * c - b ^ 2) ≠ 0 ∧
          a * x.1 ^ 2 + b * x.1 * y.1 + c * y.1 ^ 2 ∈ (maximalIdeal A) ^ 3 :=
  ⟨fun ⟨_, x, y, e, a, b, c, hx, hy, _, hnd, hm⟩ => ⟨x, y, e, a, b, c, hx, hy, hnd, hm⟩,
    fun ⟨x, y, e, a, b, c, hx, hy, hnd, hm⟩ =>
      ⟨_, x, y, e, a, b, c, hx, hy, rfl, hnd, hm⟩⟩

end Stacks.Curves

end
