module

public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Smooth.RegularRing

@[expose] public section

universe u v w

/-!
# Geometric regularity ascends along a smooth map of algebras

Let `k` be a field and let `A → B` be a smooth map of `k`-algebras. If `A` is geometrically regular
over `k`, then so is `B`.

## Main results

* `Stacks.GeometricallyRegular.SmoothAscent.solution`: a smooth algebra over a geometrically
  regular `k`-algebra is geometrically regular over `k`.
* `Algebra.IsGeometricallyRegular.of_smooth`: the same statement, in the namespace `Algebra`.

## References

* [Stacks 07QF](https://stacks.math.columbia.edu/tag/07QF)
-/

open scoped TensorProduct

@[expose] public section

namespace Stacks.GeometricallyRegular.SmoothAscent

section BaseChangeComp

variable (k A B K : Type*) [CommSemiring k] [CommSemiring A] [CommSemiring B] [CommSemiring K]
  [Algebra k A] [Algebra k B] [Algebra k K] [Algebra A B] [IsScalarTower k A B]

/-- Extending the scalars of `B` from `A` to `A ⊗[k] K` gives the base change of `B` from `k` to
`K`: the isomorphism of `k`-algebras `(A ⊗[k] K) ⊗[A] B ≃ₐ[k] K ⊗[k] B`. -/
private def baseChangeCompAlgEquiv : ((A ⊗[k] K) ⊗[A] B) ≃ₐ[k] (K ⊗[k] B) :=
  (((Algebra.TensorProduct.comm A (A ⊗[k] K) B).trans
        (Algebra.TensorProduct.cancelBaseChange k A A B K)).restrictScalars k).trans
    (Algebra.TensorProduct.comm k B K)

/-- The isomorphism `Stacks.GeometricallyRegular.SmoothAscent.baseChangeCompAlgEquiv` sends
`(a ⊗ x) ⊗ b` to `x ⊗ a • b`. -/
private theorem baseChangeCompAlgEquiv_tmul_tmul (a : A) (x : K) (b : B) :
    baseChangeCompAlgEquiv k A B K ((a ⊗ₜ x) ⊗ₜ b) = x ⊗ₜ (a • b) := by
  simp [baseChangeCompAlgEquiv]

end BaseChangeComp

/-- Regularity of a base change ascends along a smooth map: if `A → B` is a smooth map of
`k`-algebras and `K` is a `k`-algebra with `K ⊗[k] A` regular, then `K ⊗[k] B` is regular. -/
private theorem isRegularRing_tensorProduct_of_smooth {k : Type*} (A : Type*) {B K : Type*}
    [CommRing k] [CommRing A] [CommRing B] [CommRing K] [Algebra k A] [Algebra k B] [Algebra k K]
    [Algebra A B] [IsScalarTower k A B] [Algebra.Smooth A B] [IsRegularRing (K ⊗[k] A)] :
    IsRegularRing (K ⊗[k] B) :=
  have : IsRegularRing (A ⊗[k] K) :=
    .of_ringEquiv (Algebra.TensorProduct.comm k K A).toRingEquiv
  have : IsRegularRing ((A ⊗[k] K) ⊗[A] B) := Algebra.isRegularRing_of_smooth (A ⊗[k] K) _
  .of_ringEquiv (baseChangeCompAlgEquiv k A B K).toRingEquiv

/-- Let `k` be a field and let `A → B` be a smooth map of `k`-algebras. If `A` is geometrically
regular over `k`, then so is `B`. -/
public theorem solution {k : Type u} (A : Type v) {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Algebra.Smooth A B] [Algebra.IsGeometricallyRegular k A] :
    Algebra.IsGeometricallyRegular k B :=
  ⟨fun _ ↦ isRegularRing_tensorProduct_of_smooth A⟩

end Stacks.GeometricallyRegular.SmoothAscent

end

@[expose] public section

namespace Algebra

/-- **Geometric regularity ascends along smooth maps of algebras.** Let `k` be a field and let
`A → B` be a smooth map of `k`-algebras. If `A` is geometrically regular over `k`, then so is
`B`. -/
@[stacks 07QF "The source's smooth `k`-algebra map `A → B` is `Algebra A B` with \
  `IsScalarTower k A B` and `Algebra.Smooth A B`, the latter being `(algebraMap A B).Smooth` by \
  `RingHom.smooth_algebraMap` and being Definition 00T2 by Proposition 00TN; geometric regularity \
  is `Algebra.IsGeometricallyRegular` (Definition 0382), which already implies the Noetherianness \
  Definition 0382 assumes. Named after the sibling 07NH, \
  `IsGeometricallyRegular.of_faithfullyFlat`. See the module docstring."]
public theorem IsGeometricallyRegular.of_smooth {k : Type u} (A : Type v) {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Algebra.Smooth A B] [IsGeometricallyRegular k A] :
    IsGeometricallyRegular k B :=
  Stacks.GeometricallyRegular.SmoothAscent.solution A

end Algebra

end
