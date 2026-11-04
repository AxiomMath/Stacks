module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GaloisFixedComponentDescent
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BaseChangeTower
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.GaloisInvariantClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.OrbitDecomposition

/-!
# The base change comparison along a tower and the Galois action on geometric components

Let `X` be a scheme over a field `k`. The comparison of the base changes of `X` along a tower
of fields `k → E → K` is given by the two projection equations of the canonical morphism
`X_K ⟶ X_E`, and the Galois action on the geometric irreducible components of a base change is
the pointwise image under the Galois self-maps of that base change.

## Main results

* `AlgebraicGeometry.baseChangeComparison_fst` and
  `AlgebraicGeometry.baseChangeComparison_snd`: the two projection equations characterizing the
  comparison morphism of base changes along a tower of fields.
* `AlgebraicGeometry.galoisActionOnGeometricIrreducibleComponents_coe`: the Galois action on the
  geometric irreducible components is the image under the Galois self-maps of the base change.

## Implementation notes

The two statements of Stacks tag 04KZ that these equations feed —
`AlgebraicGeometry.exists_finite_subextension_defining_component` and
`AlgebraicGeometry.exists_finite_single_orbit_decomposition` — are proved in
`StacksFrontier/AlgebraicGeometry/Variety/GeometricIrreducibleComponents/FiniteExtension.lean` and
`StacksFrontier/AlgebraicGeometry/Variety/GeometricIrreducibleComponents/OrbitDecomposition.lean`,
which this file imports, so that its consumers see them unchanged.

Base changes are categorical pullbacks.

The two-step base change comparison along `k → E → K` is
`AlgebraicGeometry.baseChangeTowerIsoTo`.

## References

* [Stacks Project, Tag 04KZ](https://stacks.math.columbia.edu/tag/04KZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

section Comparison

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  (X : Scheme.{u}) (f : X ⟶ Spec (.of R))

/-- The comparison of base changes along a tower lies over `X`. -/
public theorem baseChangeComparison_fst :
    baseChangeComparison R S T X f ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
  pullback.lift_fst _ _ _

/-- On the second factor, the comparison of base changes along a tower is the extension of
scalars. -/
public theorem baseChangeComparison_snd :
    baseChangeComparison R S T X f ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T)) :=
  pullback.lift_snd _ _ _

end Comparison

/-! ### Galois self-maps of a base change -/

/-- The Galois action on geometric irreducible components is the pointwise image under the
Galois self-map of the base change. -/
public theorem galoisActionOnGeometricIrreducibleComponents_coe
    (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))
    (σ : MulOpposite (K ≃ₐ[k] K))
    (Z : (galoisActionOnGeometricIrreducibleComponents k K X).V) :
    (ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k K X).ρ σ) Z).1 =
      (galoisBaseChangeMap k K X.left X.hom σ.unop).base '' Z.1 := rfl

end AlgebraicGeometry

end
