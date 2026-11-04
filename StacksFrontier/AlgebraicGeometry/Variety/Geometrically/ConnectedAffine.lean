module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.RingTheory.GeometricallyConnected.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometric connectedness of an affine scheme

For a field `k` and a commutative `k`-algebra `A`, geometric connectedness of the affine
scheme `Spec A` over `Spec k` is equivalent to geometric connectedness of the algebra `A`.

## Main results

* `AlgebraicGeometry.geometricallyConnected_spec_iff` identifies the scheme-theoretic and
  algebraic notions of geometric connectedness for an affine scheme.

## References

* [Stacks Project, Tag 0386](https://stacks.math.columbia.edu/tag/0386)
-/

@[expose] public section

open CommRingCat

namespace AlgebraicGeometry

universe u

/-- An affine scheme is geometrically connected over a field if and only if its coordinate
algebra is geometrically connected over that field. -/
@[stacks 0386]
public theorem geometricallyConnected_spec_iff (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] :
    GeometricallyConnected (Spec.map (ofHom (algebraMap k A))) ↔
      Algebra.IsGeometricallyConnected k A := by
  rw [AlgebraicGeometry.geometricallyConnected_iff,
    AlgebraicGeometry.geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine ⟨fun h ↦ ⟨fun K _ _ ↦ ?_⟩, fun h K _ _ ↦ ?_⟩
  · exact (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k A K).toRingEquiv).connectedSpace_iff.mp
      ((Scheme.homeoOfIso (pullbackSpecIso k A K)).connectedSpace_iff.mp (h K))
  · exact (Scheme.homeoOfIso (pullbackSpecIso k A K)).connectedSpace_iff.mpr
      ((PrimeSpectrum.homeomorphOfRingEquiv
        (Algebra.TensorProduct.comm k A K).toRingEquiv).connectedSpace_iff.mpr
        (h.connectedSpace_primeSpectrum_tensorProduct K))

end AlgebraicGeometry
