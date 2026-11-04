module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfectAnyModuleUniverse
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernelPerfect

/-!
# Trivial duality for an invertible kernel at an arbitrary module universe

Let `f : R → A` be a surjection of commutative rings whose kernel `I` is an invertible
`R`-module, and let `N = Hom_A(I ⊗_R A, A)` be the inverse of the invertible `A`-module
`I ⊗_R A`. Then `RHom_R(A, -) : D(R) ⥤ D(A)` is derived tensoring over `R` with `N[-1]`, for
modules in any universe above the ring universe.

## Main results

* `nonempty_derivedHom_iso_derivedTensor_conormalInverseShift_anyModuleUniverse`: for every model
  `T` of the derived change-of-rings tensor product with `N[-1]`, the derived coextension of
  scalars `RHom_R(A, -)` is isomorphic to `T.F`.

## Implementation notes

The change-of-rings bundle `Dualizing.Stacks0BZE.bundle` has its universe annotation inferred as
`v`, while the dual complex of Stacks 0BZE produces `max v u`. The two readings have the same
module universe and the same derived tensor functor, by
`CochainComplex.DerivedTensor.canonicalDerivedTensorUniverseIso`.

## References

* [Stacks Project, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 0BYK](https://stacks.math.columbia.edu/tag/0BYK)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing.InvertibleKernel

variable {R A : Type u} [CommRing R] [CommRing A]

/-- For a surjection `f : R → A` whose kernel is an invertible `R`-module, derived coextension of
scalars `RHom_R(A, -) : D(R) ⥤ D(A)` is derived tensoring over `R` with the conormal inverse shift
`N[-1]`, for any model of the derived change-of-rings tensor product with that factor and at any
module universe above the ring universe. -/
@[stacks 0BZH "at an arbitrary module universe above the ring universe, with no carried \
hypothesis"]
theorem nonempty_derivedHom_iso_derivedTensor_conormalInverseShift_anyModuleUniverse
    (f : R →+* A) (hf : Function.Surjective f)
    (hI : Module.Invertible R (RingHom.ker f)) :
    letI := f.toAlgebra
    ∀ T : DerivedTensorChangeOfRings f (conormalInverseShift.{u, v} R A),
      Nonempty (Dualizing.derivedHom.{u, v} f ≅ T.F) := by
  let := f.toAlgebra
  intro T
  obtain ⟨e⟩ :=
    Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse.{u, v}
      f (isPerfectModule_of_surjective_of_invertible_ker hf hI)
      (Stacks0BZE.dualComplex.{u, v} f) ⟨Stacks0BZE.dualComplexIso.{u, v} f⟩
  refine ⟨e ≪≫ (canonicalDerivedTensorUniverseIso.{u, v} f
      (Stacks0BZE.dualComplex.{u, v} f)).symm ≪≫
    derivedTensorIsoOfDerivedIso f
      (Stacks0BZE.dualComplexIso.{u, v} f ≪≫ derivedHomUnitObjectIsoSingle.{u, v} hf hI ≪≫
        (conormalInverseShiftIso.{u, v} R A).symm)
      (Stacks0BZE.bundle.{u, v} f) T⟩

end Dualizing.InvertibleKernel

end
