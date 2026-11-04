module

public import StacksFrontier.Exercises.NonExercises.FaithfullyFlatSelfBaseChange

/-!
# Faithful flatness from a description of the self tensor product as a base change

Let `R ⟶ C` be a universally injective map of commutative rings. If `C ⊗_R C`, as a `C`-module
through its left factor, is isomorphic to a base change `C ⊗_A R'` of a flat `A`-module `R'`
along some ring map `A ⟶ C`, then both coprojections `C ⟶ C ⊗_R C` are flat and `R ⟶ C` is
faithfully flat by Stacks 0GRM
(`Algebra.faithfullyFlat_of_flat_selfTensor_of_universallyInjective`).

## Main results

* `Algebra.flat_includeRight_of_flat_includeLeft`: the right coprojection is flat as soon as the
  left one is.
* `Algebra.faithfullyFlat_of_universallyInjective_of_selfTensorEquivBaseChange`: the statement
  above.

## References

* [Stacks Project, Tag 0GRM](https://stacks.math.columbia.edu/tag/0GRM)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

variable {R : Type u} [CommRing R] {C : Type u} [CommRing C] [Algebra R C]

/-- The right coprojection `C ⟶ C ⊗_R C` is flat as soon as the left one is. -/
theorem flat_includeRight_of_flat_includeLeft
    (hleft : ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toRingHom).Flat) :
    ((Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toRingHom).Flat := by
  have h : (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toRingHom =
      (Algebra.TensorProduct.comm R C C).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toRingHom := by
    ext c
    simp
  rw [h]
  exact hleft.comp (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R C C).bijective)

/-- **Faithful flatness from a description of `C ⊗_R C` as a base change.** Let `R ⟶ C` be
universally injective, `A ⟶ C` a ring map and `R'` a flat `A`-module. If `C ⊗_R C`, a `C`-module
through its left factor, is isomorphic to `C ⊗_A R'`, then `R ⟶ C` is faithfully flat. -/
theorem faithfullyFlat_of_universallyInjective_of_selfTensorEquivBaseChange
    {A : Type u} [CommRing A] [Algebra A C] {R' : Type u} [AddCommGroup R'] [Module A R']
    [Module.Flat A R'] (hRC : Algebra.UniversallyInjective R C)
    (e : (C ⊗[R] C) ≃ₗ[C] (C ⊗[A] R')) :
    (algebraMap R C).FaithfullyFlat := by
  have hflat : Module.Flat C (C ⊗[R] C) := Module.Flat.of_linearEquiv e
  have hleft : ((Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toRingHom).Flat := by
    let : Algebra C (C ⊗[R] C) := Algebra.TensorProduct.leftAlgebra
    convert RingHom.flat_algebraMap_iff.mpr hflat using 1
    ext c
    rfl
  exact faithfullyFlat_of_flat_selfTensor_of_universallyInjective hleft
    (flat_includeRight_of_flat_includeLeft hleft) hRC

end Algebra
