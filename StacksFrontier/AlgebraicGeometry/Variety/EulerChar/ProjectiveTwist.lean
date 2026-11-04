module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Twisting a module on projective space over a ring

Projective space over a ring is the base change of integral projective space, and its
twisting sheaves are pulled back from the corresponding integral twists.  Twisting a module
sheaf by one of them is the tensor product taken over the structure sheaf.

## Main definitions

* `AlgebraicGeometry.projectiveTwist` is the twist of a module sheaf on projective space over
  a ring by the pullback of the integral twisting sheaf.

## Implementation notes

The grading of the polynomial ring by homogeneous components is supplied locally, since the
twisting sheaf of integral projective space is indexed by it.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The twist of a module sheaf on projective space over a ring, using the
pullback of the twisting sheaf from integral projective space. -/
noncomputable abbrev projectiveTwist {R : Type u} [CommRing R] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) (d : ℤ) :
    (projectiveSpaceOverRing n (.of R)).Modules := by
  letI : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  let X := projectiveSpaceOverRing n (.of R)
  exact (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj (F)).obj (((Scheme.Modules.pullback
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d))))

end AlgebraicGeometry
