module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjGradedRing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwist
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# The twist of a quasi-coherent module on projective space is quasi-coherent

`AlgebraicGeometry.projectiveTwist n ℱ d` is the tensor product of `ℱ` with the inverse image
of the `d`-th twisting sheaf of integral projective space. Quasi-coherence of the twist is the
composite of three facts: the sheaf attached to a graded module on a
projective spectrum is quasi-coherent ([Stacks, Tag 01MB]), the inverse image of a
quasi-coherent module is quasi-coherent ([Stacks, Tag 01BG]), and the tensor product of two
quasi-coherent modules is quasi-coherent ([Stacks, Tag 01CE]).

## Main results

* `AlgebraicGeometry.isQuasicoherent_projectiveTwist`: the twist of a quasi-coherent module on
  projective space over a ring is quasi-coherent, as an instance.

## Implementation notes

The grading of the polynomial ring by homogeneous components is supplied by a local `let`, as
in the definition of `AlgebraicGeometry.projectiveTwist` itself, because
`MvPolynomial.gradedAlgebra` is not a global instance.

Quasi-coherence of the twisting sheaf of integral projective space is written out with its
universe parameters, rather than left to `inferInstance` inside the application of
[Stacks, Tag 01BG]: the instance for the sheaf attached to a graded module is stated at
`SheafOfModules.IsQuasicoherent.{u, u, u}`, and instance search in the inverse-image position
leaves the universes as metavariables and fails.

`AlgebraicGeometry.projectiveTwist` forms its tensor product with the sheaf condition of the
structure sheaf read through `forget₂ CommRingCat RingCat`, whereas the instance
`AlgebraicGeometry.tensorSheaf_isQuasicoherent` of [Stacks, Tag 01CE] forms it with the sheaf
condition of the ringed space; the two tensor products are equal by `rfl`
(`Stacks.TensorSheafDedup.tensorSheaf_eq`), so the instance applies to the twist as it stands,
with its arguments supplied explicitly.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- **The twist of a quasi-coherent module on projective space over a ring is
quasi-coherent.** It is the tensor product of the module with the inverse image of the twisting
sheaf of integral projective space; the twisting sheaf is quasi-coherent, inverse images of
quasi-coherent modules are quasi-coherent, and so are tensor products of them. -/
public instance isQuasicoherent_projectiveTwist {R : Type u} [CommRing R] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) [F.IsQuasicoherent] (d : ℤ) :
    (projectiveTwist n F d).IsQuasicoherent := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  have htw : SheafOfModules.IsQuasicoherent.{u, u, u} (ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d) := inferInstance
  have hG : ((Scheme.Modules.pullback
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d)).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _
      (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R))).toLRSHom.toShHom _ htw
  exact @tensorSheaf_isQuasicoherent
    (projectiveSpaceOverRing n (.of R)).toRingedSpace F _ ‹_› hG

end AlgebraicGeometry

end
