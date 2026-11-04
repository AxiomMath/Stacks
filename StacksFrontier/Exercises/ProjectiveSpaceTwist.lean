module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist

/-!
# Twisting a sheaf on the projective plane

For a sheaf of modules `ℱ` on the projective plane over a field, its `n`-th twist is the tensor
product `ℱ ⊗ 𝒪(n)`.

`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` already constructs that tensor
product on the `Proj` of an arbitrary nonnegatively graded ring, so in particular for the
standard grading on `k[X₀, X₁, X₂]` and quasi-coherent sheaves there. That more general
construction is the one recorded here, rather than a synonym specific to the projective plane.

## References

* [Stacks Project, Tag 02AX](https://stacks.math.columbia.edu/tag/02AX)
-/

add_to_stacks 02AX "sheaf_twist" AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules
