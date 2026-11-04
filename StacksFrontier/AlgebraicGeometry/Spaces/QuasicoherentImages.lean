module

import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite

/-!
# Images of quasi-coherent modules on an algebraic space

Let `F` be an algebraic space over a scheme `S` in a big fppf site `B`.  At the module universe
of the structure rings, the image of a morphism out of a *coherent* `𝒪_F`-module into a
quasi-coherent one is coherent on a locally Noetherian space.

## Main results

* `AlgebraicGeometry.Space.isCoherent_image`: the image of a morphism from a coherent module to
  a quasi-coherent one is coherent.

## Implementation notes

**This statement carries no hypothesis, and that is the point of the file.**  The kernel clause
it rests on is not restated here:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_quasicoherent`
(`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardExactSequence.lean`) is the
unconditional form of it.  `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian`
(`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentKernelsOnSite.lean`) proves the kernel
clause over an argument `h03DX` — Descent, Proposition 03DX(2) for the small étale site of `F`,
in the shape "an `𝒪_F`-module is quasi-coherent exactly when it is cartesian on affine charts".
At the module universe `m = u` that argument is exactly
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, which is proved
and unconditional, so the hypothesis is discharged rather than carried.

Closure under images needs no further geometry and is not reproved here:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_image_unconditional`
(`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafImageQuasicoherent.lean`) is the
unconditional statement, on the `CategoryTheory.Limits.image` spelling.  Coherence of the image
below is stated on `CategoryTheory.Abelian.image`, and the passage between the two spellings is
`CategoryTheory.Abelian.imageIsoImage`.

No `@[stacks 03M1]` attribute is carried; that tag is registered elsewhere in the tree and
placing a second copy of it here is not this file's business.

Coherence of the image is a quotient statement, not a submodule one: the ambient module `N` is
only quasi-coherent, so the submodule form of Stacks 07UD does not apply, whereas the image is
an epimorphic image of the coherent `M` and `AlgebraicGeometry.Space.isCoherent_of_epi_of_`
`isQuasicoherentOnSite` applies once the image is known to be quasi-coherent.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The image of a morphism from a coherent `𝒪_F`-module to a quasi-coherent one is
coherent.**  The image is an epimorphic image of the coherent source, and it is quasi-coherent,
so the quotient form of Stacks 07UD applies; the ambient module need only be
quasi-coherent. -/
theorem isCoherent_image
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    (hM : IsCoherent B S hS F hF M) [N.IsQuasicoherentOnSite] :
    IsCoherent B S hS F hF (Abelian.image φ) := by
  have hMq : M.IsQuasicoherentOnSite := hM.toIsQuasicoherentOnSite
  have hq : (Abelian.image φ).IsQuasicoherentOnSite :=
    ObjectProperty.prop_of_iso _ (Abelian.imageIsoImage φ).symm
      (isQuasicoherentOnSite_image_unconditional B S hS F hF φ hMq inferInstance)
  exact isCoherent_of_epi_of_isQuasicoherentOnSite B S hS F hF
    (Abelian.factorThruImage φ) hq hM

end AlgebraicGeometry.Space

end
