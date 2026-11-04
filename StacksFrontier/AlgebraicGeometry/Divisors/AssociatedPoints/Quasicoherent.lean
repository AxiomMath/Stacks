module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# Quasi-coherence of the structure sheaf and of images

The structure sheaf of a scheme is quasi-coherent as a module over itself, and the image of a
morphism of quasi-coherent modules is quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`:
  the structure sheaf is quasi-coherent as
  a module over itself.
* `AlgebraicGeometry.isQuasicoherent_image`: the image of a morphism of quasi-coherent modules
  is quasi-coherent.

## Implementation notes

Both statements are consequences of material already in the library: the first is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`, and the second follows
from the closure of quasi-coherence under kernels and cokernels, because the categorical image
in an abelian category is the kernel of the cokernel projection.

## References

* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The image of a morphism of quasi-coherent `𝒪_X`-modules is quasi-coherent. -/
lemma isQuasicoherent_image {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (image f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage f) (inferInstanceAs (Abelian.image f).IsQuasicoherent)

end AlgebraicGeometry
