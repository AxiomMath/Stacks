module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The scheme-theoretic image of a morphism of schemes

The *scheme-theoretic image* of a morphism of schemes `f : X ⟶ Y` is the smallest closed
subscheme of `Y` through which `f` factors. It is cut out by `AlgebraicGeometry.Scheme.Hom.ker`,
the largest quasi-coherent sheaf of ideals contained in the kernel of `𝒪_Y ⟶ f_* 𝒪_X`. The closed
subscheme is `AlgebraicGeometry.Scheme.Hom.image`, and `AlgebraicGeometry.Scheme.Hom.imageι` is
its closed immersion into `Y`.
-/

@[expose] public section

namespace AlgebraicGeometry

add_to_stacks 01R7 "the scheme-theoretic image as a closed subscheme of the target"
  AlgebraicGeometry.Scheme.Hom.image
add_to_stacks 01R7 "its closed immersion into the target"
  AlgebraicGeometry.Scheme.Hom.imageι

end AlgebraicGeometry

end
