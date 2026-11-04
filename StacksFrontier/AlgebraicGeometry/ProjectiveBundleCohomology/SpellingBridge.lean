module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.PullbackWedge
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic

/-!
# The two spellings of the pullback of modules along a morphism of schemes

The pullback along a morphism of schemes `f` is written both as
`AlgebraicGeometry.Scheme.Modules.pullback f` and as the pullback
`RingedSpaceModuleAdjunction.modulePullback` along the underlying morphism of ringed spaces. The
two agree definitionally on morphisms of modules.

## Main results

* `scheme_pullback_map_eq`: The two pullback functors agree on every morphism of modules.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of a morphism, in the two spellings of the pullback functor. -/
public theorem scheme_pullback_map_eq {M N : Y.Modules} (x : M ⟶ N) :
    (Scheme.Modules.pullback f).map x = (modulePullback f.toLRSHom.toShHom).map x :=
  rfl

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
