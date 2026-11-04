module

public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.ShortComplexOfDirectImages

/-!
# The comparison of Stacks 0097 (1) for sheaves of modules is the identity

For morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` the two functors
`(g ∘ f)_*` and `g_* ∘ f_*` on sheaves of modules are *equal*, by
`Stacks.PullbackPseudofunctor.modulePushforward_comp`, and
`Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso f g` is the identity on the nose.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso_hom_app`

## Implementation notes

It holds by `rfl`: the `SheafOfModules.pushforwardCongr` factor of
`RingedSpaceModuleAdjunction.pushforwardComp` is an `eqToHom` along an equality whose two sides
are definitionally equal, hence the identity by proof irrelevance, and Mathlib's
`SheafOfModules.pushforwardComp` is `Iso.refl`.

**This belongs in a file with a small import closure.** The same `rfl` exhausts the heartbeat
budget in `whnf` when stated in a file whose closure carries the bounded below homotopy
category: adding `Mathlib.Algebra.Homology.HomotopyCategory.Plus` to the
imports of this file alone is enough to make it time out. So a consumer in the derived-category
part of the development must cite this rather than restate it.

## References

* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The comparison of [Stacks, Tag 0097] (1) is the identity**, in the `structureSheafRing`
spelling: the pushforward of a composite of morphisms of ringed spaces *is* the composite of
the pushforwards. -/
theorem pushforwardCompIso_hom_app (F : SheafOfModules.{u} (structureSheafRing X)) :
    (pushforwardCompIso f g).hom.app F = 𝟙 _ := rfl

end Stacks.Cohomology.RelativeMayerVietoris

end
