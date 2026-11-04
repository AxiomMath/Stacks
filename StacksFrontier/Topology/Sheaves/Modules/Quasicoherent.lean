module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback

public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of quasi-coherent sheaves of modules

The pullback of a quasi-coherent sheaf of modules along a morphism of ringed spaces is
quasi-coherent. Quasi-coherence of an `𝒪_Y`-module `G` is witnessed by a cover of `Y` by
opens `V i` together with a presentation of `G|_{V i}` by free modules; pulling back along
`f : X ⟶ Y` produces the cover of `X` by the opens `f⁻¹ (V i)`, and the local presentations
survive because pullback is a left adjoint and therefore preserves the colimits a
presentation is built from.

## Main results

* `AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent`: pullback along a morphism
  of ringed spaces preserves quasi-coherence.

## Implementation notes

The pullback is the canonical left adjoint `RingedSpaceModuleAdjunction.modulePullback` to
pushforward, and quasi-coherence is Mathlib's `SheafOfModules.IsQuasicoherent`.

Transporting a local presentation is the only real work, and it is done once, for Stacks 01BQ,
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationPullback.lean`: restricting
to `V : Opens Y` replaces the site `Opens Y` by its localization
`(Opens.grothendieckTopology Y).over V`, and the inverse-image functor on opens induces
`Over.post` between the two localizations. That functor is continuous and final, so the pullback
it induces on sheaves of modules carries presentations to presentations, which is
`Stacks.SheafOfModules.pullbackOverPresentation`. All that is left here is to assemble the
transported presentations into quasi-coherent data for `f^* G`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.SheafOfModules

open Stacks.SheafOfModules

/-- **Stacks 01BG.** The pullback of a quasi-coherent sheaf of modules along a
morphism of ringed spaces is quasi-coherent. -/
@[stacks 01BG]
lemma modulePullback_isQuasicoherent {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y)) [G.IsQuasicoherent] :
    ((modulePullback f).obj G).IsQuasicoherent := by
  let q : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u} G :=
    (_root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := G)).some
  let q' : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u}
      ((modulePullback f).obj G) := {
    I := q.I
    X := fun i ↦ (Opens.map f.hom.base).obj (q.X i)
    coversTop := preimage_opens_cover f q.X q.coversTop
    presentation := fun i ↦ pullbackOverPresentation f G (q.X i) (q.presentation i)
  }
  exact q'.isQuasicoherent

end AlgebraicGeometry.SheafOfModules
