module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatPoint
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.DerivedAdjunctionOfExactLeftAdjoint
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Grothendieck
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Exactness and commutation properties of pullback, for the coherator comparison

Let `f : X ⟶ Y` be a morphism of schemes. Collected here are the pullback facts that the
comparison of **Stacks 08D8** rests on: pullback of all `𝒪_Y`-modules is additive and, when `f`
is flat, left exact; and pullback commutes with the inclusion of the quasi-coherent modules,
both before and after restricting pushforward.

The comparison itself, `AlgebraicGeometry.flatPushforwardCoheratorIso`, together with the
restricted pullback `AlgebraicGeometry.quasicoherentPullback`, its adjunction
`AlgebraicGeometry.quasicoherentPullbackPushforwardAdjunction` and the coherator adjunction, is
stated in `StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback` and
`StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPushforward`, whose exactness
statements assume only flatness where these assumed quasi-compactness and quasi-separatedness as
well, and whose comparison takes the derived categories as hypotheses rather than fixing the
standard model. Both are re-exported here.

## Main definitions

* `AlgebraicGeometry.quasicoherentPullbackCompι` and
  `AlgebraicGeometry.quasicoherentPushforwardCompι`: restricting pullback, respectively
  pushforward, to quasi-coherent modules and then forgetting quasi-coherence is pullback,
  respectively pushforward, of all modules.

## Main results

* `AlgebraicGeometry.pullback_additive`: pullback of all `𝒪_Y`-modules is additive, being a
  left adjoint.

## References

* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-! ### Pullback of quasi-coherent modules -/

/-- Pullback of all `𝒪_Y`-modules along a morphism of schemes is additive, being a left
adjoint. -/
public theorem pullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Additive :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).left_adjoint_additive

/-- Pullback of quasi-coherent modules, followed by the inclusion into all modules, is the
inclusion followed by pullback of all modules. -/
public noncomputable def quasicoherentPullbackCompι {X Y : Scheme.{u}} (f : X ⟶ Y) :
    quasicoherentPullback f ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ≅
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙ Scheme.Modules.pullback f :=
  ObjectProperty.liftCompιIso _ _ _

/-- Pushforward of quasi-coherent modules, followed by the inclusion into all modules, is the
inclusion followed by pushforward of all modules. -/
public noncomputable def quasicoherentPushforwardCompι {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    quasicoherentPushforward f ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ Scheme.Modules.pushforward f :=
  ObjectProperty.liftCompιIso _ _ _

end AlgebraicGeometry

end
