module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicPro
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Pushforward and the coherator on quasi-coherent modules

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. Pushforward of
`𝒪_X`-modules preserves quasi-coherence, so it restricts to a functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. In the other direction, the inclusion of quasi-coherent modules into
all modules has a right adjoint, the *coherator* `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)`.

These are the two functors between which the comparisons of the coherator sections of the
chapter take place, and both are additive.

## Main definitions

* `AlgebraicGeometry.quasicoherentPushforward`: pushforward restricted to quasi-coherent
  modules.
* `AlgebraicGeometry.coherator`: the right adjoint of the inclusion of quasi-coherent modules.

## Implementation notes

The coherator is defined as the chosen right adjoint of the inclusion, so it is only determined
up to canonical isomorphism; every statement about it is therefore phrased through the
adjunction rather than through a formula.

## References

* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Pushforward along a quasi-compact and quasi-separated morphism of schemes, restricted to
quasi-coherent modules. -/
public noncomputable def quasicoherentPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Scheme.QuasicoherentModules X ⥤ Scheme.QuasicoherentModules Y :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent (R := Y.ringCatSheaf))
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ Scheme.Modules.pushforward f)
    (fun M => have := M.2; pushforward_isQuasicoherent f M.obj)

/-- Pushforward restricted to quasi-coherent modules is additive. -/
public instance quasicoherentPushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : (quasicoherentPushforward f).Additive where
  map_add {_ _ g h} := (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.map_injective
    ((Scheme.Modules.pushforward f).map_add (f := g.hom) (g := h.hom))

/-- The coherator of a scheme: the right adjoint of the inclusion of quasi-coherent modules
into all `𝒪_X`-modules. -/
public noncomputable def coherator (X : Scheme.{u}) :
    X.Modules ⥤ Scheme.QuasicoherentModules X :=
  have := quasicoherentInclusion_isLeftAdjoint X
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.rightAdjoint

/-- The coherator is additive, being right adjoint to an additive functor. -/
public instance coherator_additive (X : Scheme.{u}) : (coherator X).Additive :=
  have := quasicoherentInclusion_isLeftAdjoint X
  (Adjunction.ofIsLeftAdjoint
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι).right_adjoint_additive

end AlgebraicGeometry

end
