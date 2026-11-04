module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk

/-!
# Sections over the spectrum of a stalk as a module over that stalk

Let `Y` be a scheme and `y` a point of it.  A sheaf of modules on `Spec 𝒪_{Y,y}` has its global
sections acted on by `Γ(Spec 𝒪_{Y,y}, ⊤)`, and `𝒪_{Y,y}` acts through the identification
`AlgebraicGeometry.Scheme.ΓSpecIso` of the two.

`AlgebraicGeometry.fromSpecStalkPullbackModule` records this for the modules that arise as
pullbacks along `AlgebraicGeometry.Scheme.fromSpecStalk`.  Flat base change over a local base
produces one that does not arise that way — the direct image along the second projection of
`X ×_Y Spec 𝒪_{Y,y}` — so the action is recorded here for an arbitrary module on the spectrum of
the stalk.

## Main results

* `AlgebraicGeometry.specStalkAppTopModule`: the global sections of a module on
  `Spec 𝒪_{Y,y}`, as an `𝒪_{Y,y}`-module.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The global sections of a sheaf of modules on `Spec 𝒪_{Y,y}`, as an `𝒪_{Y,y}`-module: scalars
act through the identification of `𝒪_{Y,y}` with the global functions on its spectrum.

`AlgebraicGeometry.fromSpecStalkPullbackModule` is the case of a module pulled back along
`AlgebraicGeometry.Scheme.fromSpecStalk`;  the action does not use that the module is a pullback,
and the base-change comparison over a local base needs it for a direct image. -/
@[instance_reducible]
def specStalkAppTopModule {Y : Scheme.{u}} (y : Y) (M : (Spec (Y.presheaf.stalk y)).Modules) :
    Module (Y.presheaf.stalk y) Γ(M, ⊤) :=
  Module.compHom _ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom

end AlgebraicGeometry

end
