module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiFullyFaithful

/-!
# `f_small^*` commutes with the identity reading of `𝓕 ↦ 𝓕^a` on the small Zariski sites

For a morphism of schemes `f : X ⟶ Y`, let `f_small : (X_Zar, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)` be the
morphism of ringed sites of Stacks 070R (2) between the small Zariski sites. The small Zariski site
of a scheme `S` is the category of opens of its underlying space with its open coverings, so
`Mod(S_Zar, 𝒪)` is `SheafOfModules.{u} S.ringCatSheaf`. In this presentation `f_small` is the
continuous functor `V ↦ f⁻¹(V)` on opens together with the structure map
`f_small^♯ = f^♯ : 𝒪_Y ⟶ f_*𝒪_X`, and pullback of sheaves of modules along it is
`AlgebraicGeometry.Scheme.Modules.pullback f`.

The functor `AlgebraicGeometry.SmallZariski.associatedModuleOfIdentity` is pullback along the
identity morphism of ringed sites `(S_Zar, 𝒪_S) ⟶ (S_Zar, 𝒪_S)`, and is isomorphic to `𝟭` by
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfIdentity`. This file constructs the
isomorphism `f_small^* ⋙ (-)^a ≅ (-)^a ⋙ f_small^*` for this functor `𝓕 ↦ 𝓕^a`, from the two
unit isomorphisms and the unitors.

## Main definitions

* `AlgebraicGeometry.SmallZariski.opensStructureSharp`: `f_small^♯`, the morphism of sheaves of
  rings underlying `f_small`.
* `AlgebraicGeometry.SmallZariski.smallPullback`: `f_small^*`, pullback of sheaves of modules
  along `f_small`.
* `AlgebraicGeometry.SmallZariski.associatedModulePullbackIso`: the natural isomorphism
  `f_small^* ⋙ (-)^a ≅ (-)^a ⋙ f_small^*`.
* `AlgebraicGeometry.SmallZariski.associatedModuleObjPullbackIso`: its component at a module.

## Main results

* `AlgebraicGeometry.SmallZariski.schemeModulesPullback_eq`: pullback of `𝒪`-modules along
  `f_small` is pullback of `𝒪_Y`-modules along the morphism of schemes `f`.
* `AlgebraicGeometry.SmallZariski.associatedModulePullbackIso_hom_app`: the component of
  `AlgebraicGeometry.SmallZariski.associatedModulePullbackIso` at a module is the composite of
  the two unit maps of `SheafOfModules.pullbackId`.

## Implementation notes

The structure sheaf of a scheme is `AlgebraicGeometry.Scheme.ringCatSheaf`, whose type
`TopCat.Sheaf` is a non-reducible `def` wrapping `CategoryTheory.Sheaf` with a `deriving
Category` instance of its own; instance search unfolds neither, so every instance the pullback
needs fails at that spelling. `AlgebraicGeometry.SmallZariski.opensStructureSheaf` and
`AlgebraicGeometry.SmallZariski.opensStructureSharp` are the same sheaf and the same morphism
ascribed to the `CategoryTheory.Sheaf (Opens.grothendieckTopology _) RingCat` spelling.

`AlgebraicGeometry.SmallZariski.pushforward_isRightAdjoint` restates, at that spelling, the
Mathlib instance for `AlgebraicGeometry.Scheme.Modules.pushforward`; the two functors are equal
by `rfl` but instance search does not unfold `AlgebraicGeometry.Scheme.Modules.pushforward`.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallZariski

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`f_small^♯`, the ring half of the morphism of ringed sites `f_small` of Stacks 070R (2)
for the small Zariski sites.**  It is `f^♯ : 𝒪_Y ⟶ f_*𝒪_X`, the morphism of sheaves of rings of
the morphism of schemes `f`, ascribed to the spelling of the small Zariski site as the site of
opens of the underlying space; the continuous functor it lies over is `V ↦ f⁻¹(V)`. -/
public abbrev opensStructureSharp :
    opensStructureSheaf Y ⟶ ((Opens.map f.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥Y) (Opens.grothendieckTopology ↥X)).obj
      (opensStructureSheaf X) :=
  f.toRingCatSheafHom

/-- Pushforward of sheaves of modules along `f_small` has a left adjoint: it is
`AlgebraicGeometry.Scheme.Modules.pushforward f`, restated at the spelling the small Zariski
sites consume. -/
public instance pushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (opensStructureSharp f)).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint

/-- **`f_small^*`**, pullback of sheaves of modules along the morphism of ringed sites
`f_small : (X_Zar, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)` of Stacks 070R (2). -/
public noncomputable abbrev smallPullback :
    SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  SheafOfModules.pullback.{u} (opensStructureSharp f)

/-- **`f_small^* = f^*`.**  Pullback of `𝒪`-modules along the morphism of ringed sites `f_small`
of the small Zariski sites is pullback of `𝒪_Y`-modules along the morphism of schemes `f`: the
small Zariski site is the site of opens, so the two are the same functor. -/
public theorem schemeModulesPullback_eq : Scheme.Modules.pullback f = smallPullback f := rfl

/-- The natural isomorphism `f_small^* ⋙ (-)^a ≅ (-)^a ⋙ f_small^*` of functors on
`𝒪_Y`-modules, where `𝓕 ↦ 𝓕^a` is `AlgebraicGeometry.SmallZariski.associatedModuleOfIdentity`
and `f_small^*` is `AlgebraicGeometry.SmallZariski.smallPullback`. -/
public noncomputable def associatedModulePullbackIso :
    smallPullback f ⋙ associatedModuleOfIdentity X ≅
      associatedModuleOfIdentity Y ⋙ smallPullback f :=
  Functor.isoWhiskerLeft (smallPullback f) (associatedModuleIsoOfIdentity X) ≪≫
    (smallPullback f).rightUnitor ≪≫ (smallPullback f).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (associatedModuleIsoOfIdentity Y).symm (smallPullback f)

/-- The component of `AlgebraicGeometry.SmallZariski.associatedModulePullbackIso` at a module `𝓕`:
an isomorphism between the module associated to `f_small^* 𝓕` and `f_small^*` of the module
associated to `𝓕`. -/
public noncomputable def associatedModuleObjPullbackIso (𝓕 : SheafOfModules.{u} Y.ringCatSheaf) :
    (associatedModuleOfIdentity X).obj ((smallPullback f).obj 𝓕) ≅
      (smallPullback f).obj ((associatedModuleOfIdentity Y).obj 𝓕) :=
  (associatedModulePullbackIso f).app 𝓕

/-- The component of `AlgebraicGeometry.SmallZariski.associatedModulePullbackIso` at a module:
the unit map of `SheafOfModules.pullbackId` on the pullback, followed by `f_small^*` applied to
its inverse. -/
public theorem associatedModulePullbackIso_hom_app
    (𝓕 : SheafOfModules.{u} Y.ringCatSheaf) :
    (associatedModulePullbackIso f).hom.app 𝓕 =
      (associatedModuleIsoOfIdentity X).hom.app ((smallPullback f).obj 𝓕) ≫
        (smallPullback f).map ((associatedModuleIsoOfIdentity Y).inv.app 𝓕) := by
  simp [associatedModulePullbackIso]

end AlgebraicGeometry.SmallZariski

end
