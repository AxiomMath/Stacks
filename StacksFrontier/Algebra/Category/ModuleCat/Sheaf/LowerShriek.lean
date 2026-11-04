module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek for modules

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g : Sh(C) ⥤ Sh(D)` be
the associated morphism of topoi, let `O_D` be a sheaf of rings on `D` and let
`O_C = g^{-1} O_D`, so that `g` is a morphism of ringed topoi with `g^* = g^{-1}`. The inverse
image `g^* : Mod(O_D) ⥤ Mod(O_C)` then has a left adjoint `g_! : Mod(O_C) ⥤ Mod(O_D)`, obtained
by sheafifying the lower shriek of the underlying presheaves of modules.

## Main definitions

* `Stacks.SheafOfModules.inverseImageRing`: `O_C = g^{-1} O_D`.
* `Stacks.SheafOfModules.inverseImage`: `g^* = g^{-1} : Mod(O_D) ⥤ Mod(O_C)`.
* `Stacks.SheafOfModules.lowerShriek`: `g_! : Mod(O_C) ⥤ Mod(O_D)`.
* `Stacks.SheafOfModules.lowerShriekAdjunction`: `g_! ⊣ g^*`.
* `Stacks.SheafOfModules.lowerShriekIsoPullback`: `g_!` is the abstract left adjoint
  `SheafOfModules.pullback` of the inverse image.

## Implementation notes

Cocontinuity of `u` is what makes restriction along `u` the inverse image of the morphism of
topoi `g`, rather than merely the direct image of a morphism of sites the other way: restriction
is left adjoint to `{}_s u = g_*` by `CategoryTheory.Functor.sheafAdjunctionCocontinuous`, and
by Stacks 00XR (1),
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous`, it agrees with
`G ↦ (u^p G)^#`. So `inverseImageRing` is `g^{-1} O_D` and `inverseImage` is `g^* = g^{-1}` on
modules. Cocontinuity is carried as a hypothesis for that reason and is not used in the
construction: the adjunction needs only continuity of `u`, and for an arbitrary structure
morphism of sheaves of rings in place of the identity of `O_C` it is Stacks 03D7,
`SheafOfModules.pullbackPushforwardAdjunctionUnivLE`.

`O_C` and `g^*` are the sheaf of rings and the functor that
`Stacks.Cohomology.DerivedLowerShriek.inverseImageRing` and
`Stacks.Cohomology.DerivedLowerShriek.restrictionModules` name in the derived setting of Stacks
07AC, which carries the adjointness constructed here as a hypothesis.

The universes of the two sites, of their morphisms, of the sheaf of rings and of the module
sections are mutually independent, related only by `UnivLE` into the universe of the sections;
this is `SheafOfModules.pushforward_isRightAdjoint_of_univLE`.

## References

* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] (O : Sheaf K RingCat.{r})

/-- `O_C = g^{-1} O_D`, the restriction along `u` of a sheaf of rings on the target site. -/
abbrev inverseImageRing : Sheaf J RingCat.{r} :=
  (u.sheafPushforwardContinuous RingCat.{r} J K).obj O

/-- The identity of `O_C = g^{-1} O_D`, the structure morphism of sheaves of rings making the
morphism of topoi `g` a morphism of ringed topoi with `g^* = g^{-1}`. -/
abbrev structureMap : inverseImageRing J K u O ⟶ inverseImageRing J K u O := 𝟙 _

/-- `g^* = g^{-1} : Mod(O_D) ⥤ Mod(O_C)`, the inverse image of sheaves of modules along a
continuous and cocontinuous functor of sites: a sheaf of `O_D`-modules is restricted along `u`
and read as a sheaf of modules over `O_C = g^{-1} O_D`. -/
def inverseImage [u.IsCocontinuous J K] :
    _root_.SheafOfModules.{v} O ⥤ _root_.SheafOfModules.{v} (inverseImageRing J K u O) :=
  _root_.SheafOfModules.pushforward.{v} (structureMap J K u O)

variable [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{v₂, v}] [UnivLE.{u₁, v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Stacks 0797.** Lower shriek `g_! : Mod(O_C) ⥤ Mod(O_D)` for the morphism of topoi
associated with a continuous and cocontinuous functor of sites, where `O_C = g^{-1} O_D`: a
sheaf of `O_C`-modules is pushed forward as a presheaf of modules and the result is sheafified. -/
@[stacks 0797, sga "4 IV 14.2" "j_!"]
def lowerShriek [u.IsCocontinuous J K] :
    _root_.SheafOfModules.{v} (inverseImageRing J K u O) ⥤ _root_.SheafOfModules.{v} O :=
  _root_.SheafOfModules.forget _ ⋙
    PresheafOfModules.pullback.{v} (structureMap J K u O).hom ⋙
    PresheafOfModules.sheafification (R₀ := O.obj) (𝟙 O.obj)

/-- **Stacks 0797.** Lower shriek is left adjoint to the inverse image `g^* = g^{-1}` of sheaves
of modules, for the morphism of topoi associated with a continuous and cocontinuous functor of
sites. -/
@[stacks 0797, sga "4 IV 14.2" "j_! ⊣ j^*"]
def lowerShriekAdjunction [u.IsCocontinuous J K] :
    lowerShriek.{v} J K u O ⊣ inverseImage.{v} J K u O :=
  _root_.SheafOfModules.PullbackConstruction.adjunction.{v} (structureMap J K u O)

/-- The inverse image of sheaves of modules along a continuous and cocontinuous functor of sites
is a right adjoint, lower shriek being its left adjoint. -/
instance isRightAdjoint_inverseImage [u.IsCocontinuous J K] :
    (inverseImage.{v} J K u O).IsRightAdjoint :=
  (lowerShriekAdjunction.{v} J K u O).isRightAdjoint

/-- Lower shriek is the abstract left adjoint `SheafOfModules.pullback` of the inverse image:
two left adjoints of one functor are canonically isomorphic. -/
def lowerShriekIsoPullback [u.IsCocontinuous J K] :
    lowerShriek.{v} J K u O ≅ _root_.SheafOfModules.pullback.{v} (structureMap J K u O) :=
  Adjunction.leftAdjointUniq (lowerShriekAdjunction.{v} J K u O)
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} (structureMap J K u O))

end Stacks.SheafOfModules

end
