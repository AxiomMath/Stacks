module

public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.InverseImage
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback of sheaves of modules as inverse image followed by extension of scalars

For a morphism of ringed spaces `f : X ⟶ Y` the pullback functor
`f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is defined abstractly, as the left adjoint of `f_*`
(`RingedSpaceModuleAdjunction.modulePullback`, Stacks 0096).  The construction of the naive
cotangent complex, and with it Stacks 08TM and 0E1Z, is instead written over the two-step model

`Mod(𝒪_Y) ⟶ Mod(f^{-1}𝒪_Y) ⟶ Mod(𝒪_X)`,

the inverse image of sheaves of modules followed by extension of scalars along the structure
map `f^{-1}𝒪_Y ⟶ 𝒪_X`.  This file identifies the two.

## Main results

* `RingedSpaceModuleAdjunction.structureSheafHom_eq`: the morphism of sheaves of rings
  `𝒪_Y ⟶ f_*𝒪_X` that `f^*` is taken along factors as the unit `𝒪_Y ⟶ f_*f^{-1}𝒪_Y` followed
  by the direct image of the structure map `f^{-1}𝒪_Y ⟶ 𝒪_X`.  This is the adjunction identity
  `Adjunction.homEquiv_unit` for the inverse-image adjunction of sheaves of rings, since the
  structure map is by definition the adjoint transpose of `f^♯`.
* `RingedSpaceModuleAdjunction.modulePushforward_eq`: consequently `f_*` on sheaves of modules
  is restriction of scalars along `f^{-1}𝒪_Y ⟶ 𝒪_X` followed by the direct image of sheaves of
  modules along the unit, which is the right adjoint of the two-step model.
* `RingedSpaceModuleAdjunction.twoStepPullback` and
  `RingedSpaceModuleAdjunction.twoStepPullbackAdjunction`: the two-step model and its adjunction
  with `f_*`.
* `RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep`: **the identification**
  `f^* ≅ (inverse image) ⋙ (extension of scalars)`, by uniqueness of left adjoints.

## Implementation notes

The direct image of sheaves of modules `CategoryTheory.SheafOfModules.pushforward φ` for a
morphism of sheaves of rings `φ : S ⟶ F_*R` over a continuous functor `F` changes neither the
underlying sheaf nor anything else when `φ` is enlarged by a morphism of rings over the target
site: `pushforward (φ ≫ F_*ψ) = restrictScalars ψ ⋙ pushforward φ` holds by `rfl`, because both
sides pushforward the underlying sheaf and then read the scalar action through the composite.
That is what turns `structureSheafHom_eq` into `modulePushforward_eq`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096), the pullback of sheaves
  of modules along a morphism of ringed spaces.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite inverseImageRingHom opensMap)
open Stacks.SheafOfModules (inverseImageMiddleRing ringedSpaceStructureMap towerExtendScalars
  towerExtendRestrictAdjunction)

universe u

namespace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The direct image functor on sheaves of rings along the continuous functor underlying `f`. -/
noncomputable abbrev ringPushforward :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u} :=
  (AlgebraicGeometry.SheafOfModules.opensMap f.hom.base).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology (Y : TopCat)) (Opens.grothendieckTopology (X : TopCat))

/-- **The structure morphism of sheaves of rings factors through the inverse image.**  The
morphism `𝒪_Y ⟶ f_*𝒪_X` of sheaves of rings that the pullback of sheaves of modules is taken
along is the unit `𝒪_Y ⟶ f_*f^{-1}𝒪_Y` followed by the direct image of the structure map
`f^{-1}𝒪_Y ⟶ 𝒪_X`.

This is `CategoryTheory.Adjunction.homEquiv_unit` for the inverse image adjunction of sheaves of
commutative rings: the structure map `Stacks.SheafOfModules.ringedSpaceStructureMap` is by
definition the adjoint transpose of `f^♯`, so the transpose of the transpose is `f^♯` again. -/
theorem structureSheafHom_eq :
    structureSheafHom f =
      inverseImageRingHom f.hom.base Y.sheaf ≫
        (ringPushforward f).map
          (underlyingRingHomOfSite (O := inverseImageMiddleRing f) (O' := X.sheaf)
            (ringedSpaceStructureMap f)) := by
  have h0 := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv_unit
    (X := Y.sheaf) (Y := X.sheaf) (f := ringedSpaceStructureMap f)
  have h1 : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv
      Y.sheaf X.sheaf) (ringedSpaceStructureMap f) =
      (⟨f.hom.c⟩ : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf) :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      f.hom.base).homEquiv Y.sheaf X.sheaf).apply_symm_apply _
  have h := h1.symm.trans h0
  exact Eq.trans
    (congrArg (sheafCompose (Opens.grothendieckTopology (Y : TopCat))
      (forget₂ CommRingCat.{u} RingCat.{u})).map h) (Functor.map_comp _ _ _)

/-- **The direct image of sheaves of modules as restriction of scalars after a direct image.**
For a morphism of ringed spaces `f : X ⟶ Y` the functor `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` is
restriction of scalars along `f^{-1}𝒪_Y ⟶ 𝒪_X` followed by the direct image of sheaves of
modules along the unit `𝒪_Y ⟶ f_*f^{-1}𝒪_Y`.

This is `structureSheafHom_eq` read through the composition law for the direct image of sheaves
of modules, which holds by `rfl`. -/
theorem modulePushforward_eq :
    modulePushforward f =
      _root_.SheafOfModules.restrictScalars
          (underlyingRingHomOfSite (O := inverseImageMiddleRing f) (O' := X.sheaf)
            (ringedSpaceStructureMap f)) ⋙
        _root_.SheafOfModules.pushforward (inverseImageRingHom f.hom.base Y.sheaf) := by
  show _root_.SheafOfModules.pushforward (structureSheafHom f) = _
  rw [structureSheafHom_eq f]
  rfl

/-- **The two-step model of the pullback of sheaves of modules**: the inverse image of sheaves
of modules along `f`, followed by extension of scalars along the structure map
`f^{-1}𝒪_Y ⟶ 𝒪_X`.  This is the model the naive cotangent complex of Stacks 08TM is pulled back
with. -/
@[ega "0 12.1.3" "partial"]
noncomputable def twoStepPullback :=
  _root_.SheafOfModules.pullback.{u} (inverseImageRingHom f.hom.base Y.sheaf) ⋙
    towerExtendScalars.{u, u, u} (Opens.grothendieckTopology (X : TopCat))
      (inverseImageMiddleRing f) X.sheaf (ringedSpaceStructureMap f)

/-- The two-step model is left adjoint to `f_*`: it is a composite of two left adjoints, and
`modulePushforward_eq` identifies the composite of their right adjoints with `f_*`. -/
noncomputable def twoStepPullbackAdjunction : twoStepPullback f ⊣ modulePushforward f := by
  rw [modulePushforward_eq f]
  change _root_.SheafOfModules.pullback.{u} (inverseImageRingHom f.hom.base Y.sheaf) ⋙
    towerExtendScalars.{u, u, u} (Opens.grothendieckTopology (X : TopCat))
      (inverseImageMiddleRing f) X.sheaf (ringedSpaceStructureMap f) ⊣ _
  exact (_root_.SheafOfModules.pullbackPushforwardAdjunction
      (inverseImageRingHom f.hom.base Y.sheaf)).comp
    (towerExtendRestrictAdjunction.{u, u, u} (Opens.grothendieckTopology (X : TopCat))
      (inverseImageMiddleRing f) X.sheaf (ringedSpaceStructureMap f))

/-- The direct image of sheaves of modules along the inverse-image unit is additive: it changes
neither the underlying sheaf nor the addition of morphisms. -/
instance inverseImagePushforward_additive :
    (_root_.SheafOfModules.pushforward.{u}
      (inverseImageRingHom f.hom.base Y.sheaf)).Additive where
  map_add := rfl

/-- The inverse image of sheaves of modules is additive: it is a left adjoint of the additive
functor `inverseImagePushforward_additive`. -/
noncomputable instance inverseImagePullback_additive :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f.hom.base Y.sheaf)).Additive :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction
    (inverseImageRingHom f.hom.base Y.sheaf)).left_adjoint_additive

/-- The two-step model is additive: both factors are.

The general instance for a composite is *applied* rather than searched for.  The two factors
reach the preadditive structure of `Mod(f^{-1}𝒪_Y)` through two different spellings of the
inverse-image sheaf of rings — `AlgebraicGeometry.SheafOfModules.underlyingRingSheaf` for the
inverse image, `Stacks.SheafOfModules.Tensor.ringSheaf` for extension of scalars — and instance
search, which unfolds no further than `instances` transparency, does not cross them: whichever
spelling the middle category carries, the other factor's additivity is then wanted at a mixed
tuple of `Preadditive` arguments that no single instance is stated at.  Supplied as explicit
arguments the two are checked at default transparency, where the spellings agree. -/
noncomputable instance twoStepPullback_additive : (twoStepPullback f).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f.hom.base Y.sheaf))
    (inverseImagePullback_additive f) _ _ _
    (towerExtendScalars.{u, u, u} (Opens.grothendieckTopology (X : TopCat))
      (inverseImageMiddleRing f) X.sheaf (ringedSpaceStructureMap f))
    (Stacks.SheafOfModules.towerExtendScalars_additive.{u, u, u}
      (Opens.grothendieckTopology (X : TopCat)) (inverseImageMiddleRing f) X.sheaf
      (ringedSpaceStructureMap f))

/-- The two-step model preserves zero morphisms, so it may be applied termwise to complexes.
It is additive, and the general instance is again applied explicitly. -/
noncomputable instance twoStepPullback_preservesZeroMorphisms :
    (twoStepPullback f).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (twoStepPullback_additive f)

/-- **Stacks 0096, the two-step description of `f^*`.**  The pullback of sheaves of modules
along a morphism of ringed spaces is the inverse image followed by extension of scalars along
the structure map `f^{-1}𝒪_Y ⟶ 𝒪_X`.

Both functors are left adjoint to `f_*`, so they are canonically isomorphic. -/
@[ega "0 12.1.3" "partial", ega "0 4.3.1" "(G), (v)"]
noncomputable def modulePullbackIsoTwoStep : modulePullback f ≅ twoStepPullback f :=
  (modulePullbackPushforwardAdjunction f).leftAdjointUniq (twoStepPullbackAdjunction f)

end RingedSpaceModuleAdjunction

end
