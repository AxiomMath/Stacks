module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTensorPushforwardIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Twists of a direct image along a finite morphism of algebraic spaces

Let `f : Y ⟶ X` be a finite morphism of algebraic spaces.  For an `𝒪_X`-module `𝓕` and an
`𝒪_Y`-module `𝓖` the projection formula of Stacks 0DK4 identifies `𝓕 ⊗ f_*𝓖` with
`f_*(f^*𝓕 ⊗ 𝓖)`.  Applied to the tensor powers of an invertible `𝒪_X`-module `𝓛`, it identifies
the twists of a direct image with the direct images of twists:
`f_*𝓖 ⊗ 𝓛^{⊗ n} ≅ f_*(𝓖 ⊗ (f^*𝓛)^{⊗ n})` for `n ≥ 1`.

## Main definitions

* `AlgebraicGeometry.Space.tensorModulePushforwardIsoOfIsFinite`: the projection formula
  `𝓕 ⊗ f_*𝓖 ≅ f_*(f^*𝓕 ⊗ 𝓖)` for the monoidal tensor product of `𝒪`-modules.
* `AlgebraicGeometry.Space.modulePullbackTensorPowSuccIso`: `f^*(𝓛^{⊗ n}) ≅ (f^*𝓛)^{⊗ n}`.
* `AlgebraicGeometry.Space.twistStepModulePushforwardIsoOfIsFinite`: the twists of a direct image.

## References

* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

/-- **Stacks 0DK4 for the tensor product of `𝒪`-modules.**  For a finite morphism `f : Y ⟶ X`
of algebraic spaces, an `𝒪_X`-module `𝓕` and an `𝒪_Y`-module `𝓖`, the canonical map
`𝓕 ⊗ f_*𝓖 ⟶ f_*(f^*𝓕 ⊗ 𝓖)` is an isomorphism.

This is `Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints` at the
morphism of small étale ringed topoi of `f`, fed with the geometric points of `X` and Stacks 0DK3
(`AlgebraicGeometry.Space.exists_bijective_pushforwardFiberMap_of_isFinite`), as in
`AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isFinite`; the tensor product sheaf is
matched with the monoidal product by `AlgebraicGeometry.Space.modulesTensorObjIso`, and the direct
image of the ringed topoi with `AlgebraicGeometry.Space.modulePushforward` by
`AlgebraicGeometry.Space.modulePushforwardIso`. -/
noncomputable def tensorModulePushforwardIsoOfIsFinite {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsFinite B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    F ⊗ (modulePushforward B S hS f).obj G ≅
      (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj F ⊗ G) := by
  haveI : IsIso (Stacks.SheafOfModules.pushforwardTensorMap
      (smallEtaleRingedToposModulesHom B S hS f) F G) :=
    Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints
      (smallEtaleRingedToposModulesHom B S hS f)
      (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2)
      (exists_bijective_pushforwardFiberMap_of_isFinite B S hS f hf) F G
  let P : Modules.{u, u} B S hS X.1 X.2 :=
    (Stacks.Sheaves.RingedToposModules.pushforwardModules
      (smallEtaleRingedToposModulesHom B S hS f)).obj G
  let e1 : F ⊗ (modulePushforward B S hS f).obj G ≅ F ⊗ P :=
    whiskerLeftIso F ((modulePushforwardIso B S hS f).app G).symm
  let e2 := modulesTensorObjIso B S hS X.1 X.2 F P
  let e3 := asIso (Stacks.SheafOfModules.pushforwardTensorMap
      (smallEtaleRingedToposModulesHom B S hS f) F G)
  let e5 := (modulePushforward B S hS f).mapIso
    (modulesTensorObjIso B S hS Y.1 Y.2 ((modulePullback B S hS f).obj F) G).symm
  exact e1 ≪≫ e2 ≪≫ e3 ≪≫ (modulePushforwardIso B S hS f).app _ ≪≫ e5

/-- **The inverse image of an invertible module is invertible**, in the spelling of
`AlgebraicGeometry.Space.twistStep`. -/
instance isInvertible_modulePullback_obj_structurePresheaf {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L] :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
      ((modulePullback B S hS f).obj L) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (isInvertible_modulePullback_obj B S hS f L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL))

/-- **The inverse image of a positive tensor power is the tensor power of the inverse image**,
`f^*(𝓛^{⊗ (d + 1)}) ≅ (f^*𝓛)^{⊗ (d + 1)}`, by Stacks 03EL
(`AlgebraicGeometry.Space.modulePullbackTensorIso`). -/
noncomputable def modulePullbackTensorPowSuccIso {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (L : Modules.{u, u} B S hS X.1 X.2) :
    (d : ℕ) → ((modulePullback B S hS f).obj (tensorPow B S hS L (d + 1)) ≅
      tensorPow B S hS ((modulePullback B S hS f).obj L) (d + 1))
  | 0 => Iso.refl _
  | d + 1 => modulePullbackTensorIso B S hS f (tensorPow B S hS L (d + 1)) L ≪≫
      whiskerRightIso (modulePullbackTensorPowSuccIso f L d) _

/-- **The twists of a direct image along a finite morphism are the direct images of the
twists**: `f_*𝓖 ⊗ 𝓛^{⊗ (d + 1)} ≅ f_*(𝓖 ⊗ (f^*𝓛)^{⊗ (d + 1)})` for `f` finite and `𝓛`
invertible, by the projection formula
(`AlgebraicGeometry.Space.tensorModulePushforwardIsoOfIsFinite`, Stacks 0DK4) and the
compatibility of the inverse image with tensor powers. -/
noncomputable def twistStepModulePushforwardIsoOfIsFinite {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (d : ℕ) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    twistStep B S hS X.1 X.2 L ((d + 1 : ℕ) : ℤ) ((modulePushforward B S hS f).obj G) ≅
      (modulePushforward B S hS f).obj
        (twistStep B S hS Y.1 Y.2 ((modulePullback B S hS f).obj L) ((d + 1 : ℕ) : ℤ) G) :=
  twistStepSuccIsoTensorPow X L d _ ≪≫ (β_ _ _) ≪≫
    tensorModulePushforwardIsoOfIsFinite f hf _ G ≪≫
    (modulePushforward B S hS f).mapIso ((β_ _ _) ≪≫
      whiskerLeftIso G (modulePullbackTensorPowSuccIso f L d) ≪≫
      (twistStepSuccIsoTensorPow Y ((modulePullback B S hS f).obj L) d G).symm)

end AlgebraicGeometry.Space

/-! The higher direct images along a finite morphism vanish on quasi-coherent modules
([Stacks, Tag 07UH]); the theorem is
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite_of_isQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteDirectImageVanishing.lean`. -/

add_to_stacks 07UH "vanishing of the higher direct images R^p f_* F, p > 0"
  AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isFinite_of_isQuasicoherent

end
