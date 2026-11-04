module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The inverse image of modules on an algebraic space is monoidal

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. The inverse image
`AlgebraicGeometry.Space.modulePullback` of Stacks 03LU carries the tensor product of Stacks 01CA
on the small étale ringed site to the tensor product: `f^*(G ⊗_{𝒪_Y} G') ≅ f^*G ⊗_{𝒪_X} f^*G'`,
naturally in `G` and `G'`.

This is Stacks 03EL, which `Stacks.SheafOfModules.pullbackTensorIso` proves for an arbitrary
morphism of ringed topoi; `modulePullback` is the inverse image of modules of that morphism for
the small étale ringed topoi of Stacks 03G8, so the only content here is matching the two
spellings of the tensor product. The tensor product sheaf that Stacks 03EL is stated for and the
monoidal product of `AlgebraicGeometry.Space.modulesMonoidalCategory` agree on objects by
`AlgebraicGeometry.Space.modulesTensorObjIso`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackTensorIso`: **Stacks 03EL on an algebraic space**, the
  monoidality of `AlgebraicGeometry.Space.modulePullback`.
* `AlgebraicGeometry.Space.modulePullbackTensorCompIso`: the same comparison for an étale
  localization of the source of a second morphism, `φ^*(F ⊗_{𝒪_X} f^*G) ≅ φ^*F ⊗ (φ ≫ f)^*G`,
  which is the shape that both sides of Bourbaki's formula are compared in.

## Implementation notes

The module universe is that of the structure rings, which is the only universe at which the
tensor product of `AlgebraicGeometry.Space.Modules` exists; see
`AlgebraicGeometry.Space.modulesMonoidalCategory`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y : AlgebraicSpaces B S hS}

/-- **Stacks 03EL for a morphism of algebraic spaces.** The inverse image of a tensor product of
`𝒪_Y`-modules along `f : X ⟶ Y` is the tensor product of the inverse images,
`f^*(G ⊗_{𝒪_Y} G') ≅ f^*G ⊗_{𝒪_X} f^*G'`.

`AlgebraicGeometry.Space.modulePullback` is the inverse image of modules of the morphism of small
étale ringed topoi of Stacks 03G8, so this is `Stacks.SheafOfModules.pullbackTensorIso` at that
morphism, with the tensor product sheaf matched with the monoidal product by
`AlgebraicGeometry.Space.modulesTensorObjIso` on each side. -/
@[stacks 03EL "for the small étale ringed topoi of a morphism of algebraic spaces"]
noncomputable def modulePullbackTensorIso (f : X ⟶ Y)
    (G G' : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS f).obj (G ⊗ G') ≅
      (modulePullback B S hS f).obj G ⊗ (modulePullback B S hS f).obj G' :=
  (modulePullback B S hS f).mapIso (modulesTensorObjIso B S hS Y.1 Y.2 G G') ≪≫
    (Stacks.SheafOfModules.pullbackTensorIso
      (smallEtaleRingedToposModulesHom B S hS f)).app (G, G') ≪≫
    (modulesTensorObjIso B S hS X.1 X.2 ((modulePullback B S hS f).obj G)
      ((modulePullback B S hS f).obj G')).symm

/-- The comparison of `φ^*(F ⊗_{𝒪_X} f^*G)` with `φ^*F ⊗_{𝒪_{X'}} (φ ≫ f)^*G`, for
`φ : X' ⟶ X` and `f : X ⟶ Y`.

It is the monoidality of the inverse image along `φ` followed, in the second factor, by the
composition comparison `φ^*f^*G ≅ (φ ≫ f)^*G` of Stacks 03LU. -/
noncomputable def modulePullbackTensorCompIso (φ : X' ⟶ X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS φ).obj (F ⊗ (modulePullback B S hS f).obj G) ≅
      (modulePullback B S hS φ).obj F ⊗ (modulePullback B S hS (φ ≫ f)).obj G :=
  modulePullbackTensorIso B S hS φ F ((modulePullback B S hS f).obj G) ≪≫
    whiskerLeftIso ((modulePullback B S hS φ).obj F)
      ((modulePullbackCompIso B S hS φ f).app G)

end AlgebraicGeometry.Space

end
