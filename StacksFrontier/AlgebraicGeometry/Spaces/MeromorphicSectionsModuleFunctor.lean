module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections

/-!
# Functoriality of the sheaf of meromorphic sections in its module

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The sheaf
`𝒦_F(M)` of meromorphic sections of a sheaf of `𝒪_F`-modules `M`
(`AlgebraicGeometry.Space.meromorphicSectionSheaf`, Stacks 0EN5, part (1)) is built by applying
extension of scalars along `𝒪_F ⟶ 𝒦_F` to `M`, lifting the result to the universe of the objects
of the small étale site, and sheafifying.  Each of those three steps is a *functor*, but the
construction uses only their action on objects, so the library carried no map

`𝒦_F(M) ⟶ 𝒦_F(M')`

induced by a morphism `M ⟶ M'` of modules — not even one induced by an isomorphism.  This file
supplies it, by assembling the three functors, with the module universe left **free**: the
modules are `Modules.{u, max u z}` and the sheaves live at `max (u + 1) z`.

`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionSheafModuleMap.lean` supplies the same
functoriality at the pinned module universe `Modules.{u, u}`, and carries the properties of the
induced map that its own consumers use.  The two were developed in parallel; the declarations
here are therefore in the namespace `AlgebraicGeometry.Space.FreeModuleUniverse`, and unifying
them onto one construction at the free universe is left as a separate dedup.

## Main definitions

All of them live in the namespace `AlgebraicGeometry.Space.FreeModuleUniverse`.

* `meromorphicSectionPresheafMap`: the morphism of presheaves of modules
  `M ⊗_{𝒪_F} 𝒦_F ⟶ M' ⊗_{𝒪_F} 𝒦_F` induced by `M ⟶ M'`, before sheafification.
* `meromorphicSectionSheafFunctor`: **the sheaf of meromorphic sections as a functor in the
  module**, whose value on an object is `𝒦_F(M)` on the nose.
* `mapMeromorphicSectionSheaf` is the induced morphism `𝒦_F(M) ⟶ 𝒦_F(M')`,
  `mapMeromorphicSectionSheafIso` the isomorphism induced by an isomorphism of modules, and
  `mapMeromorphicSection` the induced map on meromorphic sections themselves.

## Implementation notes

The three functors are `CategoryTheory.SheafOfModules.forget` followed by
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` of Stacks 03CU, by
`PresheafOfModules.uliftFunctor`, and by `CategoryTheory.PresheafOfModules.sheafification`.  The
middle one is the step the library lacked: `AlgebraicGeometry.Space.meromorphicSectionPresheaf`
spells the universe lift by hand, as `CategoryTheory.PresheafOfModules.ofPresheaf` of a
composition with `AddCommGrpCat.uliftFunctor`, and `PresheafOfModules.uliftObj_presheaf` is what
identifies that with the functorial spelling.

The functor is the composite on the nose, and
`AlgebraicGeometry.Space.meromorphicSectionSheafFunctor_obj` holds by definition: the
hand-assembled `AlgebraicGeometry.Space.meromorphicSectionPresheaf` and the universe-lifting
functor applied to the change of rings are the same presheaf of modules, so no comparison
isomorphism is needed anywhere and the induced morphisms have the expected types without
transport.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u z

namespace AlgebraicGeometry.Space

/-! The constructions below live in the `FreeModuleUniverse` namespace: they are the
module-universe-polymorphic form of the functoriality that
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionSheafModuleMap.lean` supplies at the
pinned module universe `Modules.{u, u}`.  The two were developed in parallel and the names
would otherwise collide. -/
namespace FreeModuleUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Extension of scalars along `𝒪_F ⟶ 𝒦_F`, as a functor into the presheaves of
`𝒦_F`-modules at the universe of the objects of the small étale site.**  This is the composite
of the three functors `AlgebraicGeometry.Space.meromorphicSectionPresheaf` applies on objects:
forgetting the sheaf condition, the change of rings of Stacks 03CU, and the universe lift. -/
noncomputable def meromorphicSectionPresheafFunctor :
    Modules.{u, max u z} B S hS F hF ⥤
      PresheafOfModules.{max (u + 1) z}
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj :=
  SheafOfModules.forget _ ⋙
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
      (toMeromorphicFunctionSheaf B S hS F hF).hom ⋙
    PresheafOfModules.uliftFunctor.{_, _, _, _, u + 1}

/-- The value of `meromorphicSectionPresheafFunctor` on `M` is
`AlgebraicGeometry.Space.meromorphicSectionPresheaf` of `M`. -/
@[simp]
theorem meromorphicSectionPresheafFunctor_obj (M : Modules.{u, max u z} B S hS F hF) :
    (meromorphicSectionPresheafFunctor.{u, z} B S hS F hF).obj M =
      meromorphicSectionPresheaf.{u, z} B S hS F hF M := rfl

/-- **Extension of scalars along `𝒪_F ⟶ 𝒦_F` is functorial in the module.**  The morphism of
presheaves of `𝒦_F`-modules `M ⊗_{𝒪_F} 𝒦_F ⟶ M' ⊗_{𝒪_F} 𝒦_F` induced by a morphism `M ⟶ M'` of
sheaves of `𝒪_F`-modules. -/
noncomputable def meromorphicSectionPresheafMap
    {M N : Modules.{u, max u z} B S hS F hF} (e : M ⟶ N) :
    meromorphicSectionPresheaf.{u, z} B S hS F hF M ⟶
      meromorphicSectionPresheaf.{u, z} B S hS F hF N :=
  (meromorphicSectionPresheafFunctor.{u, z} B S hS F hF).map e

/-- `meromorphicSectionPresheafMap` sends the identity of `M` to the identity. -/
@[simp]
theorem meromorphicSectionPresheafMap_id (M : Modules.{u, max u z} B S hS F hF) :
    meromorphicSectionPresheafMap.{u, z} B S hS F hF (𝟙 M) =
      𝟙 (meromorphicSectionPresheaf.{u, z} B S hS F hF M) :=
  (meromorphicSectionPresheafFunctor.{u, z} B S hS F hF).map_id M

/-- `meromorphicSectionPresheafMap` sends a composite to the composite of the induced maps. -/
@[simp]
theorem meromorphicSectionPresheafMap_comp {M N P : Modules.{u, max u z} B S hS F hF}
    (e : M ⟶ N) (e' : N ⟶ P) :
    meromorphicSectionPresheafMap.{u, z} B S hS F hF (e ≫ e') =
      meromorphicSectionPresheafMap.{u, z} B S hS F hF e ≫
        meromorphicSectionPresheafMap.{u, z} B S hS F hF e' :=
  (meromorphicSectionPresheafFunctor.{u, z} B S hS F hF).map_comp e e'

/-- **The sheaf of meromorphic sections of Stacks 0EN5 is a functor in the module.**  Its value
on a sheaf of `𝒪_F`-modules `M` is `𝒦_F(M)`, `AlgebraicGeometry.Space.meromorphicSectionSheaf`,
and its value on a morphism is the sheafification of
`AlgebraicGeometry.Space.FreeModuleUniverse.meromorphicSectionPresheafMap`. -/
noncomputable def meromorphicSectionSheafFunctor :
    Modules.{u, max u z} B S hS F hF ⥤
      SheafOfModules.{max (u + 1) z}
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O) :=
  let := moduleHasWeakSheafify.{u, z} B S hS F
  let := moduleWEqualsLocallyBijective.{u, z} B S hS F
  meromorphicSectionPresheafFunctor.{u, z} B S hS F hF ⋙
    PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj)

/-- The value of `meromorphicSectionSheafFunctor` on `M` is the sheaf `𝒦_F(M)` of meromorphic
sections, `AlgebraicGeometry.Space.meromorphicSectionSheaf`. -/
@[simp]
theorem meromorphicSectionSheafFunctor_obj (M : Modules.{u, max u z} B S hS F hF) :
    (meromorphicSectionSheafFunctor.{u, z} B S hS F hF).obj M =
      meromorphicSectionSheaf.{u, z} B S hS F hF M := rfl

/-- **The morphism `𝒦_F(M) ⟶ 𝒦_F(M')` of sheaves of meromorphic sections induced by a morphism
`M ⟶ M'` of sheaves of `𝒪_F`-modules.** -/
noncomputable abbrev mapMeromorphicSectionSheaf
    {M N : Modules.{u, max u z} B S hS F hF} (e : M ⟶ N) :
    meromorphicSectionSheaf.{u, z} B S hS F hF M ⟶
      meromorphicSectionSheaf.{u, z} B S hS F hF N :=
  (meromorphicSectionSheafFunctor.{u, z} B S hS F hF).map e

/-- **The isomorphism `𝒦_F(M) ≅ 𝒦_F(M')` of sheaves of meromorphic sections induced by an
isomorphism `M ≅ M'` of sheaves of `𝒪_F`-modules.**  This is the first step of the comparison
`𝒦_F(ℒ) ≅ 𝒦_F(𝒪_F) = 𝒦_F` that a generator of `ℒ` produces. -/
noncomputable abbrev mapMeromorphicSectionSheafIso
    {M N : Modules.{u, max u z} B S hS F hF} (e : M ≅ N) :
    meromorphicSectionSheaf.{u, z} B S hS F hF M ≅
      meromorphicSectionSheaf.{u, z} B S hS F hF N :=
  (meromorphicSectionSheafFunctor.{u, z} B S hS F hF).mapIso e

/-- **Transport of a meromorphic section along a morphism of modules.**  A morphism `M ⟶ M'` of
sheaves of `𝒪_F`-modules carries a meromorphic section of `M` to one of `M'`, by
`AlgebraicGeometry.Space.FreeModuleUniverse.mapMeromorphicSectionSheaf` on global sections. -/
noncomputable abbrev mapMeromorphicSection
    {M N : Modules.{u, max u z} B S hS F hF} (e : M ⟶ N)
    (s : MeromorphicSection.{u, z} B S hS F hF M) :
    MeromorphicSection.{u, z} B S hS F hF N :=
  SheafOfModules.sectionsMap (mapMeromorphicSectionSheaf.{u, z} B S hS F hF e) s

end FreeModuleUniverse

end AlgebraicGeometry.Space

end
