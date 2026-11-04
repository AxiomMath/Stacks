module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite

/-!
# The associated module on a slice, as a presheaf of modules over one fixed ring

Let `S` be a scheme, `F` a quasi-coherent module on `S` and `U` an object of `Over S`. Tag 03DU
equips the presheaf of pullback sections `T ↦ Γ(T, T.hom⁺ F)` with the action of the varying ring
`Γ(T, 𝒪)`, making it a `CategoryTheory.PresheafOfModules` over the structure presheaf. On the slice
at `U` every object comes with a morphism to `U`, so `Γ(U.left, 𝒪)` acts on all of its sections at
once and `Fᵃ` is a presheaf of `Γ(U.left, 𝒪)`-modules.

## Main definitions

* `Stacks.Sites.sliceAssociatedPresheafModule`: the action of `Γ(U.left, 𝒪)` on the sections of
  `Fᵃ` over an object of the slice at `U`, obtained from the action of the global functions on that
  object by restricting scalars along its structure morphism.
* `Stacks.Sites.sliceAssociatedModuleCatObj`: the sections of `Fᵃ` over an object of the slice at
  `U`, as a `Γ(U.left, 𝒪)`-module.
* `Stacks.Sites.sliceAssociatedModuleCat`: `Fᵃ` on the slice at `U`, as a presheaf of
  `Γ(U.left, 𝒪)`-modules.

## Main results

* `Stacks.Sites.sliceAssociatedPresheaf_map_smul`: the restriction maps of `Fᵃ` are
  `Γ(U.left, 𝒪)`-linear on the slice at `U`.
* `Stacks.Sites.sliceAssociatedModuleCatForget₂Iso`: the abelian presheaf underlying
  `Stacks.Sites.sliceAssociatedModuleCat` is the restriction along `CategoryTheory.Over.forget U`
  of the presheaf of Tag 03DS.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Sites

open AlgebraicGeometry

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent] (U : Over S)

/-- The action of `Γ(U.left, 𝒪)` on the sections of `Fᵃ` over an object `Z` of the slice at
`U`: the action of the global functions on the total space of `Z`, restricted along the map on
global functions induced by the structure morphism of `Z`. -/
@[instance_reducible]
public def sliceAssociatedPresheafModule (Z : (Over U)ᵒᵖ) :
    Module (Γ(U.left, ⊤) : Type u)
      ((associatedPresheaf S F (Over.forget U)).obj Z : Type u) :=
  letI : Module (Γ(Z.unop.left.left, ⊤) : Type u)
      ((associatedPresheaf S F (Over.forget U)).obj Z : Type u) :=
    inferInstanceAs (Module (Γ(Z.unop.left.left, ⊤) : Type u)
      (Γ((Scheme.Modules.pullback Z.unop.left.hom).obj F, ⊤) : Type u))
  Module.compHom _ Z.unop.hom.left.appTop.hom

/-- **The restriction maps of `Fᵃ` are `Γ(U.left, 𝒪)`-linear on the slice at `U`.** -/
public theorem sliceAssociatedPresheaf_map_smul {Z W : (Over U)ᵒᵖ} (f : Z ⟶ W)
    (r : (Γ(U.left, ⊤) : Type u))
    (m : ((associatedPresheaf S F (Over.forget U)).obj Z : Type u)) :
    letI := sliceAssociatedPresheafModule F U Z
    letI := sliceAssociatedPresheafModule F U W
    (associatedPresheaf S F (Over.forget U)).map f (r • m) =
      r • (associatedPresheaf S F (Over.forget U)).map f m := by
  have hw : f.unop.left.left ≫ Z.unop.hom.left = W.unop.hom.left :=
    congrArg CategoryTheory.Over.Hom.left (Over.w f.unop)
  have hr : f.unop.left.left.appTop (Z.unop.hom.left.appTop r) =
      W.unop.hom.left.appTop r := by
    rw [← hw, Scheme.Hom.comp_appTop]
    rfl
  exact Eq.trans (pullbackSectionsMap_smul F f.unop.left (Z.unop.hom.left.appTop r) m)
    (congrArg (fun s => s • pullbackSectionsMap F f.unop.left m) hr)

/-- The sections of `Fᵃ` over an object of the slice at `U`, as a `Γ(U.left, 𝒪)`-module. -/
public def sliceAssociatedModuleCatObj (Z : (Over U)ᵒᵖ) :
    ModuleCat.{u} (Γ(U.left, ⊤) : Type u) :=
  letI := sliceAssociatedPresheafModule F U Z
  ModuleCat.of _ ((associatedPresheaf S F (Over.forget U)).obj Z : Type u)

/-- **`Fᵃ` on the slice at `U`, as a presheaf of `Γ(U.left, 𝒪)`-modules.**  Its sections over
an object of `Over U` are the global sections of the pullback of `F` to the total space, with
the action of `Γ(U.left, 𝒪)` through the structure morphism, and its restriction maps are
those of the presheaf of Tag 03DS. -/
public def sliceAssociatedModuleCat :
    (Over U)ᵒᵖ ⥤ ModuleCat.{u} (Γ(U.left, ⊤) : Type u) where
  obj Z := sliceAssociatedModuleCatObj F U Z
  map f := ModuleCat.homMk ((associatedPresheaf S F (Over.forget U)).map f)
    fun r => AddCommGrpCat.ext fun m =>
      (sliceAssociatedPresheaf_map_smul F U f r m).symm
  map_id Z := ModuleCat.hom_ext <| LinearMap.ext fun m =>
    congrArg (fun g => (AddCommGrpCat.Hom.hom g) m)
      ((associatedPresheaf S F (Over.forget U)).map_id Z)
  map_comp f g := ModuleCat.hom_ext <| LinearMap.ext fun m =>
    congrArg (fun h => (AddCommGrpCat.Hom.hom h) m)
      ((associatedPresheaf S F (Over.forget U)).map_comp f g)

/-- **The comparison isomorphism.** Forgetting the `Γ(U.left, 𝒪)`-action on
`Stacks.Sites.sliceAssociatedModuleCat` returns the restriction along
`CategoryTheory.Over.forget U` of the presheaf of Tag 03DS. -/
public def sliceAssociatedModuleCatForget₂Iso :
    (Over.forget U).op ⋙ quasiCoherentPresheafFunctor S F ≅
      sliceAssociatedModuleCat F U ⋙
        forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{u} :=
  Iso.refl _

end Stacks.Sites

end
