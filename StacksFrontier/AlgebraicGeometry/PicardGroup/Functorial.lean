module

public import StacksFrontier.AlgebraicGeometry.SheafPicardGroup.Basic

/-!
# Functoriality of the Picard group

A monoidal functor between categories of sheaves of modules carries invertible sheaves to
invertible sheaves and induces a homomorphism of Picard groups. This is the abstract content
of the Picard-group half of Stacks Tag 0B8L: the pullback of an invertible module along a
morphism of ringed sites is invertible, and `f ↦ f^*` is a group homomorphism `Pic → Pic`.
Nothing here is specific to pullback — only monoidality is used — so any construction on
sheaves of modules that is monoidal induces a Picard homomorphism by `map`.

## Main definitions

* `Stacks.SheafPicardGroup.classMonoidHom`: the monoid homomorphism on isomorphism classes
  induced by a monoidal functor.
* `Stacks.SheafPicardGroup.map`: **the induced homomorphism of Picard groups.**

## Main results

* `Stacks.SheafPicardGroup.isInvertible_map_obj`: a monoidal functor carries an invertible
  sheaf of modules to an invertible sheaf of modules.
* `Stacks.SheafPicardGroup.map_classOf`: `map F` sends the class of `L` to the class of
  `F.obj L`.

## Implementation notes

Both sites carry their own topology and their own sheaf of rings; only the universe `w` of
the module data is shared, since a functor between the two categories of sheaves of modules
cannot exist otherwise.

The monoid homomorphism is Mathlib's `CategoryTheory.Skeleton.monoidHom`, and the group
homomorphism is `Units.map` of it.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

universe v₁ u₁ v₂ u₂ w

open CategoryTheory MonoidalCategory Stacks.SheafOfModules.TensorSheafification
open AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafPicardGroup

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  (𝒪₁ : C₁ᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪₁ : Presheaf.IsSheaf J₁ (structureRingPresheaf 𝒪₁))
  [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₁ AddCommGrpCat.{w}]
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  (𝒪₂ : C₂ᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪₂ : Presheaf.IsSheaf J₂ (structureRingPresheaf 𝒪₂))
  [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J₂ AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (F : _root_.SheafOfModules.{w} (structureSheaf 𝒪₁ h𝒪₁) ⥤
    _root_.SheafOfModules.{w} (structureSheaf 𝒪₂ h𝒪₂)) [F.Monoidal]

/-- **A monoidal functor induces a monoid homomorphism on isomorphism classes.** -/
noncomputable def classMonoidHom : ClassMonoid 𝒪₁ h𝒪₁ →* ClassMonoid 𝒪₂ h𝒪₂ :=
  Skeleton.monoidHom F

/-- `classMonoidHom F` sends the isomorphism class of `L` to the isomorphism class of
`F.obj L`. -/
@[simp]
theorem classMonoidHom_mk (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪₁ h𝒪₁)) :
    classMonoidHom 𝒪₁ h𝒪₁ 𝒪₂ h𝒪₂ F (mk 𝒪₁ h𝒪₁ L) = mk 𝒪₂ h𝒪₂ (F.obj L) :=
  F.mapSkeleton_obj_toSkeleton L

/-- **A monoidal functor carries an invertible sheaf of modules to an invertible sheaf of
modules.** -/
theorem isInvertible_map_obj (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪₁ h𝒪₁))
    [h : IsInvertible 𝒪₁ h𝒪₁ L] : IsInvertible 𝒪₂ h𝒪₂ (F.obj L) := by
  rw [isInvertible_iff_isUnit, ← classMonoidHom_mk 𝒪₁ h𝒪₁ 𝒪₂ h𝒪₂ F L]
  exact ((isInvertible_iff_isUnit 𝒪₁ h𝒪₁ L).mp h).map _

/-- **The homomorphism of Picard groups induced by a monoidal functor.** -/
noncomputable def map : PicardGroup 𝒪₁ h𝒪₁ →* PicardGroup 𝒪₂ h𝒪₂ :=
  Units.map (classMonoidHom 𝒪₁ h𝒪₁ 𝒪₂ h𝒪₂ F)

/-- `map F` sends the class of `L` to the class of `F.obj L`. -/
theorem map_classOf (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪₁ h𝒪₁))
    [IsInvertible 𝒪₁ h𝒪₁ L] :
    map 𝒪₁ h𝒪₁ 𝒪₂ h𝒪₂ F (classOf 𝒪₁ h𝒪₁ L) =
      @classOf _ _ _ 𝒪₂ h𝒪₂ _ _ (F.obj L) (isInvertible_map_obj 𝒪₁ h𝒪₁ 𝒪₂ h𝒪₂ F L) :=
  Units.ext <| by
    rw [map, Units.coe_map, val_classOf, classMonoidHom_mk, val_classOf]

end Stacks.SheafPicardGroup

end
