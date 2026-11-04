module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback

/-!
# Restriction of scalars along an isomorphism of sheaves of rings

Let `θ : O ⟶ O'` be an isomorphism of sheaves of rings on a site `(C, J)`. Restriction of scalars
along `θ` is fully faithful, and the canonical morphism
`unit O ⟶ (restrictScalars θ).obj (unit O')` of `SheafOfModules.unitToRestrictScalarsObjUnit`,
which is `θ` on sections, is an isomorphism whose inverse is `θ⁻¹` on sections.

## Main definitions

* `Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsInv`: the inverse morphism, `θ⁻¹` on
  sections.
* `Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIso`: the isomorphism
  `unit O ≅ (restrictScalars θ).obj (unit O')`.
* `Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsIso`: restriction of scalars along `θ` is
  fully faithful.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.inv_app_app` and
  `Stacks.SheafOfModules.ChangeOfRings.app_inv_app`: the two sectionwise cancellations of an
  isomorphism of sheaves of rings.
* `Stacks.SheafOfModules.ChangeOfRings.moduleSheafFunctor_map_unitToRestrictScalarsObjUnit`: the
  underlying morphism of sheaves of sets of `unit O ⟶ (restrictScalars α).obj (unit O')` is `α`
  itself, for an arbitrary morphism `α` of sheaves of rings.
* `Stacks.SheafOfModules.ChangeOfRings.isIso_unitToRestrictScalarsObjUnit`: the canonical
  morphism is an isomorphism when `θ` is.

## References

* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930), restriction of scalars
  along a surjection.
-/

@[expose] public section

open CategoryTheory

universe u v' u'

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

section General

variable [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  {O O' : Sheaf J RingCat.{u}} (α : O ⟶ O')

/-- The underlying morphism of sheaves of sets of the canonical morphism
`unit O ⟶ (restrictScalars α).obj (unit O')` is `α` itself. -/
theorem moduleSheafFunctor_map_unitToRestrictScalarsObjUnit :
    (Sheaf.moduleSheafFunctor O).map (SheafOfModules.unitToRestrictScalarsObjUnit.{u} α) =
      (sheafCompose J (CategoryTheory.forget RingCat.{u})).map α :=
  rfl

end General

section Iso

variable {O O' : Sheaf J RingCat.{u}} (θ : O ⟶ O') [IsIso θ]

/-- An isomorphism of sheaves of rings cancels its inverse on sections, in one order. -/
theorem inv_app_app (U : Cᵒᵖ) (r : O.obj.obj U) :
    ((inv θ).hom.app U).hom ((θ.hom.app U).hom r) = r :=
  ConcreteCategory.congr_hom
    (congrArg (fun m : O ⟶ O ↦ m.hom.app U) (IsIso.hom_inv_id (f := θ))) r

/-- An isomorphism of sheaves of rings cancels its inverse on sections, in the other order. -/
theorem app_inv_app (U : Cᵒᵖ) (a : O'.obj.obj U) :
    ((θ.hom.app U).hom) (((inv θ).hom.app U).hom a) = a :=
  ConcreteCategory.congr_hom
    (congrArg (fun m : O' ⟶ O' ↦ m.hom.app U) (IsIso.inv_hom_id (f := θ))) a

/-- The inverse of the canonical morphism `unit O ⟶ (restrictScalars θ).obj (unit O')` for an
isomorphism `θ` of sheaves of rings: the inverse of `θ` on sections. -/
noncomputable def unitRestrictScalarsInv :
    (SheafOfModules.restrictScalars.{u} θ).obj (SheafOfModules.unit O') ⟶
      SheafOfModules.unit O :=
  ⟨PresheafOfModules.homMk
    (((sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).map (inv θ)).hom)
    (fun U r m ↦ (map_mul ((inv θ).hom.app U).hom ((θ.hom.app U).hom r) m).trans
      (congrArg (· * _) (inv_app_app θ U r)))⟩

/-- The structure sheaf of the source, as a module over itself, is the restriction of scalars of
the structure sheaf of the target along an isomorphism `θ`, by the canonical morphism
`SheafOfModules.unitToRestrictScalarsObjUnit`, which is `θ` on sections. -/
noncomputable def unitRestrictScalarsIso :
    SheafOfModules.unit O ≅
      (SheafOfModules.restrictScalars.{u} θ).obj (SheafOfModules.unit O') where
  hom := SheafOfModules.unitToRestrictScalarsObjUnit θ
  inv := unitRestrictScalarsInv θ
  hom_inv_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun a ↦ inv_app_app θ U a))
  inv_hom_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun a ↦ app_inv_app θ U a))

/-- The isomorphism `unit O ≅ (restrictScalars θ).obj (unit O')` is the canonical morphism. -/
@[simp]
theorem unitRestrictScalarsIso_hom :
    (unitRestrictScalarsIso θ).hom = SheafOfModules.unitToRestrictScalarsObjUnit θ :=
  rfl

/-- The canonical morphism `unit O ⟶ (restrictScalars θ).obj (unit O')` is an isomorphism when
`θ` is. -/
instance isIso_unitToRestrictScalarsObjUnit :
    IsIso (SheafOfModules.unitToRestrictScalarsObjUnit.{u} θ) :=
  (unitRestrictScalarsIso θ).isIso_hom

/-- Restriction of scalars along an isomorphism of sheaves of rings is fully faithful. -/
noncomputable def fullyFaithfulOfIsIso :
    (SheafOfModules.restrictScalars.{u} θ).FullyFaithful :=
  fullyFaithfulOfIsLocallySurjective.{u} θ

end Iso

end Stacks.SheafOfModules.ChangeOfRings

end
