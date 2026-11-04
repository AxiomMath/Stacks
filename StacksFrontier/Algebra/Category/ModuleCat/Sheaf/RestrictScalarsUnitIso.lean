module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint

/-!
# Restriction of scalars of the structure sheaf along an isomorphism of sheaves of rings

Restriction of scalars along an isomorphism `e : R ≅ R'` of sheaves of rings carries the
structure sheaf `𝒪_{R'}` to `𝒪_R`; on sections the identification is the inverse of `e`.

## Main definitions

* `Stacks.Sheaves.RingedPoint.restrictScalarsUnitLinearEquiv`: the identification on sections.
* `Stacks.Sheaves.RingedPoint.restrictScalarsUnitIsoOfIso`: the isomorphism of sheaves of
  modules.

## Implementation notes

These declarations complement
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedPoint.lean` and sit in a file of their own.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.RingedPoint

universe v u w

/-- On sections, restriction of scalars of the structure sheaf along an isomorphism of sheaves
of rings is the inverse of that isomorphism. -/
noncomputable def restrictScalarsUnitLinearEquiv {T : Type u} [Category.{v} T]
    {J : GrothendieckTopology T} {R R' : Sheaf J RingCat.{w}} (e : R ≅ R') (Z : Tᵒᵖ) :
    ((SheafOfModules.restrictScalars.{w} e.hom).obj (SheafOfModules.unit R')).val.obj Z
      ≃ₗ[R.obj.obj Z] (SheafOfModules.unit R).val.obj Z where
  toFun y := ((sheafToPresheaf J RingCat.{w}).mapIso e).app Z |>.inv (show R'.obj.obj Z from y)
  invFun y := ((sheafToPresheaf J RingCat.{w}).mapIso e).app Z |>.hom y
  map_add' y z := map_add (e.inv.hom.app Z).hom (show R'.obj.obj Z from y) z
  map_smul' r y := by
    change (e.inv.hom.app Z).hom ((e.hom.hom.app Z).hom r * (show R'.obj.obj Z from y)) =
      r * (e.inv.hom.app Z).hom (show R'.obj.obj Z from y)
    rw [map_mul]
    congr 1
    exact (((sheafToPresheaf J RingCat.{w}).mapIso e).app Z).hom_inv_id_apply r
  left_inv y := (((sheafToPresheaf J RingCat.{w}).mapIso e).app Z).inv_hom_id_apply
    (show R'.obj.obj Z from y)
  right_inv y := (((sheafToPresheaf J RingCat.{w}).mapIso e).app Z).hom_inv_id_apply y

/-- Restriction of scalars along an isomorphism of sheaves of rings carries the structure sheaf
to the structure sheaf. -/
noncomputable def restrictScalarsUnitIsoOfIso {T : Type u} [Category.{v} T]
    {J : GrothendieckTopology T} {R R' : Sheaf J RingCat.{w}} (e : R ≅ R') :
    (SheafOfModules.restrictScalars.{w} e.hom).obj (SheafOfModules.unit R') ≅
      SheafOfModules.unit R :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun Z => (restrictScalarsUnitLinearEquiv e Z).toModuleIso)
      (fun Z Z' f => by
        ext y
        exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) (show R'.obj.obj Z from y)))

end Stacks.Sheaves.RingedPoint

end
