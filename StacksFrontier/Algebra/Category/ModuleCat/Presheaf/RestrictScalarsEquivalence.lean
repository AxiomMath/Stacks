module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# Restriction of scalars along inverse morphisms of presheaves of rings

If `α : R ⟶ R'` and `β : R' ⟶ R` are mutually inverse morphisms of presheaves of rings, then
restriction of scalars along `α` and along `β` are mutually inverse equivalences between
presheaves of `R'`-modules and presheaves of `R`-modules. The comparisons are the identity on
underlying presheaves of abelian groups.

## Main definitions

* `PresheafOfModules.restrictScalarsCompIdIso`: a presheaf of modules is its restriction of
  scalars along a composite which is the identity.
* `PresheafOfModules.restrictScalarsEquivalence`: restriction of scalars along mutually inverse
  morphisms of presheaves of rings is an equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v v' u u'

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}

/-- The identity of underlying presheaves of abelian groups, as an isomorphism between a
presheaf of modules and its restriction of scalars along a composite which is the identity. -/
def restrictScalarsCompIdIso (α : R ⟶ R') (β : R' ⟶ R) (h : β ≫ α = 𝟙 R')
    (M : PresheafOfModules.{v} R') :
    M ≅ (restrictScalars β).obj ((restrictScalars α).obj M) :=
  isoMk (fun X => (ModuleCat.restrictScalarsId'App (RingCat.Hom.hom ((β ≫ α).app X))
      (by rw [h]; rfl) (M.obj X)).symm ≪≫
      ModuleCat.restrictScalarsComp'App (β.app X).hom (α.app X).hom _ rfl (M.obj X))
    (fun _ _ _ => rfl)

/-- Restriction of scalars along mutually inverse morphisms of presheaves of rings is an
equivalence. -/
def restrictScalarsEquivalence (α : R ⟶ R') (β : R' ⟶ R) (h₁ : α ≫ β = 𝟙 R)
    (h₂ : β ≫ α = 𝟙 R') : PresheafOfModules.{v} R' ≌ PresheafOfModules.{v} R :=
  CategoryTheory.Equivalence.mk (restrictScalars α) (restrictScalars β)
    (NatIso.ofComponents (restrictScalarsCompIdIso α β h₂) fun _ => rfl)
    (NatIso.ofComponents (fun M => (restrictScalarsCompIdIso β α h₁ M).symm) fun _ => rfl)
/-- The unit of `restrictScalarsEquivalence` is the identity on underlying presheaves of abelian
groups. -/
theorem toPresheaf_map_restrictScalarsEquivalence_unit_app (α : R ⟶ R') (β : R' ⟶ R)
    (h₁ : α ≫ β = 𝟙 R) (h₂ : β ≫ α = 𝟙 R') (M : PresheafOfModules.{v} R') :
    (toPresheaf R').map ((restrictScalarsEquivalence α β h₁ h₂).unit.app M) = 𝟙 _ :=
  NatTrans.ext (funext fun _ => rfl)

/-- The counit of `restrictScalarsEquivalence` is the identity on underlying presheaves of
abelian groups. -/
theorem toPresheaf_map_restrictScalarsEquivalence_counit_app (α : R ⟶ R') (β : R' ⟶ R)
    (h₁ : α ≫ β = 𝟙 R) (h₂ : β ≫ α = 𝟙 R') (M : PresheafOfModules.{v} R) :
    (toPresheaf R).map ((restrictScalarsEquivalence α β h₁ h₂).counit.app M) = 𝟙 _ :=
  NatTrans.ext (funext fun _ => rfl)

end PresheafOfModules
