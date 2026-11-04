module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension of scalars into a categorical pullback

A commutative square of commutative rings gives a functor from modules over its upper-left
corner to the categorical fibre product of the module categories at the other three corners.

## Main definitions

* `ModuleGlueing.extendScalarsComp`: composition of extension of scalars, for three rings in
  independent universes.
* `ModuleGlueing.extensionOfScalarsToPullback`: the functor given on a module by extension of
  scalars along the two maps out of the upper-left corner, together with the canonical
  identification after extending once more to the lower-right corner.

## Implementation notes

Mathlib models extension of scalars from `R` to `S` as `S ⊗[R] M`, reversing the displayed
order of tensor factors relative to the usual presentation. The comparison isomorphism is
assembled from the canonical isomorphisms for extension of scalars along a composite. Rings have
independent universes; module categories use a common upper universe with an independent module
universe parameter.

This content is provided locally and untagged: the tagged providers live on another branch, and
these declarations are to be collapsed onto them at merge.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleGlueing

@[expose] public section

/-- Composition of extension of scalars, allowing the three rings to live in independent
universes. This uses the same adjunction construction as `ModuleCat.extendScalarsComp`. -/
noncomputable def extendScalarsComp.{u, u₁, u₂, u₃}
    {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃}
    [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    ModuleCat.extendScalars.{u₁, u₃, max u u₂ u₃} (g.comp f) ≅
      ModuleCat.extendScalars.{u₁, u₂, max u u₂ u₃} f ⋙
        ModuleCat.extendScalars.{u₂, u₃, max u u₂ u₃} g :=
  (conjugateIsoEquiv
    ((ModuleCat.extendRestrictScalarsAdj.{max u u₂ u₃} f).comp
      (ModuleCat.extendRestrictScalarsAdj.{max u u₂ u₃} g))
    (ModuleCat.extendRestrictScalarsAdj.{max u u₂ u₃} (g.comp f))).symm
      (ModuleCat.restrictScalarsComp.{max u u₂ u₃} f g).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Under the extension-restriction adjunction for `g.comp f`, the component of
`extendScalarsComp f g` at `M` corresponds to the composite of the units of the adjunctions for
`f` and `g`, followed by the identification `restrictScalarsComp f g`. -/
lemma homEquiv_extendScalarsComp.{u, u₁, u₂, u₃}
    {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃}
    [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃) (M : ModuleCat.{max u u₂ u₃} R₁) :
    (ModuleCat.extendRestrictScalarsAdj.{max u u₂ u₃} (g.comp f)).homEquiv _ _
      ((extendScalarsComp.{u} f g).hom.app M) =
      (ModuleCat.extendRestrictScalarsAdj.{max u u₂ u₃} f).unit.app M ≫
        (ModuleCat.restrictScalars f).map
          ((ModuleCat.extendRestrictScalarsAdj.{max u u₂ u₃} g).unit.app _) ≫
        (ModuleCat.restrictScalarsComp.{max u u₂ u₃} f g).inv.app _ := by
  dsimp [extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Functor.comp_obj, Category.assoc, Category.id_comp,
    Category.comp_id, Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `extendScalarsComp f g` sends `1 ⊗ m` to `1 ⊗ (1 ⊗ m)`. -/
lemma extendScalarsComp_hom_app_one_tmul.{u, u₁, u₂, u₃}
    {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃}
    [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (M : ModuleCat.{max u u₂ u₃} R₁) (m : M) :
    (extendScalarsComp.{u} f g).hom.app M ((1 : R₃) ⊗ₜ[R₁,g.comp f] m) =
      (1 : R₃) ⊗ₜ[R₂,g] ((1 : R₂) ⊗ₜ[R₁,f] m) := by
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  erw [homEquiv_extendScalarsComp.{u} f g M]
  rfl

/-- A commutative square of commutative rings induces the
extension-of-scalars functor
`Mod B' ⟶ Mod B ×_(Mod A) Mod A'`. Its value at `L'` consists of the two scalar
extensions of `L'` and their canonical identification after extending scalars to `A`. -/
@[stacks 08KI, stacks 0D2E]
noncomputable def extensionOfScalarsToPullback.{u, uB', uB, uA', uA}
    {B' : Type uB'} {B : Type uB} {A' : Type uA'} {A : Type uA}
    [CommRing B'] [CommRing B] [CommRing A'] [CommRing A]
    (toB : B' →+* B) (toA' : B' →+* A') (BtoA : B →+* A) (A'toA : A' →+* A)
    (comm : BtoA.comp toB = A'toA.comp toA') :
    ModuleCat.{max u uB uA' uA} B' ⥤
      CategoricalPullback (ModuleCat.extendScalars.{uB, uA, max u uB uA' uA} BtoA)
        (ModuleCat.extendScalars.{uA', uA, max u uB uA' uA} A'toA) :=
  CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (ModuleCat.extendScalars.{uB, uA, max u uB uA' uA} BtoA)
    (ModuleCat.extendScalars.{uA', uA, max u uB uA' uA} A'toA)
    (ModuleCat.{max u uB uA' uA} B') |>.obj
    { fst := ModuleCat.extendScalars.{uB', uB, max u uB uA' uA} toB
      snd := ModuleCat.extendScalars.{uB', uA', max u uB uA' uA} toA'
      iso := (extendScalarsComp.{max u uB uA' uA} toB BtoA).symm ≪≫
        eqToIso (congrArg ModuleCat.extendScalars comm) ≪≫
        extendScalarsComp.{max u uB uA' uA} toA' A'toA }

end

end ModuleGlueing
