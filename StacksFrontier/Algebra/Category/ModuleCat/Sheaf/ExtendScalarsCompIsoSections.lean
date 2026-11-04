module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCompIso

/-! # The composition comparison for extension of scalars, against the unit of Stacks 03CZ

`Stacks.Sheaves.RingedToposModules.extendScalarsCompIso` identifies extension of scalars along a
composite `θ₁ ≫ θ₂` with the composite of the two extensions of scalars.  It is a bare
`CategoryTheory.Adjunction.leftAdjointUniq`, so nothing at all is known about it as written: every
use has to go back to the characterisation of `leftAdjointUniq`, which is that it is the unique
map compatible with the two units.

This file records that characterisation for this one comparison, in the three shapes a consumer
needs — against the unit of Stacks 03CZ as morphisms, the same read on a local section, and the
inverse read on a local section — together with the one further fact about that unit which using
them needs, its naturality on sections.  It is deliberately a separate module from any consumer:
the comparison appears in the composition law of *every* step of the chain of Stacks 03EL that
extension of scalars enters, and each of those would otherwise rediscover these lemmas.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendScalars_map_val_app_unit`: **extension of scalars
  commutes with the unit of Stacks 03CZ on a local section.** This is the naturality of that unit,
  and it is what lets a value formula be pushed through a further extension of scalars.
* `Stacks.Sheaves.RingedToposModules.unit_comp_restrictScalars_map_extendScalarsCompIso_hom_app`:
  **the comparison carries the unit of extension of scalars along the composite to the two units
  in turn.**  This is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` followed by
  `CategoryTheory.Adjunction.comp_unit_app`, and it is the only input the other two have.
* `Stacks.Sheaves.RingedToposModules.extendScalarsCompIso_hom_app_val_app_unit`: the same on a
  local section — the comparison carries the image of `x` under the unit for `θ₁ ≫ θ₂` to its
  image under the unit for `θ₁` followed by the unit for `θ₂`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsCompIso_inv_app_val_app_unit`: the inverse
  comparison, on a local section, which is the direction a composition law stated with the
  comparison on the *source* needs.

## Implementation notes

The right adjoint of the composite of the two adjunctions of Stacks 03CZ is
`restrictScalars θ₂ ⋙ restrictScalars θ₁`, and the right adjoint of the adjunction for the
composite is `restrictScalars (θ₁ ≫ θ₂)`.  The two are equal, but only up to unfolding
`SheafOfModules.restrictScalars`, which is what makes a `rw` with
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` report its target ill-typed at the
implicit transparency level.  So the generic statement is isolated as a private lemma over an
*abstract* pair of adjunctions and applied by `exact`, where the identification happens once, in
a defeq check at default transparency, rather than inside a rewrite motive.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.PresheafOfModules.ChangeOfRings

universe w v u

namespace Stacks.Sheaves.RingedToposModules

/-- Equal morphisms of sheaves of modules have equal values on a local section. -/
private lemma val_app_congr {C : Type u} [Category.{v} C] {K : GrothendieckTopology C}
    {R : Sheaf K RingCat.{w}} {M N : SheafOfModules.{w} R} {f g : M ⟶ N} (h : f = g) (V : Cᵒᵖ)
    (x : M.val.obj V) : f.val.app V x = g.val.app V x := by
  rw [h]

section Unit

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- **Extension of scalars commutes with the unit of Stacks 03CZ, on a local section.** The
extension of scalars of a morphism carries the unit image of a local section to the unit image of
its value.

This is the naturality of the unit of `extendRestrictScalarsAdjunction`, read at a section; it is
what lets a formula for a morphism on unit images be pushed through a further extension of
scalars. -/
lemma extendScalars_map_val_app_unit {M M' : SheafOfModules.{w} (commRingSheaf J A₁ h₁)}
    (g : M ⟶ M') (V : Cᵒᵖ) (z : M.val.obj V) :
    ((extendScalars J θ h₁ h₂).map g).val.app V
        (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app M).val.app V z) =
      ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app M').val.app V (g.val.app V z) :=
  val_app_congr ((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.naturality g).symm V z

end Unit

section CompIsoUnit

/-- `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` for the comparison of a left adjoint
with a composite of left adjoints, with the unit of the composite already expanded by
`CategoryTheory.Adjunction.comp_unit_app`.

Stated over abstract adjunctions so that the consumer below can apply it by `exact`: the two
spellings of the common right adjoint are then identified by a single defeq check, instead of
inside the motive of a rewrite. -/
private lemma unit_comp_map_leftAdjointUniq_comp_hom_app {𝒞 : Type u} [Category.{v} 𝒞]
    {𝒟 : Type*} [Category 𝒟] {ℰ : Type*} [Category ℰ]
    {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} {H : 𝒟 ⥤ ℰ} {I : ℰ ⥤ 𝒟} {K : 𝒞 ⥤ ℰ}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (adj : K ⊣ I ⋙ G) (X : 𝒞) :
    adj.unit.app X ≫
        (I ⋙ G).map ((Adjunction.leftAdjointUniq adj (adj₁.comp adj₂)).hom.app X) =
      adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) :=
  (Adjunction.unit_leftAdjointUniq_hom_app adj (adj₁.comp adj₂) X).trans
    (Adjunction.comp_unit_app adj₁ adj₂ X)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A₁ A₂ A₃ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
  (h₃ : Presheaf.IsSheaf J (ringPresheaf A₃))

/-- **The composition comparison for extension of scalars carries the unit of Stacks 03CZ for the
composite to the two units in turn.**

`Stacks.Sheaves.RingedToposModules.extendScalarsCompIso` is `leftAdjointUniq` between the
adjunction of Stacks 03CZ for `θ₁ ≫ θ₂` and the composite of the adjunctions for `θ₁` and for
`θ₂`, so this *is* its defining property; the right-hand side is the unit of that composite
adjunction, written out. Every other statement about the comparison is read off from here. -/
lemma unit_comp_restrictScalars_map_extendScalarsCompIso_hom_app
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃).unit.app L ≫
        (SheafOfModules.restrictScalars (commRingSheafMap J (θ₁ ≫ θ₂) h₁ h₃)).map
          ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app L) =
      (extendRestrictScalarsAdjunction J θ₁ h₁ h₂).unit.app L ≫
        (SheafOfModules.restrictScalars (commRingSheafMap J θ₁ h₁ h₂)).map
          ((extendRestrictScalarsAdjunction J θ₂ h₂ h₃).unit.app
            ((extendScalars J θ₁ h₁ h₂).obj L)) :=
  unit_comp_map_leftAdjointUniq_comp_hom_app (extendRestrictScalarsAdjunction J θ₁ h₁ h₂)
    (extendRestrictScalarsAdjunction J θ₂ h₂ h₃)
    (extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃) L

/-- **The composition comparison for extension of scalars, on a local section in the image of the
unit of Stacks 03CZ.** The unit image of `x` for the composite `θ₁ ≫ θ₂` goes to its unit image
for `θ₁` followed by its unit image for `θ₂`.

This is
`Stacks.Sheaves.RingedToposModules.unit_comp_restrictScalars_map_extendScalarsCompIso_hom_app`
read at a section; restriction of scalars does not change the underlying presheaf of modules, so
no comparison appears on either side. -/
lemma extendScalarsCompIso_hom_app_val_app_unit
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ) (x : L.val.obj V) :
    ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app L).val.app V
        (((extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃).unit.app L).val.app V x) =
      ((extendRestrictScalarsAdjunction J θ₂ h₂ h₃).unit.app
            ((extendScalars J θ₁ h₁ h₂).obj L)).val.app V
        (((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).unit.app L).val.app V x) :=
  val_app_congr (unit_comp_restrictScalars_map_extendScalarsCompIso_hom_app J θ₁ θ₂ h₁ h₂ h₃ L)
    V x

/-- **The inverse of the composition comparison for extension of scalars, on a local section in
the image of the two units of Stacks 03CZ.** It returns the unit image of `x` for the composite.

This is the direction wanted by a composition law whose statement puts the comparison on the
*source* of the morphism being compared: the two units are then what the source produces, and the
comparison has to be traversed backwards. -/
lemma extendScalarsCompIso_inv_app_val_app_unit
    (L : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ) (x : L.val.obj V) :
    ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).inv.app L).val.app V
        (((extendRestrictScalarsAdjunction J θ₂ h₂ h₃).unit.app
              ((extendScalars J θ₁ h₁ h₂).obj L)).val.app V
          (((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).unit.app L).val.app V x)) =
      ((extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃).unit.app L).val.app V x := by
  refine Eq.trans (congrArg (((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).inv.app L).val.app V)
    (extendScalarsCompIso_hom_app_val_app_unit J θ₁ θ₂ h₁ h₂ h₃ L V x).symm) ?_
  exact val_app_congr ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).app L).hom_inv_id V _

end CompIsoUnit

end Stacks.Sheaves.RingedToposModules

end
