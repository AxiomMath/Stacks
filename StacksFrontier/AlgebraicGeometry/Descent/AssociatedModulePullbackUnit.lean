module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback

/-!
# The unit module of a composite comparison, and of a reparametrised one

For a continuous functor of sites `F` and a comparison `φ : R ⟶ F_*R'` of sheaves of rings,
`SheafOfModules.unitToPushforwardObjUnit` reads `φ` as the morphism
`𝒪 ⟶ F_*𝒪'` of sheaves of modules: over an object of the source site it is the component of `φ`
with its ring structure forgotten.  This file records how that reading interacts with the two
ways a comparison is built out of others:

* composing two comparisons along a composite functor of sites
  (`SheafOfModules.comparisonComp`);
* transporting a comparison along a natural isomorphism of the functor of sites
  (`SheafOfModules.pushforwardCongr₂`).

Both statements are what carries an equality of *ring* comparisons — a commuting square of
morphisms of ringed sites — to the corresponding equality of the induced morphisms of *modules*
on the structure sheaves.

## Main results

* `SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp`: the unit morphism of a
  composite comparison is the unit morphism of the first factor followed by the direct image of
  the unit morphism of the second.
* `SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr₂_hom_app`: the
  comparison of the two direct images attached to a natural isomorphism of the functor of sites
  carries the unit morphism of one comparison to the unit morphism of the other.

## Implementation notes

Both proofs are `rfl` — in the second case after substituting the equation of comparisons, which
is a hypothesis of `SheafOfModules.pushforwardCongr₂` rather than an equation
between terms already in the goal.  The reason is that each of the three constructions involved
acts on the sections over an object of the site by a map which is already determined by the
component of the comparison there: `unitToPushforwardObjUnit` by the component itself,
`comparisonComp` because the direct image of a morphism of sheaves of rings along a continuous
functor is restriction of its components,
`SheafOfModules.pushforwardComp` because it is `CategoryTheory.Iso.refl`, and the
two factors of `pushforwardCongr₂` because both are induced by congruence of restriction of
scalars.  No extensionality is therefore needed, and none is used: the statements are recorded
so that consumers rewrite with them instead of relying on that defeq, which is not available at
the transparency at which `rw` and `simp` match.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace SheafOfModules

section Comp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E} {F : C ⥤ D} {G : D ⥤ E} [F.IsContinuous J K]
    [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L] {R : Sheaf J RingCat.{u}}
    {R' : Sheaf K RingCat.{u}} {R'' : Sheaf L RingCat.{u}}

/-- **The unit morphism of a composite comparison factors as the composite of the two unit
morphisms.**  For comparisons `φ : R ⟶ F_*R'` and `ψ : R' ⟶ G_*R''` of sheaves of rings along
two continuous functors of sites, the morphism `𝒪 ⟶ (F ⋙ G)_*𝒪''` of modules attached to
`SheafOfModules.comparisonComp φ ψ` is the morphism attached to `φ` followed by
the direct image along `φ` of the morphism attached to `ψ`. -/
theorem unitToPushforwardObjUnit_comparisonComp_eq_comp
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    (ψ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R'') :
    unitToPushforwardObjUnit (comparisonComp φ ψ) =
      unitToPushforwardObjUnit φ ≫ (pushforward.{u} φ).map (unitToPushforwardObjUnit ψ) :=
  rfl

end Comp

section Congr

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F G : C ⥤ D}
    {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}}
    [F.IsContinuous J K] [G.IsContinuous J K]

/-- **Reparametrising a comparison along a natural isomorphism of the functor of sites carries
unit morphism to unit morphism.**  Let `φ : R ⟶ G_*R'` be a comparison of sheaves of rings, let
`e : F ≅ G` be a natural isomorphism of the two continuous functors of sites and let `ψ` be the
comparison `φ` transported along `e`.  Then the isomorphism
`SheafOfModules.pushforwardCongr₂` of the two direct images of modules carries
the morphism `𝒪 ⟶ G_*𝒪'` attached to `φ` to the morphism `𝒪 ⟶ F_*𝒪'` attached to `ψ`. -/
theorem unitToPushforwardObjUnit_comp_pushforwardCongr₂_hom_app
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    {ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R'} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app R' = ψ) :
    unitToPushforwardObjUnit φ ≫ (pushforwardCongr₂ φ e he).hom.app (unit R') =
      unitToPushforwardObjUnit ψ := by
  subst he
  rfl

end Congr

end SheafOfModules

end
