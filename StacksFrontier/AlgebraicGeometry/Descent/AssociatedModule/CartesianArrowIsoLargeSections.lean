module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange

/-!
# The base-change comparison along isomorphic arrows, at a module universe above the rings

`Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso` says that a presheaf of
modules is cartesian over a morphism `g` of `Cᵒᵖ` exactly when it is cartesian over any arrow
isomorphic to `g` in the arrow category; it is stated with the sections of the module in the
universe of the rings. This file states it with the sections in `Type (max m r)`, where the
modules of the stacks chapters live at module universe `u + 1`; the argument is the same.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso_freeModuleUniverse`.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.PresheafOfModules

universe u v r m

section Arrow

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- A restriction map of a presheaf of modules, with its target typed as the sections of the
presheaf rather than as a module over the source ring, so that the module structure found by
instance search is the one of the target. -/
private noncomputable def largeSectionMap
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) (x : M.obj X) : M.obj X₁ :=
  M.map α x

/-- `Stacks.PresheafOfModules.largeSectionMap` is additive. -/
private theorem largeSectionMap_add
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) (x y : M.obj X) :
    largeSectionMap M α (x + y) = largeSectionMap M α x + largeSectionMap M α y :=
  map_add (M.map α).hom x y

/-- `Stacks.PresheafOfModules.largeSectionMap` is semilinear over the restriction map of rings. -/
private theorem largeSectionMap_smul
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) (t : R.obj X) (x : M.obj X) :
    largeSectionMap M α (t • x) = (R.map α).hom t • largeSectionMap M α x :=
  M.map_smul α t x

/-- `Stacks.PresheafOfModules.largeSectionMap` is compatible with composition. -/
private theorem largeSectionMap_comp
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ X₂ : Cᵒᵖ} (α : X ⟶ X₁) (β : X₁ ⟶ X₂) (x : M.obj X) :
    largeSectionMap M β (largeSectionMap M α x) = largeSectionMap M (α ≫ β) x :=
  (M.map_comp_apply α β x).symm

/-- `Stacks.PresheafOfModules.largeSectionMap` of an identity is the identity. -/
private theorem largeSectionMap_id
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X : Cᵒᵖ} (x : M.obj X) : largeSectionMap M (𝟙 X) x = x := by
  simp [largeSectionMap]

/-- `Stacks.PresheafOfModules.largeSectionMap` sends `0` to `0`. -/
private theorem largeSectionMap_zero
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) : largeSectionMap M α 0 = 0 :=
  map_zero (M.map α).hom

/-- The base-change comparison on a pure tensor, written with
`Stacks.PresheafOfModules.largeSectionMap`. -/
private theorem largeRestrictionBaseChange_tmul
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (c : R.obj Y) (x : M.obj X) :
    letI : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
    (restrictionBaseChange.{u, v, r, m} M g).hom (c ⊗ₜ x) = c • largeSectionMap M g x :=
  restrictionBaseChange_tmul M g c x

/-- The transport `R Y ⊗[R X] M X ⟶ R Y₁ ⊗[R X₁] M X₁` along a commuting square from `g : X ⟶ Y`
to `g₁ : X₁ ⟶ Y₁`: it sends `c ⊗ₜ x` to the restrictions of `c` and of `x`. -/
private theorem exists_largeTensorMap_of_arrowIso
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y X₁ Y₁ : Cᵒᵖ} (g : X ⟶ Y) (g₁ : X₁ ⟶ Y₁) (α : X ⟶ X₁) (β : Y ⟶ Y₁)
    (hsq : g ≫ β = α ≫ g₁) :
    letI : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
    letI : Module (R.obj X₁) (R.obj Y₁) := Module.compHom _ (R.map g₁).hom
    ∃ w : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →+
        TensorProduct (R.obj X₁) (R.obj Y₁) (M.obj X₁),
      ∀ (c : R.obj Y) (x : M.obj X), w (c ⊗ₜ x) = (R.map β).hom c ⊗ₜ largeSectionMap M α x := by
  let : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
  let : Module (R.obj X₁) (R.obj Y₁) := Module.compHom _ (R.map g₁).hom
  refine ⟨TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun c => AddMonoidHom.mk' (fun x => ((R.map β).hom c) ⊗ₜ[R.obj X₁] (largeSectionMap M α x))
        (fun x y => by
          change _ ⊗ₜ[R.obj X₁] (largeSectionMap M α (x + y)) = _
          rw [largeSectionMap_add, TensorProduct.tmul_add]))
      (fun c d => AddMonoidHom.ext fun x => by
        change ((R.map β).hom (c + d)) ⊗ₜ[R.obj X₁] (largeSectionMap M α x) =
          _ ⊗ₜ[R.obj X₁] _ + _ ⊗ₜ[R.obj X₁] _
        rw [map_add, TensorProduct.add_tmul]))
    (fun t c x => by
      change ((R.map β).hom ((R.map g).hom t * c)) ⊗ₜ[R.obj X₁] (largeSectionMap M α x) =
        ((R.map β).hom c) ⊗ₜ[R.obj X₁] (largeSectionMap M α (t • x))
      rw [map_mul, largeSectionMap_smul]
      have h2 : (R.map β).hom ((R.map g).hom t) = (R.map g₁).hom ((R.map α).hom t) := by
        rw [← CommRingCat.comp_apply, ← R.map_comp, hsq, R.map_comp, CommRingCat.comp_apply]
      rw [h2]
      exact (TensorProduct.smul_tmul ((R.map α).hom t) ((R.map β).hom c)
        (largeSectionMap M α x))), fun c x => rfl⟩

/-- **The base-change comparison is invariant under isomorphism of arrows.** If `g` and `g₁` are
identified by isomorphisms `α` and `β` of their sources and targets, then `M` is cartesian over
`g` exactly when it is cartesian over `g₁`. -/
theorem bijective_restrictionBaseChange_iff_of_arrowIso_freeModuleUniverse
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y X₁ Y₁ : Cᵒᵖ} (g : X ⟶ Y) (g₁ : X₁ ⟶ Y₁) (α : X ⟶ X₁) (β : Y ⟶ Y₁)
    [IsIso α] [IsIso β] (hsq : g ≫ β = α ≫ g₁) :
    Function.Bijective (restrictionBaseChange.{u, v, r, m} M g) ↔
      Function.Bijective (restrictionBaseChange.{u, v, r, m} M g₁) := by
  let : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
  let : Module (R.obj X₁) (R.obj Y₁) := Module.compHom _ (R.map g₁).hom
  have hsq' : g₁ ≫ inv β = inv α ≫ g := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  obtain ⟨w, hw⟩ := exists_largeTensorMap_of_arrowIso M g g₁ α β hsq
  obtain ⟨w', hw'⟩ := exists_largeTensorMap_of_arrowIso M g₁ g (inv α) (inv β) hsq'
  have hww' : ∀ z, w' (w z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      rw [hw, hw', ← CommRingCat.comp_apply, ← R.map_comp, IsIso.hom_inv_id, R.map_id,
        CommRingCat.id_apply, largeSectionMap_comp, IsIso.hom_inv_id, largeSectionMap_id]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  have hw'w : ∀ z, w (w' z) = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      rw [hw', hw, ← CommRingCat.comp_apply, ← R.map_comp, IsIso.inv_hom_id, R.map_id,
        CommRingCat.id_apply, largeSectionMap_comp, IsIso.inv_hom_id, largeSectionMap_id]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  have hwb : Function.Bijective w :=
    Function.bijective_iff_has_inverse.mpr ⟨w', hww', hw'w⟩
  have hcomp : ∀ z, (restrictionBaseChange M g₁).hom (w z) =
      largeSectionMap M β ((restrictionBaseChange M g).hom z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      rw [hw]
      refine (largeRestrictionBaseChange_tmul M g₁ _ _).trans ?_
      refine Eq.trans ?_
        (congrArg (largeSectionMap M β) (largeRestrictionBaseChange_tmul M g c x)).symm
      rw [largeSectionMap_smul, largeSectionMap_comp, largeSectionMap_comp, hsq]
    | add z z' hz hz' =>
      refine (congrArg _ (map_add w z z')).trans ?_
      refine (map_add (restrictionBaseChange M g₁).hom _ _).trans ?_
      refine Eq.trans ?_
        (congrArg (largeSectionMap M β) (map_add (restrictionBaseChange M g).hom z z')).symm
      rw [largeSectionMap_add, hz, hz']
      rfl
  have hβ : Function.Bijective (largeSectionMap M β) :=
    Function.bijective_iff_has_inverse.mpr ⟨largeSectionMap M (inv β),
      fun y => by rw [largeSectionMap_comp, IsIso.hom_inv_id, largeSectionMap_id],
      fun y => by rw [largeSectionMap_comp, IsIso.inv_hom_id, largeSectionMap_id]⟩
  have hfun : (largeSectionMap M β) ∘ (restrictionBaseChange M g).hom =
      (restrictionBaseChange M g₁).hom ∘ w := funext fun z => (hcomp z).symm
  change Function.Bijective (restrictionBaseChange M g).hom ↔
    Function.Bijective (restrictionBaseChange M g₁).hom
  rw [← Function.Bijective.of_comp_iff' hβ, hfun]
  exact Function.Bijective.of_comp_iff _ hwb

end Arrow

end Stacks.PresheafOfModules

end
