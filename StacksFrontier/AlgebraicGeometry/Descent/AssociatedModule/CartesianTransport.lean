module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange

/-!
# Transporting the base-change comparison of a presheaf of modules

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of modules over
it. For a morphism `g : X ⟶ Y` of `Cᵒᵖ` the base-change comparison
`Stacks.PresheafOfModules.restrictionBaseChange M g : R Y ⊗[R X] M X ⟶ M Y` measures whether `M`
is cartesian over `g`. This file records two ways of moving that condition around without
changing it.

* Along an isomorphism of arrows: if `g` and `g₁` are isomorphic objects of the arrow category of
  `Cᵒᵖ`, then `M` is cartesian over `g` exactly when it is cartesian over `g₁`.
* Along a change of index category with an isomorphism of rings: if `q : D ⥤ C` is a functor and
  `ψ : R' ⟶ q.op ⋙ R` an isomorphism of presheaves of rings on `D`, then the module on `D`
  obtained from `M` by restricting along `q` and then restricting scalars along `ψ` is cartesian
  over `g` exactly when `M` is cartesian over `q.op.map g`.

Both are needed whenever a module on one site is compared with its restriction to another site
whose objects are only identified with objects of the first up to a chosen isomorphism, as for
the restriction of a module on a category fibred in groupoids to the small étale site of an
object (Stacks 06W1, 06WJ).

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_iff_of_arrowIso`: invariance under
  isomorphism of arrows.
* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff`:
  invariance under restriction along a functor followed by restriction of scalars along an
  isomorphism of presheaves of rings.

## Implementation notes

The restriction maps of `M` are packaged as `Stacks.PresheafOfModules.sectionMap`, whose result
type is the sections of `M` themselves rather than a module over the source ring: instance search
then finds the module structure of the target, which is what the tensor-product manipulations
need.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.PresheafOfModules

universe u v u' v' r

section Arrow

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- A restriction map of a presheaf of modules, with its target typed as the sections of the
presheaf rather than as a module over the source ring, so that the module structure found by
instance search is the one of the target. -/
noncomputable def sectionMap (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) (x : M.obj X) : M.obj X₁ :=
  M.map α x

/-- `Stacks.PresheafOfModules.sectionMap` is additive. -/
theorem sectionMap_add (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) (x y : M.obj X) :
    sectionMap M α (x + y) = sectionMap M α x + sectionMap M α y :=
  map_add (M.map α).hom x y

/-- `Stacks.PresheafOfModules.sectionMap` is semilinear over the restriction map of rings. -/
theorem sectionMap_smul (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) (t : R.obj X) (x : M.obj X) :
    sectionMap M α (t • x) = (R.map α).hom t • sectionMap M α x :=
  M.map_smul α t x

/-- `Stacks.PresheafOfModules.sectionMap` is compatible with composition. -/
theorem sectionMap_comp (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ X₂ : Cᵒᵖ} (α : X ⟶ X₁) (β : X₁ ⟶ X₂) (x : M.obj X) :
    sectionMap M β (sectionMap M α x) = sectionMap M (α ≫ β) x :=
  (M.map_comp_apply α β x).symm

/-- `Stacks.PresheafOfModules.sectionMap` of an identity is the identity. -/
theorem sectionMap_id (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X : Cᵒᵖ} (x : M.obj X) : sectionMap M (𝟙 X) x = x := by
  simp [sectionMap]

/-- `Stacks.PresheafOfModules.sectionMap` sends `0` to `0`. -/
theorem sectionMap_zero (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X X₁ : Cᵒᵖ} (α : X ⟶ X₁) : sectionMap M α 0 = 0 :=
  map_zero (M.map α).hom

/-- The base-change comparison on a pure tensor, written with
`Stacks.PresheafOfModules.sectionMap`. -/
theorem restrictionBaseChange_tmul' (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (c : R.obj Y) (x : M.obj X) :
    letI : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
    (restrictionBaseChange.{u, v, r, r} M g).hom (c ⊗ₜ x) = c • sectionMap M g x :=
  restrictionBaseChange_tmul M g c x

/-- Two additive maps out of a tensor product agreeing on pure tensors agree everywhere. -/
private theorem tensor_addMonoidHom_apply_eq {S A B P : Type*} [CommSemiring S] [AddCommMonoid A]
    [AddCommMonoid B] [Module S A] [Module S B] [AddCommMonoid P]
    (f g : TensorProduct S A B →+ P) (h : ∀ a b, f (a ⊗ₜ b) = g (a ⊗ₜ b))
    (z : TensorProduct S A B) : f z = g z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => exact h a b
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- The transport `R Y ⊗[R X] M X ⟶ R Y₁ ⊗[R X₁] M X₁` along a commuting square from `g : X ⟶ Y`
to `g₁ : X₁ ⟶ Y₁`: it sends `c ⊗ₜ x` to the restrictions of `c` and of `x`. -/
theorem exists_tensorMap_of_arrowIso (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y X₁ Y₁ : Cᵒᵖ} (g : X ⟶ Y) (g₁ : X₁ ⟶ Y₁) (α : X ⟶ X₁) (β : Y ⟶ Y₁)
    (hsq : g ≫ β = α ≫ g₁) :
    letI : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
    letI : Module (R.obj X₁) (R.obj Y₁) := Module.compHom _ (R.map g₁).hom
    ∃ w : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →+
        TensorProduct (R.obj X₁) (R.obj Y₁) (M.obj X₁),
      ∀ (c : R.obj Y) (x : M.obj X), w (c ⊗ₜ x) = (R.map β).hom c ⊗ₜ sectionMap M α x := by
  let : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
  let : Module (R.obj X₁) (R.obj Y₁) := Module.compHom _ (R.map g₁).hom
  refine ⟨TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun c => AddMonoidHom.mk' (fun x => ((R.map β).hom c) ⊗ₜ[R.obj X₁] (sectionMap M α x))
        (fun x y => by
          show _ ⊗ₜ[R.obj X₁] (sectionMap M α (x + y)) = _
          rw [sectionMap_add, TensorProduct.tmul_add]))
      (fun c d => AddMonoidHom.ext fun x => by
        show ((R.map β).hom (c + d)) ⊗ₜ[R.obj X₁] (sectionMap M α x) =
          _ ⊗ₜ[R.obj X₁] _ + _ ⊗ₜ[R.obj X₁] _
        rw [map_add, TensorProduct.add_tmul]))
    (fun t c x => by
      show ((R.map β).hom ((R.map g).hom t * c)) ⊗ₜ[R.obj X₁] (sectionMap M α x) =
        ((R.map β).hom c) ⊗ₜ[R.obj X₁] (sectionMap M α (t • x))
      rw [map_mul, sectionMap_smul, show (R.map β).hom ((R.map g).hom t) =
          (R.map g₁).hom ((R.map α).hom t) by
        rw [← CommRingCat.comp_apply, ← R.map_comp, hsq, R.map_comp, CommRingCat.comp_apply]]
      exact (TensorProduct.smul_tmul ((R.map α).hom t) ((R.map β).hom c)
        (sectionMap M α x))), fun c x => rfl⟩

/-- **The base-change comparison is invariant under isomorphism of arrows.** If `g` and `g₁` are
identified by isomorphisms `α` and `β` of their sources and targets, then `M` is cartesian over
`g` exactly when it is cartesian over `g₁`. -/
theorem bijective_restrictionBaseChange_iff_of_arrowIso
    (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y X₁ Y₁ : Cᵒᵖ} (g : X ⟶ Y) (g₁ : X₁ ⟶ Y₁) (α : X ⟶ X₁) (β : Y ⟶ Y₁)
    [IsIso α] [IsIso β] (hsq : g ≫ β = α ≫ g₁) :
    Function.Bijective (restrictionBaseChange.{u, v, r, r} M g) ↔
      Function.Bijective (restrictionBaseChange.{u, v, r, r} M g₁) := by
  let : Module (R.obj X) (R.obj Y) := Module.compHom _ (R.map g).hom
  let : Module (R.obj X₁) (R.obj Y₁) := Module.compHom _ (R.map g₁).hom
  have hsq' : g₁ ≫ inv β = inv α ≫ g := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hsq, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  obtain ⟨w, hw⟩ := exists_tensorMap_of_arrowIso M g g₁ α β hsq
  obtain ⟨w', hw'⟩ := exists_tensorMap_of_arrowIso M g₁ g (inv α) (inv β) hsq'
  have hww' : ∀ z, w' (w z) = z := fun z => by
    refine tensor_addMonoidHom_apply_eq (w'.comp w) (AddMonoidHom.id _) (fun c x => ?_) z
    change w' (w _) = _
    rw [hw, hw', ← CommRingCat.comp_apply, ← R.map_comp, IsIso.hom_inv_id, R.map_id,
      CommRingCat.id_apply, sectionMap_comp, IsIso.hom_inv_id, sectionMap_id]
    rfl
  have hw'w : ∀ z, w (w' z) = z := fun z => by
    refine tensor_addMonoidHom_apply_eq (w.comp w') (AddMonoidHom.id _) (fun c x => ?_) z
    change w (w' _) = _
    rw [hw', hw, ← CommRingCat.comp_apply, ← R.map_comp, IsIso.inv_hom_id, R.map_id,
      CommRingCat.id_apply, sectionMap_comp, IsIso.inv_hom_id, sectionMap_id]
    rfl
  have hcomp : ∀ z, (restrictionBaseChange M g₁).hom (w z) =
      sectionMap M β ((restrictionBaseChange M g).hom z) := fun z => by
    refine tensor_addMonoidHom_apply_eq ((restrictionBaseChange M g₁).hom.toAddMonoidHom.comp w)
      ((AddMonoidHom.mk' (sectionMap M β) (sectionMap_add M β)).comp
        (restrictionBaseChange M g).hom.toAddMonoidHom) (fun c x => ?_) z
    change (restrictionBaseChange M g₁).hom (w _) =
      sectionMap M β ((restrictionBaseChange M g).hom _)
    rw [hw]
    refine (restrictionBaseChange_tmul' M g₁ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (sectionMap M β) (restrictionBaseChange_tmul' M g c x)).symm
    rw [sectionMap_smul, sectionMap_comp, sectionMap_comp, hsq]
  have hβ : Function.Bijective (sectionMap M β) :=
    Function.bijective_iff_has_inverse.mpr ⟨sectionMap M (inv β),
      fun y => by rw [sectionMap_comp, IsIso.hom_inv_id, sectionMap_id],
      fun y => by rw [sectionMap_comp, IsIso.inv_hom_id, sectionMap_id]⟩
  have hfun : (sectionMap M β) ∘ (restrictionBaseChange M g).hom =
      (restrictionBaseChange M g₁).hom ∘ w := funext fun z => (hcomp z).symm
  show Function.Bijective (restrictionBaseChange M g).hom ↔
    Function.Bijective (restrictionBaseChange M g₁).hom
  rw [← Function.Bijective.of_comp_iff' hβ, hfun]
  exact Function.Bijective.of_comp_iff _
    (Function.bijective_iff_has_inverse.mpr ⟨w', hww', hw'w⟩)

end Arrow

section Pushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **The base-change comparison after restriction along a functor and an isomorphism of rings.**
Let `q : D ⥤ C`, and let `ψ : R' ⟶ q.op ⋙ R` be an isomorphism of presheaves of rings on `D`.
The module obtained from `M` by restricting along `q` and then restricting scalars along `ψ` is
cartesian over `g` exactly when `M` is cartesian over `q.op.map g`: the sections and restriction
maps are those of `M`, and the two tensor products are identified along `ψ`. -/
theorem bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff
    (q : D ⥤ C) (R : Cᵒᵖ ⥤ CommRingCat.{r}) (R' : Dᵒᵖ ⥤ CommRingCat.{r})
    (ψ : R' ⋙ forget₂ CommRingCat RingCat ⟶ q.op ⋙ R ⋙ forget₂ CommRingCat RingCat)
    (hψ : ∀ Z, IsIso (ψ.app Z))
    (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat)) {X Y : Dᵒᵖ} (g : X ⟶ Y) :
    Function.Bijective (restrictionBaseChange.{u', v', r, r} (R := R')
      ((_root_.PresheafOfModules.restrictScalars ψ).obj
        ((_root_.PresheafOfModules.pushforward₀ q (R ⋙ forget₂ CommRingCat RingCat)).obj M))
      g) ↔
    Function.Bijective (restrictionBaseChange.{u, v, r, r} (R := R) M (q.op.map g)) := by
  have _ : IsIso (ψ.app X) := hψ X
  have _ : IsIso (ψ.app Y) := hψ Y
  set NM := (_root_.PresheafOfModules.restrictScalars ψ).obj
        ((_root_.PresheafOfModules.pushforward₀ q (R ⋙ forget₂ CommRingCat RingCat)).obj M)
  let _ : Module (R'.obj X) (R'.obj Y) := Module.compHom _ (R'.map g).hom
  let _ : Module (R.obj (q.op.obj X)) (R.obj (q.op.obj Y)) :=
    Module.compHom _ (R.map (q.op.map g)).hom
  let _ : Module (R'.obj X) (M.obj (q.op.obj X)) := Module.compHom _ (ψ.app X).hom
  let u := Stacks.RingSquare.tensorMap (P := M.obj (q.op.obj X)) (R'.map g).hom
    (R.map (q.op.map g)).hom
    (asIso (ψ.app X)).ringCatIsoToRingEquiv (asIso (ψ.app Y)).ringCatIsoToRingEquiv
    (fun t => RingHom.congr_fun (congrArg RingCat.Hom.hom (ψ.naturality g)) t)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hu : Function.Bijective u := Stacks.RingSquare.bijective_tensorMap _ _ _ _ _ _ _ _
  have hcomp : ∀ z, (restrictionBaseChange (R := R) M (q.op.map g)).hom (u z)
      = (restrictionBaseChange (R := R') NM g).hom z := fun z => by
    refine tensor_addMonoidHom_apply_eq
      ((restrictionBaseChange (R := R) M (q.op.map g)).hom.toAddMonoidHom.comp u)
      (restrictionBaseChange (R := R') NM g).hom.toAddMonoidHom (fun c x => ?_) z
    exact restrictionBaseChange_tmul M (q.op.map g) ((ψ.app Y).hom c) x
  have hfun : (⇑(restrictionBaseChange (R := R') NM g).hom)
      = (⇑(restrictionBaseChange (R := R) M (q.op.map g)).hom) ∘ (⇑u) :=
    funext fun z => (hcomp z).symm
  show Function.Bijective (⇑(restrictionBaseChange (R := R') NM g).hom) ↔ _
  rw [hfun]
  exact Function.Bijective.of_comp_iff _ hu

end Pushforward

end Stacks.PresheafOfModules

end
