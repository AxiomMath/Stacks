module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction

/-!
# Cartesian presheaves of modules and change of rings

A presheaf of modules `M` over a presheaf of commutative rings `R` on a category `C` is
*cartesian* when every one of its restriction maps is a base-change isomorphism, that is when
`Stacks.PresheafOfModules.restrictionBaseChange M f` is an isomorphism for every morphism `f` of
`Cᵒᵖ`. The cartesian presheaves of modules form a full subcategory, and the change-of-rings
functor `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ`, `M ↦ O₂ ⊗_{O₁} M`, carries
cartesian presheaves to cartesian presheaves, hence restricts to a functor between these
subcategories.

## Main definitions

* `Stacks.PresheafOfModules.cartesianModules`: the cartesian presheaves of modules, as an object
  property; `(cartesianModules R).FullSubcategory` is the category they form.
* `Stacks.PresheafOfModules.ChangeOfRings.cartesianChangeOfRings`: the change-of-rings functor
  between the categories of cartesian presheaves of modules.
* `CategoryTheory.ObjectProperty.liftNatIso`: a natural isomorphism of functors landing in an
  object property, lifted to the functors into its full subcategory.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsCompIso`,
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsIdIso` and their cartesian counterparts
  `Stacks.PresheafOfModules.ChangeOfRings.cartesianChangeOfRingsCompIso`,
  `Stacks.PresheafOfModules.ChangeOfRings.cartesianChangeOfRingsIdIso`: change of rings is
  functorial up to isomorphism.

## Main results

* `Stacks.PresheafOfModules.ChangeOfRings.isScalarTower_changeOfRings_right` and
  `Stacks.PresheafOfModules.ChangeOfRings.isScalarTower_changeOfRings_left`: the two towers of
  scalars of the commuting square of a morphism of presheaves of commutative rings.
* `Stacks.PresheafOfModules.ChangeOfRings.isIso_restrictionBaseChange_changeOfRings`: change of
  rings preserves the base-change isomorphism.
* `Stacks.PresheafOfModules.ChangeOfRings.cartesianModules_changeOfRings`: change of rings
  carries cartesian presheaves of modules to cartesian presheaves of modules.

## Implementation notes

Restriction of scalars for presheaves of modules is strictly functorial, so
`changeOfRings (θ ≫ θ')` and `changeOfRings θ ⋙ changeOfRings θ'` are left adjoints of one
functor (Stacks 03CU); `changeOfRingsCompIso` and `changeOfRingsIdIso` are obtained from
`CategoryTheory.Adjunction.leftAdjointUniq` rather than computed.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C]

/-- The cartesian presheaves of modules over a presheaf of commutative rings `R`: those whose
base-change comparison `R Y ⊗[R X] M X ⟶ M Y` is an isomorphism for every morphism `f : X ⟶ Y`
of `Cᵒᵖ`. -/
abbrev cartesianModules (R : Cᵒᵖ ⥤ CommRingCat.{r}) :
    ObjectProperty (PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)) :=
  fun M => ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), IsIso (restrictionBaseChange M f)

namespace ChangeOfRings

variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- The tower of scalars `O₁ X ⟶ O₂ X ⟶ O₂ Y` of the naturality square of `θ : O₁ ⟶ O₂` at
`f : X ⟶ Y`, the composite `O₁ X ⟶ O₂ Y` being taken through `O₂ X`. -/
theorem isScalarTower_changeOfRings_right (θ : O₁ ⟶ O₂) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI := (θ.app X).hom.toAlgebra
    letI := (O₂.map f).hom.toAlgebra
    letI := ((O₂.map f).hom.comp (θ.app X).hom).toAlgebra
    IsScalarTower (O₁.obj X) (O₂.obj X) (O₂.obj Y) := by
  let := (θ.app X).hom.toAlgebra
  let := (O₂.map f).hom.toAlgebra
  let := ((O₂.map f).hom.comp (θ.app X).hom).toAlgebra
  refine ⟨fun a s t => ?_⟩
  show (O₂.map f).hom ((θ.app X).hom a * s) * t =
    ((O₂.map f).hom ((θ.app X).hom a)) * ((O₂.map f).hom s * t)
  rw [map_mul, mul_assoc]

/-- The tower of scalars `O₁ X ⟶ O₁ Y ⟶ O₂ Y` of the naturality square of `θ : O₁ ⟶ O₂` at
`f : X ⟶ Y`, the composite `O₁ X ⟶ O₂ Y` being taken through `O₂ X`. -/
theorem isScalarTower_changeOfRings_left (θ : O₁ ⟶ O₂) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI := (θ.app Y).hom.toAlgebra
    letI := (O₁.map f).hom.toAlgebra
    letI := ((O₂.map f).hom.comp (θ.app X).hom).toAlgebra
    IsScalarTower (O₁.obj X) (O₁.obj Y) (O₂.obj Y) := by
  let := (θ.app Y).hom.toAlgebra
  let := (O₁.map f).hom.toAlgebra
  let := ((O₂.map f).hom.comp (θ.app X).hom).toAlgebra
  refine ⟨fun a b t => ?_⟩
  show (θ.app Y).hom ((O₁.map f).hom a * b) * t =
    ((O₂.map f).hom ((θ.app X).hom a)) * ((θ.app Y).hom b * t)
  rw [map_mul, mul_assoc]
  refine congrArg (fun z => z * ((θ.app Y).hom b * t)) ?_
  simpa only [CommRingCat.comp_apply] using
    congrArg (fun (g : O₁.obj X ⟶ O₂.obj Y) => g.hom a) (θ.naturality f)

/-- **Change of rings preserves the base-change isomorphism.** If the restriction map of `M` along
`f` is a base-change isomorphism then so is the restriction map of `O₂ ⊗_{O₁} M`. -/
theorem isIso_restrictionBaseChange_changeOfRings (θ : O₁ ⟶ O₂)
    (M : PresheafOfModules.{max m r} (ringPresheaf O₁))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange M f)] :
    IsIso (restrictionBaseChange ((changeOfRings θ).obj M) f) := by
  let : Algebra (O₁.obj X) (O₂.obj X) := (θ.app X).hom.toAlgebra
  let : Algebra (O₁.obj Y) (O₂.obj Y) := (θ.app Y).hom.toAlgebra
  let : Algebra (O₂.obj X) (O₂.obj Y) := (O₂.map f).hom.toAlgebra
  let : Algebra (O₁.obj X) (O₁.obj Y) := (O₁.map f).hom.toAlgebra
  let : Algebra (O₁.obj X) (O₂.obj Y) := ((O₂.map f).hom.comp (θ.app X).hom).toAlgebra
  let := isScalarTower_changeOfRings_right θ f
  let := isScalarTower_changeOfRings_left θ f
  set c₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange
    (O₁.obj X) (O₂.obj X) (O₂.obj Y) (O₂.obj Y) (M.obj X)
  set c₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange
    (O₁.obj X) (O₁.obj Y) (O₂.obj Y) (O₂.obj Y) (M.obj X)
  set e : TensorProduct (O₁.obj X) (O₁.obj Y) (M.obj X) ≃ₗ[O₁.obj Y] (M.obj Y) :=
    CategoryTheory.Iso.toLinearEquiv (asIso (restrictionBaseChange M f))
  set E := c₁.trans (c₂.symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (O₂.obj Y) (O₂.obj Y)) e)) with hE
  set N := (changeOfRings θ).obj M
  have hone : ∀ w : TensorProduct (O₁.obj X) (O₂.obj X) (M.obj X),
      E ((1 : O₂.obj Y) ⊗ₜ[O₂.obj X] w) = (N.map f).hom w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact (map_zero E).trans (map_zero (N.map f).hom).symm
    | add w w' hw hw' =>
      exact ((congrArg E (tmul_add ..)).trans (map_add E ..)).trans
        ((congrArg₂ _ hw hw').trans (map_add (N.map f).hom w w').symm)
    | tmul c x =>
      have h1 : c₁ ((1 : O₂.obj Y) ⊗ₜ[O₂.obj X] (c ⊗ₜ[O₁.obj X] x))
          = (c • (1 : O₂.obj Y)) ⊗ₜ[O₁.obj X] x :=
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
          (O₁.obj X) (O₂.obj X) (O₂.obj Y) (1 : O₂.obj Y) x c
      have hc1 : (c • (1 : O₂.obj Y)) = (O₂.map f).hom c := by
        rw [Algebra.smul_def, mul_one]
        rfl
      have h2 : c₂.symm (((O₂.map f).hom c) ⊗ₜ[O₁.obj X] x)
          = ((O₂.map f).hom c) ⊗ₜ[O₁.obj Y] ((1 : O₁.obj Y) ⊗ₜ[O₁.obj X] x) := by
        refine (LinearEquiv.symm_apply_eq c₂).mpr ?_
        refine Eq.trans ?_ (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul
          (O₁.obj X) (O₁.obj Y) (O₂.obj Y) ((O₂.map f).hom c) x (1 : O₁.obj Y)).symm
        exact (congrArg (fun z => z ⊗ₜ[O₁.obj X] x)
          (one_smul (O₁.obj Y) ((O₂.map f).hom c))).symm
      have hcomp : E ((1 : O₂.obj Y) ⊗ₜ[O₂.obj X] (c ⊗ₜ[O₁.obj X] x))
          = ((O₂.map f).hom c) ⊗ₜ[O₁.obj Y] ((M.map f).hom x) := by
        rw [hE, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, hc1, h2,
          TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
        exact congrArg _ (restrictionBaseChange_one_tmul M f x)
      rw [hcomp]
      exact (cofMap_tmul θ M f c x).symm
  have key : restrictionBaseChange N f = ModuleCat.ofHom E.toLinearMap :=
    (Equiv.symm_apply_eq _).mpr (ModuleCat.hom_ext (LinearMap.ext fun w => (hone w).symm))
  rw [key]
  exact (LinearEquiv.toModuleIso E).isIso_hom

/-- **Change of rings carries cartesian presheaves of modules to cartesian presheaves of
modules.** -/
theorem cartesianModules_changeOfRings (θ : O₁ ⟶ O₂)
    (M : PresheafOfModules.{max m r} (ringPresheaf O₁)) (hM : cartesianModules O₁ M) :
    cartesianModules O₂ ((changeOfRings θ).obj M) := fun _ _ f =>
  let := hM f
  isIso_restrictionBaseChange_changeOfRings θ M f

/-- **The change-of-rings functor between the categories of cartesian presheaves of modules**,
`M ↦ O₂ ⊗_{O₁} M`. This is the functor of Stacks 039Y (4) in the generality of presheaves of
modules on an arbitrary category. -/
noncomputable def cartesianChangeOfRings (θ : O₁ ⟶ O₂) :
    (cartesianModules.{u, v, r, m} O₁).FullSubcategory ⥤
      (cartesianModules.{u, v, r, m} O₂).FullSubcategory :=
  ObjectProperty.lift _ ((cartesianModules.{u, v, r, m} O₁).ι ⋙ changeOfRings θ)
    (fun M => cartesianModules_changeOfRings θ M.obj M.property)

end ChangeOfRings

end Stacks.PresheafOfModules

namespace CategoryTheory.ObjectProperty

/-- A natural isomorphism of two functors whose values satisfy an object property lifts to a
natural isomorphism of the two induced functors into the full subcategory. -/
def liftNatIso {D : Type*} [Category D] {E : Type*} [Category E] (P : ObjectProperty D)
    {F G : E ⥤ D} (e : F ≅ G) (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) :
    P.lift F hF ≅ P.lift G hG :=
  NatIso.ofComponents (fun X => P.fullyFaithfulι.preimageIso (e.app X))
    (fun f => P.ι.map_injective (by
      simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom]
      exact e.hom.naturality f))

end CategoryTheory.ObjectProperty

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C]

namespace ChangeOfRings

variable {O₁ O₂ O₃ : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **Change of rings is functorial up to isomorphism**: `O₃ ⊗_{O₁} M` is
`O₃ ⊗_{O₂} (O₂ ⊗_{O₁} M)`. -/
noncomputable def changeOfRingsCompIso (θ : O₁ ⟶ O₂) (θ' : O₂ ⟶ O₃) :
    changeOfRings θ ⋙ changeOfRings θ' ≅ changeOfRings (θ ≫ θ') :=
  ((changeOfRingsAdjunction θ).comp (changeOfRingsAdjunction θ')).leftAdjointUniq
    (changeOfRingsAdjunction (θ ≫ θ'))

/-- **Change of rings along an identity is the identity up to isomorphism**: `O ⊗_{O} M` is `M`. -/
noncomputable def changeOfRingsIdIso (O : Cᵒᵖ ⥤ CommRingCat.{r}) :
    changeOfRings (𝟙 O) ≅ Functor.id (PMod O) :=
  (changeOfRingsAdjunction (𝟙 O)).leftAdjointUniq Adjunction.id

/-- `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsCompIso` on cartesian presheaves of
modules. -/
noncomputable def cartesianChangeOfRingsCompIso (θ : O₁ ⟶ O₂) (θ' : O₂ ⟶ O₃) :
    cartesianChangeOfRings.{u, v, r, m} θ ⋙ cartesianChangeOfRings.{u, v, r, m} θ' ≅
      cartesianChangeOfRings.{u, v, r, m} (θ ≫ θ') :=
  ObjectProperty.liftNatIso _
    (Functor.isoWhiskerLeft (cartesianModules.{u, v, r, m} O₁).ι
      (changeOfRingsCompIso.{u, v, r, max m r} θ θ')) _ _

/-- `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsIdIso` on cartesian presheaves of
modules. -/
noncomputable def cartesianChangeOfRingsIdIso (O : Cᵒᵖ ⥤ CommRingCat.{r}) :
    cartesianChangeOfRings.{u, v, r, m} (𝟙 O) ≅
      Functor.id (cartesianModules.{u, v, r, m} O).FullSubcategory :=
  ObjectProperty.liftNatIso _
    (Functor.isoWhiskerLeft (cartesianModules.{u, v, r, m} O).ι
      (changeOfRingsIdIso.{u, v, r, max m r} O)) _ _

end ChangeOfRings

end Stacks.PresheafOfModules

end
