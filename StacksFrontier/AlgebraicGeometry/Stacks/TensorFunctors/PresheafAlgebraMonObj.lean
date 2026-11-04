module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# A presheaf of algebras is a commutative monoid in presheaves of modules

Let `α : R ⟶ A` be a morphism of presheaves of commutative rings on a category `C`.  Then `A`,
read as a presheaf of `R`-modules by restriction of scalars along `α`, is a commutative monoid
object of the symmetric monoidal category of presheaves of `R`-modules (whose tensor product is
objectwise): the multiplication is the objectwise multiplication of `A` and the unit is `α`.

## Main definitions

* `PresheafOfModules.algebraPresheaf`: `A` read as a presheaf of `R`-modules.
* `PresheafOfModules.monObjAlgebraPresheaf`, `PresheafOfModules.isCommMonObjAlgebraPresheaf`:
  its commutative monoid structure.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace PresheafOfModules

variable {C : Type*} [Category* C] {R A : Cᵒᵖ ⥤ CommRingCat.{u}} (α : R ⟶ A)

/-- The presheaf of commutative rings `A`, read as a presheaf of modules over `R` along
`α : R ⟶ A`. -/
noncomputable def algebraPresheaf : PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat) :=
  (restrictScalars (Functor.whiskerRight α (forget₂ _ RingCat))).obj (unit (A ⋙ forget₂ _ RingCat))

/-- A section of `algebraPresheaf α`, read as an element of the ring `A(X)`. -/
abbrev toRingElem {X : Cᵒᵖ} (a : (algebraPresheaf α).obj X) : A.obj X := a

/-- An element of the ring `A(X)`, read as a section of `algebraPresheaf α`. -/
abbrev ofRingElem {X : Cᵒᵖ} (a : A.obj X) : (algebraPresheaf α).obj X := a

/-- The action of `r ∈ R(X)` on a section of `algebraPresheaf α` is multiplication by
`α r` in `A(X)`. -/
lemma algebraPresheaf_smul (X : Cᵒᵖ) (r : (R ⋙ forget₂ _ RingCat).obj X)
    (a : (algebraPresheaf α).obj X) :
    toRingElem α (r • a) = (α.app X).hom r * toRingElem α a := rfl

/-- The multiplication of `A` on sections over one object, as a map out of the tensor product of
modules over `R`. -/
noncomputable def algebraPresheafMulApp (X : Cᵒᵖ) :
    ((algebraPresheaf α ⊗ algebraPresheaf α).obj X) ⟶ (algebraPresheaf α).obj X :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (a b : (algebraPresheaf α).obj X) => ofRingElem α (toRingElem α a * toRingElem α b))
    (fun a a' b => add_mul (toRingElem α a) (toRingElem α a') (toRingElem α b))
    (fun r a b => mul_assoc ((α.app X).hom r) (toRingElem α a) (toRingElem α b))
    (fun a b b' => mul_add (toRingElem α a) (toRingElem α b) (toRingElem α b'))
    (fun r a b => mul_left_comm (toRingElem α a) ((α.app X).hom r) (toRingElem α b))

/-- `algebraPresheafMulApp α X` sends `a ⊗ₜ b` to the product `a * b` in `A(X)`. -/
lemma algebraPresheafMulApp_tmul (X : Cᵒᵖ) (a b : (algebraPresheaf α).obj X) :
    toRingElem α ((algebraPresheafMulApp α X).hom (a ⊗ₜ b)) = toRingElem α a * toRingElem α b :=
  rfl

/-- The multiplication of `A`, a morphism of presheaves of `R`-modules. -/
noncomputable def algebraPresheafMul :
    algebraPresheaf α ⊗ algebraPresheaf α ⟶ algebraPresheaf α where
  app X := algebraPresheafMulApp α X
  naturality f := ModuleCat.MonoidalCategory.tensor_ext (fun a b =>
    (map_mul (A.map f).hom (toRingElem α a) (toRingElem α b)).symm)

/-- The global section `1` of `A`. -/
noncomputable def algebraPresheafOneSection : (algebraPresheaf α).sections :=
  sectionsMk (fun X => ofRingElem α (1 : A.obj X))
    (fun _ _ f => map_one (A.map f).hom)

/-- The unit of `A`, a morphism of presheaves of `R`-modules out of the tensor unit. -/
noncomputable def algebraPresheafOne : 𝟙_ (PresheafOfModules.{u} (R ⋙ forget₂ _ RingCat)) ⟶
    algebraPresheaf α :=
  (unitHomEquiv _).symm (algebraPresheafOneSection α)

/-- The unit `algebraPresheafOne α` sends `r ∈ R(X)` to `α r ∈ A(X)`. -/
lemma algebraPresheafOne_app (X : Cᵒᵖ) (r : (R ⋙ forget₂ _ RingCat).obj X) :
    toRingElem α (((algebraPresheafOne α).app X).hom r) = (α.app X).hom r :=
  mul_one ((α.app X).hom r)

/-- The monoid object structure on `algebraPresheaf α`, with multiplication `algebraPresheafMul α`
and unit `algebraPresheafOne α`. -/
noncomputable instance monObjAlgebraPresheaf : MonObj (algebraPresheaf α) where
  one := algebraPresheafOne α
  mul := algebraPresheafMul α
  one_mul := by
    ext1 X
    refine ModuleCat.MonoidalCategory.tensor_ext (fun r a => ?_)
    exact congrArg (fun z => z * toRingElem α a) (algebraPresheafOne_app α X r)
  mul_one := by
    ext1 X
    refine ModuleCat.MonoidalCategory.tensor_ext (fun a r => ?_)
    exact (congrArg (fun z => toRingElem α a * z) (algebraPresheafOne_app α X r)).trans
      (mul_comm _ _)
  mul_assoc := by
    ext1 X
    refine ModuleCat.MonoidalCategory.tensor_ext₃' (fun a b c => ?_)
    exact mul_assoc (toRingElem α a) (toRingElem α b) (toRingElem α c)

/-- The monoid object `algebraPresheaf α` is commutative. -/
noncomputable instance isCommMonObjAlgebraPresheaf : IsCommMonObj (algebraPresheaf α) where
  mul_comm := by
    ext1 X
    refine ModuleCat.MonoidalCategory.tensor_ext (fun a b => ?_)
    exact mul_comm (toRingElem α b) (toRingElem α a)

/-- **Multiplication by a global section** `σ` of the presheaf of rings `A`, an endomorphism of
`A` read as a presheaf of `R`-modules. -/
noncomputable def algebraPresheafMulBy (σ : ∀ X, A.obj X)
    (hσ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), (A.map f).hom (σ X) = σ Y) :
    algebraPresheaf α ⟶ algebraPresheaf α where
  app X := @ModuleCat.ofHom _ _ ((algebraPresheaf α).obj X) ((algebraPresheaf α).obj X) _
    ((algebraPresheaf α).obj X).isModule _ ((algebraPresheaf α).obj X).isModule
    ({ toFun := fun a => ofRingElem α (σ X * toRingElem α a)
       map_add' := fun a b => mul_add (σ X) (toRingElem α a) (toRingElem α b)
       map_smul' := fun r a => mul_left_comm (σ X) ((α.app X).hom r) (toRingElem α a) } :
      (algebraPresheaf α).obj X →ₗ[(R ⋙ forget₂ _ RingCat).obj X] (algebraPresheaf α).obj X)
  naturality {X Y} f := ModuleCat.hom_ext (LinearMap.ext fun a => by
    change σ Y * (A.map f).hom (toRingElem α a) = (A.map f).hom (σ X * toRingElem α a)
    rw [map_mul, hσ f])

/-- **Multiplication by a global section is a morphism of modules over the monoid `A`**: it
commutes with the multiplication. -/
theorem algebraPresheafMulBy_whiskerRight_mul (σ : ∀ X, A.obj X)
    (hσ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), (A.map f).hom (σ X) = σ Y) :
    algebraPresheafMulBy α σ hσ ▷ algebraPresheaf α ≫ MonObj.mul =
      MonObj.mul ≫ algebraPresheafMulBy α σ hσ := by
  ext1 X
  refine ModuleCat.MonoidalCategory.tensor_ext (fun a b => ?_)
  exact mul_assoc (σ X) (toRingElem α a) (toRingElem α b)

/-- A section of the free presheaf of `A`-modules of rank one, read as an element of `A(X)`. -/
abbrev unitToRing {X : Cᵒᵖ} (a : (unit (A ⋙ forget₂ _ RingCat)).obj X) : A.obj X := a

/-- An element of `A(X)`, read as a section of the free presheaf of `A`-modules of rank one. -/
abbrev unitOfRing {X : Cᵒᵖ} (a : A.obj X) : (unit (A ⋙ forget₂ _ RingCat)).obj X := a

/-- **Multiplication by a global section** `σ` of a presheaf of commutative rings `A`, an
endomorphism of the free presheaf of `A`-modules of rank one. -/
noncomputable def unitMulBy (σ : ∀ X, A.obj X)
    (hσ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), (A.map f).hom (σ X) = σ Y) :
    unit (A ⋙ forget₂ _ RingCat) ⟶ unit (A ⋙ forget₂ _ RingCat) where
  app X := @ModuleCat.ofHom _ _ ((unit (A ⋙ forget₂ _ RingCat)).obj X)
    ((unit (A ⋙ forget₂ _ RingCat)).obj X) _ ((unit (A ⋙ forget₂ _ RingCat)).obj X).isModule _
    ((unit (A ⋙ forget₂ _ RingCat)).obj X).isModule
    ({ toFun := fun a => unitOfRing (σ X * unitToRing a)
       map_add' := fun a b => mul_add (σ X) (unitToRing a) (unitToRing b)
       map_smul' := fun r a => mul_left_comm (σ X) (unitToRing (A := A) r) (unitToRing a) } :
      (unit (A ⋙ forget₂ _ RingCat)).obj X →ₗ[(A ⋙ forget₂ _ RingCat).obj X]
        (unit (A ⋙ forget₂ _ RingCat)).obj X)
  naturality {X Y} f := ModuleCat.hom_ext (LinearMap.ext fun a => by
    change σ Y * (A.map f).hom (unitToRing a) = (A.map f).hom (σ X * unitToRing a)
    rw [map_mul, hσ f])

/-- `unitMulBy σ hσ` sends a section `a` over `X` to `σ X * a`. -/
lemma unitMulBy_app (σ : ∀ X, A.obj X)
    (hσ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), (A.map f).hom (σ X) = σ Y) (X : Cᵒᵖ)
    (a : (unit (A ⋙ forget₂ _ RingCat)).obj X) :
    unitToRing (((unitMulBy σ hσ).app X).hom a) = σ X * unitToRing a := rfl

end PresheafOfModules
