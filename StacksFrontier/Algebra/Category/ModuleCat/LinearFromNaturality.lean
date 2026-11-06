module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Natural transformations of module-valued linear functors are linear

Let `A` be a commutative ring, let `C` be an `A`-linear preadditive category and let
`T T' : C ⥤ ModuleCat A` be two `A`-linear functors. Multiplication by `a : A` on `T.obj X` is
the image under `T` of the scalar `a • 𝟙 X`, so a natural transformation `η` between the
composites of `T` and `T'` with `forget₂ (ModuleCat A) AddCommGrpCat` has `A`-linear components
automatically: the naturality square of `η` at `a • 𝟙 X` is exactly the commutation of `η.app X`
with the two scalar actions. Consequently `η` lifts to a natural transformation `T ⟶ T'` whose
underlying transformation of abelian-group-valued functors is `η` itself, and the lift is an
isomorphism as soon as every component of `η` is.

## Main definitions

* `Stacks.LinearFromNaturality.appLinearMap` — a component of a natural transformation of the
  underlying `AddCommGrpCat`-valued functors, read as an `A`-linear map.
* `Stacks.LinearFromNaturality.lift` — the natural transformation `T ⟶ T'` it induces.
* `Stacks.LinearFromNaturality.liftIso` — the natural isomorphism `T ≅ T'` induced by a natural
  isomorphism of the underlying `AddCommGrpCat`-valued functors.

## Main results

* `Stacks.LinearFromNaturality.map_smul_id`: an `A`-linear functor carries the scalar `a • 𝟙 X`
  to the scalar `a • 𝟙 (T.obj X)`.
* `Stacks.LinearFromNaturality.app_comp_smul` and
  `Stacks.LinearFromNaturality.appLinearMap_smul`: **every natural transformation of the
  underlying `AddCommGrpCat`-valued functors has `A`-linear components.**
* `Stacks.LinearFromNaturality.whiskerRight_lift` and
  `Stacks.LinearFromNaturality.whiskerRight_liftIso_hom`: forgetting the module structure of the
  lift returns the transformation it was built from.
* `Stacks.LinearFromNaturality.isIso_lift_app`, `Stacks.LinearFromNaturality.isIso_lift` and
  `Stacks.LinearFromNaturality.isIso_lift_of_bijective`: the lift is an isomorphism as soon as
  every component of the given transformation is an isomorphism of abelian groups, equivalently
  as soon as every component is bijective.

## Implementation notes

Additivity of the two functors is not assumed. `CategoryTheory.Functor.Linear` is a class
independent of `CategoryTheory.Functor.Additive`, and the only facts about `T` and `T'` used
below are `CategoryTheory.Functor.map_smul` and `CategoryTheory.Functor.map_id`.

The comparisons with `forget₂ (ModuleCat A) AddCommGrpCat` are equalities rather than
isomorphisms. `ModuleCat.ofHom` leaves the underlying map of abelian groups untouched, and
`forget₂ (ModuleCat A) AddCommGrpCat` carries `a • 𝟙 M` to `ModuleCat.smul`, so
`forget₂_map_smul_id`, `forget₂_map_lift_app`, `whiskerRight_lift` and `whiskerRight_liftIso_hom`
all hold by unfolding.

Linearity of a component is recorded as the `A`-linear map `appLinearMap` rather than as an
equation `η.app X (a • x) = a • η.app X x`: the codomain of `η.app X` is the abelian group
`(T' ⋙ forget₂ (ModuleCat A) AddCommGrpCat).obj X`, which carries no action of `A`, so the
scalar multiple on the right has to be read in `T'.obj X`. The equation in that reading is
`appLinearMap_smul`, and `appLinearMap_apply` identifies the linear map with `η.app X`.

That the lift of an objectwise isomorphism is an isomorphism uses that
`forget₂ (ModuleCat A) AddCommGrpCat` reflects isomorphisms; the formulation in terms of
bijectivity of the components is the same hypothesis, by
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`.
-/

@[expose] public section

open CategoryTheory

universe v u u₁ v₁

namespace Stacks.LinearFromNaturality

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear A C]
  (T T' : C ⥤ ModuleCat.{v} A)

/-- Forgetting the module structure carries the scalar `a • 𝟙 M` to multiplication by `a`. -/
lemma forget₂_map_smul_id (M : ModuleCat.{v} A) (a : A) :
    (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}).map (a • 𝟙 M) = (M.smul a).asHom := rfl

/-- An `A`-linear functor carries the scalar `a • 𝟙 X` to the scalar `a • 𝟙 (T.obj X)`. -/
lemma map_smul_id [Functor.Linear A T] (X : C) (a : A) :
    T.map (a • 𝟙 X) = a • 𝟙 (T.obj X) := by
  rw [Functor.map_smul, T.map_id]

variable [Functor.Linear A T] [Functor.Linear A T']
  (η : T ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v} ⟶
    T' ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v})

/-- **A component of a natural transformation of the underlying abelian-group-valued functors
commutes with the scalar actions.** This is the naturality square of `η` at `a • 𝟙 X`. -/
lemma app_comp_smul (X : C) (a : A) :
    η.app X ≫ ((T'.obj X).smul a).asHom = ((T.obj X).smul a).asHom ≫ η.app X := by
  have h := η.naturality (a • 𝟙 X)
  rw [Functor.comp_map, Functor.comp_map, map_smul_id, map_smul_id, forget₂_map_smul_id,
    forget₂_map_smul_id] at h
  exact h.symm

/-- **A component of a natural transformation of the underlying abelian-group-valued functors,
read as an `A`-linear map.** -/
def appLinearMap (X : C) : T.obj X →ₗ[A] T'.obj X where
  toFun := η.app X
  map_add' := map_add _
  map_smul' a x := (ConcreteCategory.congr_hom (app_comp_smul T T' η X a) x).symm

/-- The linear map `appLinearMap T T' η X` agrees with `η.app X` on every element. -/
@[simp]
lemma appLinearMap_apply (X : C) (x : T.obj X) :
    appLinearMap T T' η X x = (η.app X) x := rfl

/-- A component of a natural transformation of the underlying abelian-group-valued functors
commutes with multiplication by a scalar. -/
lemma appLinearMap_smul (X : C) (a : A) (x : T.obj X) :
    appLinearMap T T' η X (a • x) = a • appLinearMap T T' η X x :=
  (appLinearMap T T' η X).map_smul a x

/-- **The lift of a natural transformation of the underlying abelian-group-valued functors to a
natural transformation `T ⟶ T'`.** -/
def lift : T ⟶ T' where
  app X := ModuleCat.ofHom (appLinearMap T T' η X)
  naturality _ _ f := (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}).map_injective (η.naturality f)

/-- Forgetting the module structure of a component of `lift T T' η` returns the corresponding
component of `η`. -/
@[simp]
lemma forget₂_map_lift_app (X : C) :
    (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}).map ((lift T T' η).app X) = η.app X := rfl

/-- **The lift is a lift:** forgetting the module structure of `lift η` returns `η`. -/
lemma whiskerRight_lift :
    Functor.whiskerRight (lift T T' η) (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}) = η := rfl

/-- A component of the lift is an isomorphism as soon as the corresponding component of the
given transformation is an isomorphism of abelian groups. -/
instance isIso_lift_app (X : C) [IsIso (η.app X)] : IsIso ((lift T T' η).app X) := by
  have : IsIso ((forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}).map ((lift T T' η).app X)) := by
    rw [forget₂_map_lift_app]
    infer_instance
  exact isIso_of_reflects_iso _ (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v})

/-- **The lift of an objectwise invertible transformation is an isomorphism.** -/
instance isIso_lift [∀ X, IsIso (η.app X)] : IsIso (lift T T' η) :=
  NatIso.isIso_of_isIso_app _

/-- **The lift of a transformation with bijective components is an isomorphism.** -/
lemma isIso_lift_of_bijective (h : ∀ X : C, Function.Bijective (η.app X)) :
    IsIso (lift T T' η) := by
  have : ∀ X : C, IsIso (η.app X) := fun X => (ConcreteCategory.isIso_iff_bijective _).2 (h X)
  infer_instance

/-- **The lift of a natural isomorphism of the underlying abelian-group-valued functors to a
natural isomorphism `T ≅ T'`.** -/
noncomputable def liftIso (e : T ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v} ≅
    T' ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}) : T ≅ T' :=
  asIso (lift T T' e.hom)

/-- Forgetting the module structure of `liftIso e` returns `e`. -/
lemma whiskerRight_liftIso_hom (e : T ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v} ≅
    T' ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}) :
    Functor.whiskerRight (liftIso T T' e).hom
      (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}) = e.hom := rfl

end Stacks.LinearFromNaturality

end
