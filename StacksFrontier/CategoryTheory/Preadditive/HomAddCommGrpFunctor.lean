module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# `Hom(A, -)` as a functor to abelian groups, with morphisms as elements

For an object `A` of a preadditive category `C`, `homAddCommGrpFunctor A : C ⥤ AddCommGrpCat`
sends `X` to the abelian group `A ⟶ X` and `q : X ⟶ Y` to postcomposition with `q`. It is
isomorphic to `preadditiveCoyoneda.obj (op A)` with identity components, but its objects and
maps are the hom groups and the compositions on the nose.

## Main definitions

* `CategoryTheory.homAddCommGrpFunctor`: the functor `Hom(A, -) : C ⥤ AddCommGrpCat`.
* `CategoryTheory.homAddCommGrpFunctorPrecomp` and `CategoryTheory.homAddCommGrpFunctorIsoOfIso`:
  its functoriality in `A`.
* `CategoryTheory.preadditiveCoyonedaIsoHomAddCommGrpFunctor`: the isomorphism
  `preadditiveCoyoneda.obj (op A) ≅ homAddCommGrpFunctor A`.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- **`Hom(A, -)` as a functor to abelian groups.** -/
def homAddCommGrpFunctor (A : C) : C ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (A ⟶ X)
  map q := AddCommGrpCat.ofHom (Preadditive.rightComp A q)
  map_id X := by
    ext x
    exact Category.comp_id x
  map_comp q q' := by
    ext x
    exact (Category.assoc x q q').symm

/-- The map `(homAddCommGrpFunctor A).map q` sends `x : A ⟶ X` to `x ≫ q`. -/
theorem homAddCommGrpFunctor_map_hom_apply (A : C) {X Y : C} (q : X ⟶ Y) (x : A ⟶ X) :
    ((homAddCommGrpFunctor A).map q).hom x = x ≫ q :=
  rfl

/-- Precomposition with `φ : A ⟶ A'`, as a natural transformation
`Hom(A', -) ⟶ Hom(A, -)`. -/
def homAddCommGrpFunctorPrecomp {A A' : C} (φ : A ⟶ A') :
    homAddCommGrpFunctor A' ⟶ homAddCommGrpFunctor A where
  app X := AddCommGrpCat.ofHom (Preadditive.leftComp X φ)
  naturality X Y q := by
    ext x
    exact (Category.assoc φ x q).symm

/-- The component at `X` of `homAddCommGrpFunctorPrecomp φ` sends `x : A' ⟶ X` to `φ ≫ x`. -/
theorem homAddCommGrpFunctorPrecomp_app_hom_apply {A A' : C} (φ : A ⟶ A') (X : C)
    (x : A' ⟶ X) : ((homAddCommGrpFunctorPrecomp φ).app X).hom x = φ ≫ x :=
  rfl

/-- An isomorphism `A ≅ A'` induces `Hom(A', -) ≅ Hom(A, -)`. -/
def homAddCommGrpFunctorIsoOfIso {A A' : C} (e : A ≅ A') :
    homAddCommGrpFunctor A' ≅ homAddCommGrpFunctor A where
  hom := homAddCommGrpFunctorPrecomp e.hom
  inv := homAddCommGrpFunctorPrecomp e.inv
  hom_inv_id := by
    ext X x
    exact e.inv_hom_id_assoc (show A' ⟶ X from x)
  inv_hom_id := by
    ext X x
    exact e.hom_inv_id_assoc (show A ⟶ X from x)

/-- `preadditiveCoyoneda.obj (op A)` is `Hom(A, -)`. -/
def preadditiveCoyonedaIsoHomAddCommGrpFunctor (A : C) :
    preadditiveCoyoneda.obj (op A) ≅ homAddCommGrpFunctor A :=
  NatIso.ofComponents (fun X => AddEquiv.toAddCommGrpIso (AddEquiv.refl (A ⟶ X)))
    (fun q => by
      ext x
      rfl)

/-- The component at `X` of `preadditiveCoyonedaIsoHomAddCommGrpFunctor A` is the identity
of `A ⟶ X`. -/
theorem preadditiveCoyonedaIsoHomAddCommGrpFunctor_hom_app_hom_apply (A X : C) (x : A ⟶ X) :
    ((preadditiveCoyonedaIsoHomAddCommGrpFunctor A).hom.app X).hom x = x :=
  rfl

end CategoryTheory

end
