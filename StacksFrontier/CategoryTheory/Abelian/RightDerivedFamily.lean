module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Right derived functors of a family of functors

Let `Ψ : I ⥤ A ⥤ B` be a family of additive functors from an abelian category with injective
resolutions to an abelian category, indexed by a category `I`. Each member `Ψ i` has right
derived functors, and a morphism `i ⟶ j` induces a morphism between them, so the right derived
functors form a family `Ψ.rightDerivedFamily n : I ⥤ A ⥤ B` again.

The flipped family `Ψ.flip : A ⥤ (I ⥤ B)` is a single additive functor into the functor
category, and it has right derived functors of its own. Since evaluation at an object of `I` is
exact, these are computed objectwise: for every object `X` of `A` the functor
`(Ψ.flip.rightDerived n).obj X : I ⥤ B` is isomorphic to `i ↦ (Ψ i).rightDerived n X`,
*including its action on morphisms of `I`*, which is the morphism of right derived functors
induced by `Ψ.map`.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFamily`: the family of right derived functors of a family
  of additive functors.
* `CategoryTheory.Functor.rightDerivedFlipObjIso`: the right derived functors of `Ψ.flip` are
  computed objectwise, as functors on the index category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {I : Type*} [Category* I] {A : Type*} [Category* A] [Abelian A]
  [HasInjectiveResolutions A] {B : Type*} [Category* B] [Abelian B]

/-- The right derived functors of a family of additive functors, as a family: the member at
`i` is `(Ψ.obj i).rightDerived n`, and a morphism `i ⟶ j` acts by the morphism of right derived
functors induced by `Ψ.map`. -/
noncomputable def rightDerivedFamily (Ψ : I ⥤ A ⥤ B) [∀ i, (Ψ.obj i).Additive] (n : ℕ) :
    I ⥤ A ⥤ B where
  obj i := (Ψ.obj i).rightDerived n
  map φ := NatTrans.rightDerived (Ψ.map φ) n
  map_id i := by
    rw [← NatTrans.rightDerived_id]
    congr 1
    exact Ψ.map_id i
  map_comp φ ψ := by
    rw [← NatTrans.rightDerived_comp]
    congr 1
    exact Ψ.map_comp φ ψ

/-- The member at `i` of `Ψ.rightDerivedFamily n` is `(Ψ.obj i).rightDerived n`. -/
@[simp]
lemma rightDerivedFamily_obj (Ψ : I ⥤ A ⥤ B) [∀ i, (Ψ.obj i).Additive] (n : ℕ) (i : I) :
    (Ψ.rightDerivedFamily n).obj i = (Ψ.obj i).rightDerived n := rfl

/-- The action of `Ψ.rightDerivedFamily n` on a morphism `φ` is the morphism of right derived
functors `NatTrans.rightDerived (Ψ.map φ) n`. -/
@[simp]
lemma rightDerivedFamily_map (Ψ : I ⥤ A ⥤ B) [∀ i, (Ψ.obj i).Additive] (n : ℕ) {i j : I}
    (φ : i ⟶ j) : (Ψ.rightDerivedFamily n).map φ = NatTrans.rightDerived (Ψ.map φ) n := rfl

/-- A family of additive functors, flipped, is an additive functor into the functor category. -/
instance additive_flip (Ψ : I ⥤ A ⥤ B) [∀ i, (Ψ.obj i).Additive] : Ψ.flip.Additive where
  map_add := by
    intros
    ext i
    simp

/-- The value at `i` of the right derived functor of the flipped family is the right derived
functor of the member at `i`. -/
@[sga "4 V 2.4.2" "more general"]
noncomputable def rightDerivedFlipObjObjIso (Ψ : I ⥤ A ⥤ B) [∀ i, (Ψ.obj i).Additive] (n : ℕ)
    (X : A) (i : I) :
    ((Ψ.flip.rightDerived n).obj X).obj i ≅ ((Ψ.obj i).rightDerived n).obj X :=
  ((evaluation I B).obj i).mapIso ((injectiveResolution X).isoRightDerivedObj Ψ.flip n) ≪≫
    ((((Ψ.flip.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution X).cocomplex).sc n).mapHomologyIso ((evaluation I B).obj i)).symm ≪≫
    ((injectiveResolution X).isoRightDerivedObj (Ψ.obj i) n).symm

/-- **The right derived functors of a flipped family are computed objectwise.** For every object
`X`, the functor `(Ψ.flip.rightDerived n).obj X` on the index category is isomorphic to
`i ↦ (Ψ i).rightDerived n X`, whose action on a morphism of the index category is the morphism of
right derived functors induced by `Ψ.map`. -/
@[sga "4 V 2.4.2" "more general"]
noncomputable def rightDerivedFlipObjIso (Ψ : I ⥤ A ⥤ B) [∀ i, (Ψ.obj i).Additive] (n : ℕ)
    (X : A) :
    (Ψ.flip.rightDerived n).obj X ≅ (Ψ.rightDerivedFamily n).flip.obj X :=
  NatIso.ofComponents (rightDerivedFlipObjObjIso Ψ n X) (by
    intro i j φ
    let C := (injectiveResolution X).cocomplex
    let K := (Ψ.flip.mapHomologicalComplex (ComplexShape.up ℕ)).obj C
    let S := K.sc n
    let α := (injectiveResolution X).isoRightDerivedObj Ψ.flip n
    let β := fun k => (injectiveResolution X).isoRightDerivedObj (Ψ.obj k) n
    let m : ∀ k, (HomologicalComplex.homologyFunctor B _ n).obj
          (((Ψ.obj k).mapHomologicalComplex (ComplexShape.up ℕ)).obj C) ≅
        ((HomologicalComplex.homologyFunctor _ _ n).obj K).obj k :=
      fun k => S.mapHomologyIso ((evaluation I B).obj k)
    have hα : ((Ψ.flip.rightDerived n).obj X).map φ ≫ α.hom.app j =
        α.hom.app i ≫ ((HomologicalComplex.homologyFunctor _ _ n).obj K).map φ :=
      α.hom.naturality φ
    have hτ : (HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex (Ψ.map φ) (ComplexShape.up ℕ)).app C) =
        (m i).hom ≫ ((HomologicalComplex.homologyFunctor _ _ n).obj K).map φ ≫ (m j).inv :=
      ShortComplex.homologyMap_mapNatTrans S ((evaluation I B).map φ)
    have hR : (NatTrans.rightDerived (Ψ.map φ) n).app X = (β i).hom ≫
        (HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex (Ψ.map φ) (ComplexShape.up ℕ)).app C) ≫ (β j).inv :=
      InjectiveResolution.rightDerived_app_eq (Ψ.map φ) (injectiveResolution X) n
    change ((Ψ.flip.rightDerived n).obj X).map φ ≫ (α.hom.app j ≫ (m j).inv ≫ (β j).inv) =
      (α.hom.app i ≫ (m i).inv ≫ (β i).inv) ≫ (NatTrans.rightDerived (Ψ.map φ) n).app X
    rw [hR, hτ, reassoc_of% hα]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

end CategoryTheory.Functor

end
