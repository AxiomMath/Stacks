module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An exact functor on the bounded below derived category

An additive functor `F : A ⥤ B` of abelian categories which preserves finite limits and finite
colimits acts on unbounded derived categories by `Functor.mapDerivedCategory`, degreewise on
complexes. Being exact it preserves boundedness below of the cohomology, so that action
restricts to the bounded below derived categories. This file constructs that restriction,
`Functor.mapDerivedCategoryPlus`, together with the isomorphism saying that it too is induced
degreewise.

Alongside it are results which do not use exactness: the unit of the total right derived functor of
a homology-preserving functor on bounded below derived categories is invertible, right derivation
there is compatible with postcomposition by an arbitrary functor, an additive natural
transformation acts on bounded below homotopy categories, and an adjunction of additive functors
whose left adjoint preserves homology induces an adjunction of the total right derived functors on
bounded below derived categories.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryPlus`: the action of an exact functor on the
  bounded below derived category.
* `CategoryTheory.Functor.mapHomotopyCategoryPlusNatTrans`: the action of a natural
  transformation of additive functors on bounded below homotopy categories.
* `CategoryTheory.Functor.mapHomotopyCategoryPlusIdComparison`: the comparison of the identity
  functor of a bounded below homotopy category with the action of the identity functor.
* `CategoryTheory.Adjunction.mapHomotopyCategoryPlus`: the adjunction induced on bounded below
  homotopy categories.
* `CategoryTheory.Adjunction.rightDerivedFunctorPlus`: the adjunction induced on bounded below
  derived categories by an adjunction whose left adjoint preserves homology.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryPlusFactorsh`: the bounded below derived action of
  an exact functor is induced degreewise.
* `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology`: the unit of
  the total right derived functor of a homology-preserving functor is invertible.
* `CategoryTheory.Functor.isRightDerivedFunctor_postcomp`: right derivation on the bounded
  below derived category is compatible with postcomposition.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public noncomputable section

universe u₁ v₁ w₁ u₂ v₂ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

section Exact

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The action of an exact functor on the bounded below derived category: the restriction of
its action on the unbounded derived category, which preserves boundedness below. -/
def mapDerivedCategoryPlus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
  DerivedCategory.TStructure.t.plus.lift (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (by
    intro K
    let M := DerivedCategory.Plus.Qh.objPreimage K
    let e := (F.mapDerivedCategory.mapIso
      (DerivedCategory.Plus.ι.mapIso (DerivedCategory.Plus.Qh.objObjPreimageIso K))).symm ≪≫
      F.mapDerivedCategoryFactorsh.app M.obj
    exact DerivedCategory.TStructure.t.plus.prop_of_iso e.symm
      (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj M)).property)

/-- The bounded below derived action of an exact functor is induced degreewise. -/
def mapDerivedCategoryPlusFactorsh :
    DerivedCategory.Plus.Qh ⋙ F.mapDerivedCategoryPlus ≅
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (F.mapDerivedCategoryFactorsh.app K.obj))
    (by intro K L f; ext; exact F.mapDerivedCategoryFactorsh.hom.naturality f.hom)

/-- `mapDerivedCategoryPlusFactorsh` presents the bounded below derived action as a lift of the
degreewise action along the localization functor. -/
instance mapDerivedCategoryPlusLifting :
    Localization.Lifting DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) F.mapDerivedCategoryPlus :=
  ⟨F.mapDerivedCategoryPlusFactorsh⟩

end Exact

section RightDerived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The unit of the total right derived functor on bounded below derived categories is
invertible for a functor which preserves homology. -/
lemma isIso_rightDerivedFunctorPlusUnit_of_preservesHomology [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology] : IsIso F.rightDerivedFunctorPlusUnith := by
  apply Functor.isIso_of_isRightDerivedFunctor_of_inverts
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
    (W := HomotopyCategory.Plus.quasiIso A)
  intro K L f hf
  suffices IsIso (DerivedCategory.Plus.ι.map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map f)) from
    isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  change IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map f.hom))
  rw [DerivedCategory.isIso_Qh_map_iff]
  obtain ⟨K, hK⟩ := K
  obtain ⟨L, hL⟩ := L
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective f.hom
  change HomotopyCategory.quasiIso A (.up ℤ) f.hom at hf
  rw [← hg, HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
  rw [← hg]
  change HomotopyCategory.quasiIso B (.up ℤ)
    ((HomotopyCategory.quotient B (.up ℤ)).map ((F.mapHomologicalComplex (.up ℤ)).map g))
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  have : QuasiIso g := hf
  change QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map g)
  infer_instance

/-- Right derivation on bounded below derived categories is compatible with postcomposition by an
arbitrary functor `G`: `F.rightDerivedFunctorPlus ⋙ G`, with the unit whiskered by `G`, is a right
derived functor of `F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ G`. -/
instance isRightDerivedFunctor_postcomp {E : Type*} [Category* E] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (G : DerivedCategory.Plus B ⥤ E) :
    (F.rightDerivedFunctorPlus ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight F.rightDerivedFunctorPlusUnith G)
      (HomotopyCategory.Plus.quasiIso A) := by
  apply (HomotopyCategory.Plus.localizerMorphism_derives
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ G)).isRightDerivedFunctor_of_isIso
  intro K
  dsimp
  infer_instance

end RightDerived

section HomotopyCategory

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B]

/-- The action on bounded below homotopy categories of a natural transformation of additive
functors. -/
def mapHomotopyCategoryPlusNatTrans {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus where
  app K := ObjectProperty.homMk ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K.obj)
  naturality K L f := by
    ext
    exact (NatTrans.mapHomotopyCategory α (.up ℤ)).naturality f.hom

/-- The functor induced on a bounded below homotopy category by the identity functor is
canonically the identity. -/
def mapHomotopyCategoryPlusIdComparison (A : Type u₁) [Category.{v₁} A] [Preadditive A] :
    𝟭 (HomotopyCategory.Plus A) ⟶ (𝟭 A).mapHomotopyCategoryPlus := by
  let e : (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.natIsoLift _
      (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)))
  exact
    { app := fun K ↦ ObjectProperty.homMk (e.inv.app K.obj)
      naturality := by
        intro K L f
        ext
        exact e.inv.naturality f.hom }

end HomotopyCategory

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

section Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {L : A ⥤ B} {R : B ⥤ A}

/-- The degreewise adjunction on homotopy categories, restricted to the bounded below full
subcategories. -/
def mapHomotopyCategoryPlus [L.Additive] [R.Additive] (adj : L ⊣ R) :
    L.mapHomotopyCategoryPlus ⊣ R.mapHomotopyCategoryPlus :=
  (adj.mapHomotopyCategory (ComplexShape.up ℤ)).restrictFullyFaithful
    (HomotopyCategory.Plus.fullyFaithfulι A) (HomotopyCategory.Plus.fullyFaithfulι B)
    (Iso.refl _) (Iso.refl _)

/-- **An adjunction of additive functors descends to the bounded below derived categories**,
provided the left adjoint preserves homology:
`L.rightDerivedFunctorPlus ⊣ R.rightDerivedFunctorPlus`. -/
@[sga "4 V 2.2" "more general"]
def rightDerivedFunctorPlus [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [EnoughInjectives A] [EnoughInjectives B] [L.Additive] [R.Additive] (adj : L ⊣ R)
    [L.PreservesHomology] :
    L.rightDerivedFunctorPlus ⊣ R.rightDerivedFunctorPlus := by
  letI := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hα : L.rightDerivedFunctorPlus.IsLeftDerivedFunctor
      (asIso L.rightDerivedFunctorPlusUnith).inv (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (asIso L.rightDerivedFunctorPlusUnith).symm
  have hαR : (L.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (asIso L.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso L.rightDerivedFunctorPlusUnith).symm _)
  have hβL : (R.rightDerivedFunctorPlus ⋙ L.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorPlusUnith L.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B) := by
    apply (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso
    intro K
    dsimp
    infer_instance
  exact adj.mapHomotopyCategoryPlus.derived
    (HomotopyCategory.Plus.quasiIso A) (HomotopyCategory.Plus.quasiIso B)
    (asIso L.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlusUnith

end Derived

end CategoryTheory.Adjunction
