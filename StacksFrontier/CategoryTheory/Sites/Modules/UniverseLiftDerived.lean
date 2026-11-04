module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSheaf
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Derived categories along an equivalence of ringed sites, with a change of ring universe

An exact equivalence of abelian categories `E : A ≌ B` induces an equivalence of derived
categories `D(A) ≌ D(B)` (`Dualizing.mapDerivedCategoryEquivalenceOfEquivalence`), and the
induced functor commutes with the cohomology functors
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`). This file records the consequence
for subcategories cut out by a condition on the cohomology objects: if a property `P'` of objects
of `B` corresponds to a property `P` of objects of `A` along `E`, then the subcategories
`D_P(A)` and `D_{P'}(B)` of objects all of whose cohomology objects satisfy the property
correspond as well. It then specializes everything to the equivalence of sheaves of modules
attached to a ring transport, `Stacks.UniverseLift.RingTransport.sheafEquivalence`.

## Main definitions

* `Stacks.UniverseLift.derivedCategoryBEquivalence`: the equivalence `D_P(A) ≌ D_{P'}(B)`.
* `Stacks.UniverseLift.RingTransport.derivedEquivalence`: the equivalence of derived categories of
  sheaves of modules induced by a ring transport.
* `Stacks.UniverseLift.RingTransport.derivedHomologyIso`: it commutes with cohomology.

## Main results

* `Stacks.UniverseLift.derivedCategoryB_mapDerivedCategory_obj_iff`: the cohomology of `E(K)`
  satisfies `P'` exactly when that of `K` satisfies `P`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategoryB

universe w₁ w₂ m v₁ v₂ u₁ u₂ r₁ r₂

namespace Stacks.UniverseLift

section General

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

/-- **The cohomology of the image of a complex under an exact functor.** If `F` is exact and the
property `P'` of objects of `B` corresponds to the property `P` of objects of `A` along `F`, then
all cohomology objects of `F(K)` satisfy `P'` exactly when all cohomology objects of `K`
satisfy `P`. -/
theorem derivedCategoryB_mapDerivedCategory_obj_iff (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : ObjectProperty A)
    (P' : ObjectProperty B) [P'.IsClosedUnderIsomorphisms] (h : ∀ X, P' (F.obj X) ↔ P X)
    (K : DerivedCategory A) :
    derivedCategoryB P' (F.mapDerivedCategory.obj K) ↔ derivedCategoryB P K := by
  refine forall_congr' fun n ↦ ?_
  rw [← h]
  exact P'.prop_iff_of_iso ((F.mapDerivedCategoryHomologyIso n).app K)

variable (E : A ≌ B) [E.functor.Additive] [E.inverse.Additive]
  (P : ObjectProperty A) (P' : ObjectProperty B) [P'.IsClosedUnderIsomorphisms]
  (h : ∀ X, P' (E.functor.obj X) ↔ P X)

/-- **The subcategories cut out by corresponding cohomology conditions are equivalent.** For an
additive equivalence `E : A ≌ B` and properties `P` of `A` and `P'` of `B` with
`P'(E X) ↔ P(X)`, the full subcategories `D_P(A)` and `D_{P'}(B)` of the derived categories,
of the objects all of whose cohomology objects satisfy the property, are equivalent through
the derived functor of `E`. -/
noncomputable def derivedCategoryBEquivalence :
    (derivedCategoryB P).FullSubcategory ≌ (derivedCategoryB P').FullSubcategory :=
  letI : (derivedCategoryB P').IsClosedUnderIsomorphisms :=
    ⟨fun {X Y} e hX n ↦ P'.prop_of_iso ((DerivedCategory.homologyFunctor B n).mapIso e) (hX n)⟩
  (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E).congrFullSubcategory (by
    ext K
    exact derivedCategoryB_mapDerivedCategory_obj_iff E.functor P P' h K)

/-- The functor of `derivedCategoryBEquivalence` is the derived functor of `E`. -/
lemma derivedCategoryBEquivalence_functor_obj_obj
    (K : (derivedCategoryB P).FullSubcategory) :
    ((derivedCategoryBEquivalence E P P' h).functor.obj K).obj =
      E.functor.mapDerivedCategory.obj K.obj :=
  rfl

end General

namespace RingTransport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{r₁}} {R' : Sheaf K RingCat.{r₂}} (T : RingTransport e R.obj R'.obj)
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory.{w₁} (SheafOfModules.{m} R)]
  [HasDerivedCategory.{w₂} (SheafOfModules.{m} R')]

/-- **The equivalence of derived categories of sheaves of modules induced by a ring
transport.** Its functor is the derived functor of `RingTransport.sheafFunctor`, which is exact,
so no derived correction is needed. -/
noncomputable def derivedEquivalence :
    DerivedCategory (SheafOfModules.{m} R) ≌ DerivedCategory (SheafOfModules.{m} R') :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence T.sheafEquivalence

/-- The functor of the derived equivalence is the derived functor of the transport. -/
lemma derivedEquivalence_functor :
    (T.derivedEquivalence : DerivedCategory (SheafOfModules.{m} R) ≌ _).functor =
      T.sheafFunctor.mapDerivedCategory :=
  rfl

/-- **The derived transport commutes with cohomology**: `Hⁿ(T(K)) ≅ T(Hⁿ(K))`, naturally in
`K`. -/
noncomputable def derivedHomologyIso (n : ℤ) :
    (T.derivedEquivalence : DerivedCategory (SheafOfModules.{m} R) ≌ _).functor ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{m} R') n ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{m} R) n ⋙ T.sheafFunctor :=
  T.sheafFunctor.mapDerivedCategoryHomologyIso n

end RingTransport

end Stacks.UniverseLift
