module

public import StacksFrontier.Homology.DerivedComplete.RingEquivTransport
public import StacksFrontier.RingTheory.Koszul.NoetherianDerivedCompleteEquivalence

/-!
# The full subcategory `D_comp(R, I)` of Stacks 0GZK in other models and over isomorphic rings

`Koszul.derivedCompleteObjects I` is the full subcategory of derived complete objects of
`D(R) = DerivedCategory (ModuleCat.{u} R)` for `R : Type u`, in the standard model of the
derived category, as used by Stacks 0GZK. This file transports it

* to any other model of `D(ModuleCat.{u} R)`, along the model comparison
  `StacksDraft.DerivedModel.modelEquiv`;
* to the derived complete objects for `e(I)` of `D(ModuleCat.{u} R')`, in any model, along a
  ring isomorphism `e : R ≃+* R'` with `R'` in an arbitrary universe (for instance
  `R = ULift.{u} A` and `R' = A`).

## Main definitions

* `Koszul.derivedCompleteObjectsModelEquivalence`
* `Koszul.derivedCompleteObjectsEquivalenceOfRingEquiv`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u u'

namespace Koszul

variable {R : Type u} [CommRing R]

/-- **`D_comp(R, I)` in an arbitrary model.** The full subcategory
`Koszul.derivedCompleteObjects I` of the standard model of `D(R)` is equivalent to the full
subcategory of derived complete objects of any other model `h` of `D(ModuleCat.{u} R)`, through
the model comparison. -/
def derivedCompleteObjectsModelEquivalence (h : HasDerivedCategory.{w} (ModuleCat.{u} R))
    (I : Ideal R) :
    (derivedCompleteObjects I).FullSubcategory ≌
      ObjectProperty.FullSubcategory
        (fun K : @DerivedCategory (ModuleCat.{u} R) _ _ h => IsDerivedComplete I K) :=
  Stacks.DerivedCompleteTransport.derivedCompleteModelEquivalence
    (HasDerivedCategory.standard _) h I

/-- The functor of `derivedCompleteObjectsModelEquivalence h I` is the model comparison. -/
@[simp]
theorem derivedCompleteObjectsModelEquivalence_functor_obj_obj
    (h : HasDerivedCategory.{w} (ModuleCat.{u} R)) (I : Ideal R)
    (X : (derivedCompleteObjects I).FullSubcategory) :
    ((derivedCompleteObjectsModelEquivalence h I).functor.obj X).obj =
      (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard _) h).functor.obj X.obj :=
  rfl

/-- **`D_comp(R, I)` over an isomorphic ring.** For a ring isomorphism `e : R ≃+* R'`, with
`R'` in any universe, the full subcategory `Koszul.derivedCompleteObjects I` of the standard
model of `D(ModuleCat.{u} R)` is equivalent to the full subcategory of objects of
`D(ModuleCat.{u} R')`, in any model, which are derived complete for `e(I)`. -/
def derivedCompleteObjectsEquivalenceOfRingEquiv {R' : Type u'} [CommRing R'] (e : R ≃+* R')
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (I : Ideal R) :
    (derivedCompleteObjects I).FullSubcategory ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{u} R') => IsDerivedComplete (I.map e) K) :=
  letI : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  Stacks.DerivedCompleteTransport.derivedCompleteEquivalenceOfRingEquiv e I

/-- The functor of `derivedCompleteObjectsEquivalenceOfRingEquiv e I` is induced by restriction
of scalars along `e.symm`. -/
@[simp]
theorem derivedCompleteObjectsEquivalenceOfRingEquiv_functor_obj_obj {R' : Type u'}
    [CommRing R'] (e : R ≃+* R') [HasDerivedCategory.{w} (ModuleCat.{u} R')] (I : Ideal R)
    (X : (derivedCompleteObjects I).FullSubcategory) :
    ((derivedCompleteObjectsEquivalenceOfRingEquiv e I).functor.obj X).obj =
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _ _
        (ModuleCat.restrictScalars.{u} e.symm.toRingHom) _ _ _).obj X.obj :=
  rfl

end Koszul

end
