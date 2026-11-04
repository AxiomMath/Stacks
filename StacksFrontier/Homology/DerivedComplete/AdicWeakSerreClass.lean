module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence
public import StacksFrontier.Homology.DerivedComplete.PseudoCoherentComplete
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Derived complete modules as a weak Serre subcategory

For a commutative ring `A` and an ideal `I`, the derived complete `A`-modules form a weak Serre
subcategory of `ModuleCat A`. An object of the derived category belongs to the subcategory cut out
by these modules on cohomology exactly when the object itself is derived complete.

## Main definitions

There are no new definitions.

## Main results

* `AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff`: derived complete
  modules form a weak Serre class, and derived completeness of a complex is detected on all of
  its cohomology modules.

## Implementation notes

The full subcategory `D_𝒞(A)` is expressed by the object property requiring every cohomology
module to lie in `𝒞`. Thus the second conjunct identifies its objects with the derived complete
objects of `D(A)`.

The weak Serre property is the two-out-of-three property of bijectivity of the recurrence
operator, which already holds for independent ring and module universes. The cohomological
criterion is available when the modules live in the ring's own universe; it is transported to an
independent module universe by the exact universe enlargement
`AdicKoszul.moduleUniverseLift` together with its scalar-tower comparison.

## References

* [The Stacks Project, Tag 091U](https://stacks.math.columbia.edu/tag/091U)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u v w

namespace AdicWeakSerre

/-- The exact universe enlargement preserves and reflects derived completeness. -/
private theorem complete_universeLift_iff (A : Type u) [CommRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{v} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)))] :
    IsDerivedComplete (I.comap (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom)
        ((AdicKoszul.derivedUniverseLift.{u, v} A).obj K) ↔
      IsDerivedComplete I K := by
  constructor
  · intro h f hf
    rw [isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
    refine (KoszulCompletion.derivedUniverseLift_scalarTower_zero_iff f K).mp ?_
    rw [← isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
    exact h (ULift.up f) hf
  · intro h f hf
    rw [isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
    refine (KoszulCompletion.derivedUniverseLift_scalarTower_zero_iff f.down K).mpr ?_
    rw [← isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
    exact h f.down hf

/-- Compatibility with complexes concentrated in degree zero. -/
private theorem completeModule_universeLift_iff (A : Type u) [CommRing A] (I : Ideal A)
    (M : ModuleCat.{v} A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)))] :
    IsDerivedCompleteModule (I.comap (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom)
        ((AdicKoszul.moduleUniverseLift.{u, v} A).obj M) ↔
      IsDerivedCompleteModule I M := by
  let e := ((AdicKoszul.moduleUniverseLift.{u, v} A).mapDerivedCategorySingleFunctor 0).app M
  exact ⟨fun h => (complete_universeLift_iff A I _).mp
      (DerivedCompleteRecurrence.isDerivedComplete_of_iso e.symm h),
    fun h => DerivedCompleteRecurrence.isDerivedComplete_of_iso e
      ((complete_universeLift_iff A I _).mpr h)⟩

/-- **Stacks 091U.** The derived complete modules with respect to `I` form a weak Serre
subcategory of `ModuleCat A`. Moreover, an object of `D(A)` is derived complete exactly when all
of its cohomology modules are derived complete. -/
@[stacks 091U]
public theorem derivedCompleteModules_isWeakSerreClass_and_homology_iff
    (A : Type u) [CommRing A] (I : Ideal A) :
    letI : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} A) :=
      moduleCat_hasExactLimitsOfShape_discrete.{v} A ℕ
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let C : ObjectProperty (ModuleCat.{v} A) :=
      fun M => IsDerivedCompleteModule I M
    C.IsWeakSerreClass ∧
      ∀ K : DerivedCategory (ModuleCat.{v} A),
        (∀ n : ℤ, C ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K)) ↔
          IsDerivedComplete I K := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} (ULift.{v} A)) :=
    moduleCat_hasExactLimitsOfShape_discrete.{max u v} (ULift.{v} A) ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} (ULift.{v} A))) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  let J := I.comap (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom
  let F := AdicKoszul.moduleUniverseLift.{u, v} A
  let P : ObjectProperty (ModuleCat.{max u v} (ULift.{v} A)) :=
    fun M => IsDerivedCompleteModule J M
  have hP1 : P.IsWeakSerreClass :=
    DerivedCompleteRecurrence.isWeakSerreClass_isDerivedCompleteModule J
  have hP2 : ∀ K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)),
      (∀ n : ℤ, P ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} (ULift.{v} A)) n).obj K)) ↔ IsDerivedComplete J K := fun K =>
    (isDerivedComplete_iff_forall_isDerivedCompleteModule_homology J K).symm
  have : P.IsWeakSerreClass := hP1
  dsimp only
  refine ⟨DerivedCompleteRecurrence.isWeakSerreClass_isDerivedCompleteModule I, ?_⟩
  intro K
  rw [← complete_universeLift_iff A I K, ← hP2]
  refine forall_congr' fun n => ?_
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} (ULift.{v} A)) n).obj
        (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K) :=
    (F.mapDerivedCategoryCompHomologyFunctorIso n).app K
  exact (completeModule_universeLift_iff A I _).symm.trans (P.prop_iff_of_iso e).symm

end AdicWeakSerre

end

end
