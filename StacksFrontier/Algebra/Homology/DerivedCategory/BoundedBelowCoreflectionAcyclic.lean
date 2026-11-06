module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCohomologicalDescent

/-!
# `D⁺(ℬ) ≌ D⁺_ℬ(𝒜)` for a coreflective exact subcategory with acyclic coreflection

Let `𝒜` be an abelian category with enough injectives and let `ℬ ⊆ 𝒜` be the full subcategory
cut out by an object property `P` closed under kernels, cokernels and finite products, so that
`ℬ` is abelian and the inclusion `i = P.ι` is exact. Suppose that `i` has a right adjoint
`R : 𝒜 ⥤ ℬ`. Then `R` carries injectives to injectives, so `ℬ` has enough injectives, and the
adjunction descends to the bounded below derived categories, `i ⊣ RR` with `RR` the total right
derived functor of `R`. If moreover every object of `ℬ` is acyclic for `R`, the unit and the
counit of this derived adjunction are invertible on single objects of `ℬ`, and the canonical
comparison functor `D⁺(ℬ) ⥤ D⁺_ℬ(𝒜)` is an equivalence with quasi-inverse `RR`.

This is the argument of [Stacks, Tag 06ZV], where `𝒜` is the category of `𝒪`-modules on the big
site of an affine scheme, `ℬ = Adeq(𝒪)`, `R` is the adequator of [Stacks, Tag 06ZS] and the
acyclicity is [Stacks, Tag 06ZU].

## Main definitions

* `DerivedCategoryB.coreflectionDerivedAdjunction`: the derived adjunction
  `i ⊣ RR : D⁺(𝒜) ⥤ D⁺(ℬ)`, whose left adjoint is the degreewise action
  `CategoryTheory.Functor.mapDerivedCategoryPlus` of the inclusion.

## Main results

* `DerivedCategoryB.isIso_coreflectionDerivedAdjunction_unit_app_single` and
  `DerivedCategoryB.isIso_coreflectionDerivedAdjunction_counit_app_single`: the unit and the
  counit of the derived adjunction are invertible at an object `X` of `ℬ` placed in degree zero
  as soon as `X` is acyclic for `R`.
* `DerivedCategoryB.isEquivalence_boundedBelowComparison_of_rightAcyclic`: the comparison functor
  `D⁺(ℬ) ⥤ D⁺_ℬ(𝒜)` is an equivalence when every object of `ℬ` is acyclic for `R`.

## Implementation notes

The derived adjunction is `CategoryTheory.Adjunction.rightDerivedFunctorPlus`, whose left adjoint
is the total right derived functor of the exact inclusion; it is transported to the degreewise
action along `CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`. The unit
at `X[0]` is computed by `CategoryTheory.Adjunction.derivedη_fac_app`: up to isomorphisms it is
the degreewise unit, invertible because the inclusion is fully faithful
(`CategoryTheory.Adjunction.isIso_mapHomotopyCategoryPlus_unit_app`), followed by the unit of
`RR` at `X[0]`, whose invertibility is the definition of `X` being acyclic for `R`.
The counit at `X[0]` is then inverse to the image of the unit, by a triangle identity.

The passage from single objects to all of `D⁺` is
`DerivedCategoryB.isEquivalence_boundedBelowComparison`. It asks for a shift and a triangulated
structure on the right adjoint compatible with the adjunction; they are the ones the adjunction
induces from those of the left adjoint, `CategoryTheory.Adjunction.rightAdjointCommShift` and
`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`, and `RR` preserves boundedness below by
`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`.

## References

* [Stacks Project, Tag 06ZV](https://stacks.math.columbia.edu/tag/06ZV)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

universe v u

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace DerivedCategoryB

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
  (P : ObjectProperty A) [P.ContainsZero]
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts]
  [PreservesFiniteLimits P.ι] [PreservesFiniteColimits P.ι]
  [HasDerivedCategory P.FullSubcategory]
  {R : A ⥤ P.FullSubcategory} [R.Additive] (adj : P.ι ⊣ R)

/-- **The derived adjunction of a coreflective exact subcategory**: the derived inclusion
`D⁺(ℬ) ⥤ D⁺(𝒜)` is left adjoint to the total right derived functor of the coreflection
`R : 𝒜 ⥤ ℬ`. -/
def coreflectionDerivedAdjunction :
    P.ι.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus :=
  haveI : EnoughInjectives P.FullSubcategory := EnoughInjectives.of_adjunction adj
  haveI : P.ι.PreservesHomology := Functor.preservesHomologyOfExact _
  adj.rightDerivedFunctorPlus.ofNatIsoLeft P.ι.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus

/-- **The unit of the derived adjunction at an `R`-acyclic object** of `ℬ` placed in degree zero
is invertible. -/
theorem isIso_coreflectionDerivedAdjunction_unit_app_single (X : P.FullSubcategory)
    (hX : R.rightAcyclic (P.ι.obj X)) :
    IsIso ((coreflectionDerivedAdjunction P adj).unit.app
      ((Plus.singleFunctor P.FullSubcategory 0).obj X)) := by
  have : EnoughInjectives P.FullSubcategory := EnoughInjectives.of_adjunction adj
  have : P.ι.PreservesHomology := Functor.preservesHomologyOfExact _
  rw [NatTrans.isIso_app_iff_of_iso _
    ((Functor.singleFunctorPlusIsoCompQh (A := P.FullSubcategory) 0).app X)]
  simp only [coreflectionDerivedAdjunction, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app]
  rw [isIso_comp_right_iff]
  have := P.ι.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hαR : (P.ι.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (asIso P.ι.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso P.FullSubcategory) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso P.ι.rightDerivedFunctorPlusUnith).symm _)
  let K := (HomotopyCategory.Plus.singleFunctor P.FullSubcategory 0).obj X
  have h₁ : IsIso (adj.mapHomotopyCategoryPlus.unit.app K) :=
    adj.isIso_mapHomotopyCategoryPlus_unit_app K
  have h₂ : IsIso (R.rightDerivedFunctorPlusUnith.app (P.ι.mapHomotopyCategoryPlus.obj K)) := by
    refine (NatTrans.isIso_app_iff_of_iso R.rightDerivedFunctorPlusUnith
      (P.ι.mapHomotopyCategoryPlusObjSingleIso 0 X)).2 ?_
    -- `rightDerivedFunctorPlusUnith` is not exposed: compare it with `totalRightDerivedUnit`.
    have := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc R.rightDerivedFunctorPlus
      R.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A) _
      ((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A))).1 inferInstance
    have hX' : IsIso (((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A)).app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj (P.ι.obj X))) := hX
    rw [← Functor.rightDerived_fac_app R.rightDerivedFunctorPlus R.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso A) _ _] at hX'
    exact (isIso_comp_right_iff _ _).1 hX'
  have h₃ : IsIso ((Adjunction.derivedη adj.mapHomotopyCategoryPlus
      (HomotopyCategory.Plus.quasiIso _) (asIso P.ι.rightDerivedFunctorPlusUnith).inv
      R.rightDerivedFunctorPlusUnith).app (Plus.Qh.obj K) ≫
      R.rightDerivedFunctorPlus.map ((asIso P.ι.rightDerivedFunctorPlusUnith).inv.app K)) := by
    rw [Adjunction.derivedη_fac_app (adj := adj.mapHomotopyCategoryPlus)
      (W₁ := HomotopyCategory.Plus.quasiIso _) (α := (asIso P.ι.rightDerivedFunctorPlusUnith).inv)
      (β := R.rightDerivedFunctorPlusUnith) K]
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) h₂
  exact (isIso_comp_right_iff _ _).1 h₃

/-- **The counit of the derived adjunction at an `R`-acyclic object** of `ℬ` placed in degree zero
in `D⁺(𝒜)` is invertible: by a triangle identity it is inverse to the image of the unit. -/
theorem isIso_coreflectionDerivedAdjunction_counit_app_single (X : P.FullSubcategory)
    (hX : R.rightAcyclic (P.ι.obj X)) :
    IsIso ((coreflectionDerivedAdjunction P adj).counit.app
      ((Plus.singleFunctor A 0).obj (P.ι.obj X))) := by
  have := isIso_coreflectionDerivedAdjunction_unit_app_single P adj X hX
  have h' : IsIso (P.ι.mapDerivedCategoryPlus.map ((coreflectionDerivedAdjunction P adj).unit.app
      ((Plus.singleFunctor P.FullSubcategory 0).obj X)) ≫
      (coreflectionDerivedAdjunction P adj).counit.app (P.ι.mapDerivedCategoryPlus.obj
        ((Plus.singleFunctor P.FullSubcategory 0).obj X))) := by
    rw [(coreflectionDerivedAdjunction P adj).left_triangle_components
      ((Plus.singleFunctor P.FullSubcategory 0).obj X)]
    exact Iso.isIso_hom (Iso.refl _)
  exact (NatTrans.isIso_app_iff_of_iso _
    ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle P.ι 0).app X)).1
    (IsIso.of_isIso_comp_left (P.ι.mapDerivedCategoryPlus.map
      ((coreflectionDerivedAdjunction P adj).unit.app
        ((Plus.singleFunctor P.FullSubcategory 0).obj X)))
      ((coreflectionDerivedAdjunction P adj).counit.app (P.ι.mapDerivedCategoryPlus.obj
        ((Plus.singleFunctor P.FullSubcategory 0).obj X))))

variable [P.IsClosedUnderIsomorphisms]

include adj in
/-- **The comparison `D⁺(ℬ) ⥤ D⁺_ℬ(𝒜)` is an equivalence for a coreflective exact subcategory
whose coreflection is acyclic on it.** Let `𝒜` have enough injectives, let `ℬ` be closed under
kernels, cokernels and finite products with exact inclusion, and let the inclusion have a right
adjoint `R` for which every object of `ℬ` is acyclic. Then the canonical functor from `D⁺(ℬ)` to
the bounded below objects of `D(𝒜)` with cohomology in `ℬ` is an equivalence; its quasi-inverse
is the total right derived functor of `R`.

This is the argument of [Stacks, Tag 06ZV]. -/
theorem isEquivalence_boundedBelowComparison_of_rightAcyclic
    (hR : ∀ X : P.FullSubcategory, R.rightAcyclic (P.ι.obj X)) :
    (boundedBelowComparison P).IsEquivalence := by
  let adj' := coreflectionDerivedAdjunction P adj
  let : R.rightDerivedFunctorPlus.CommShift ℤ := adj'.rightAdjointCommShift ℤ
  have : adj'.CommShift ℤ := adj'.commShift_of_leftAdjoint ℤ
  have : R.rightDerivedFunctorPlus.IsTriangulated := adj'.isTriangulated_rightAdjoint
  exact isEquivalence_boundedBelowComparison P R.rightDerivedFunctorPlus adj'
    (fun K m _ ↦ R.isGE_rightDerivedFunctorPlus_obj K m)
    (fun X ↦ isIso_coreflectionDerivedAdjunction_unit_app_single P adj X (hR X))
    (fun M hM ↦ isIso_coreflectionDerivedAdjunction_counit_app_single P adj ⟨M, hM⟩ (hR _))

end DerivedCategoryB
