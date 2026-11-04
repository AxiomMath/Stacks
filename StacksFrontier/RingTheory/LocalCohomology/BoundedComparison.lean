module

public import StacksFrontier.RingTheory.LocalCohomology.Sweep.ClosedSupportColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bounded-below and unbounded derived functors of sections with support agree

Let `A` be a commutative ring and `T ⊆ Spec(A)` a subset. Sections with support in `T` have two
total right derived functors: one on the bounded-below derived category,
`derivedSectionsWithSupportInPlus`, built from injective resolutions, and one on the unbounded
derived category, `derivedSectionsWithSupportIn`, built from K-injective resolutions. This file
identifies the first with the restriction of the second:
$$ RΓ^+_T(-) \;\cong\; RΓ_T(-) \quad\text{on } D^+(A). $$

## Main results

* `Stacks.LocalCohomology.nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso` — the
  comparison isomorphism.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-- Sections with support in `T`, applied to bounded-below complexes and landing in the
unbounded derived category. -/
private abbrev plusSectionsToUnbounded :
    HomotopyCategory.Plus (ModuleCat.{max u v} A) ⥤ DerivedCategory (ModuleCat.{max u v} A) :=
  (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι

/-- The canonical unit of the bounded-below derived functor, pushed into the unbounded derived
category. -/
private def plusUnit : plusSectionsToUnbounded.{u, v} A T ⟶ DerivedCategory.Plus.Qh ⋙
    (derivedSectionsWithSupportInPlus.{u, v} A T ⋙ DerivedCategory.Plus.ι) :=
  whiskerRight (sectionsWithSupportInFunctor.{u, v} A T).rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι

/-- The canonical unit of the unbounded derived functor, restricted to bounded-below objects. -/
private def unboundedUnit : plusSectionsToUnbounded.{u, v} A T ⟶ DerivedCategory.Plus.Qh ⋙
    (DerivedCategory.Plus.ι ⋙ derivedSectionsWithSupportIn.{u, v} A T) :=
  whiskerLeft (HomotopyCategory.Plus.ι (ModuleCat.{max u v} A))
    (derivedSectionsWithSupportInUnit.{u, v} A T)

/-- The canonical unit of the unbounded derived functor is invertible at a bounded-below object
of the homotopy category whose terms are injective. -/
private theorem isIso_unboundedUnit_app_of_injective
    (X : HomotopyCategory.Plus (ModuleCat.{max u v} A))
    [∀ n : ℤ, Injective (X.obj.as.X n)] :
    IsIso ((unboundedUnit.{u, v} A T).app X) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, CochainComplex.IsStrictlyGE X.obj.as n := by
    have hX := X.property
    rwa [show X.obj = (HomotopyCategory.quotient _ _).obj X.obj.as from rfl,
      HomotopyCategory.plus_quotient_obj_iff] at hX
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (fun K ↦ by
      obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨I, q, hI, hq⟩)).2 DerivedCategory.Qh
      (derivedSectionsWithSupportIn.{u, v} A T) (derivedSectionsWithSupportInUnit.{u, v} A T)
      X.obj.as (CochainComplex.isKInjective_of_injective _ n)

/-- The restriction of the unbounded derived functor to bounded-below objects is a right derived
functor of sections with support, relative to the quasi-isomorphisms of `K⁺(A)`. -/
private instance isRightDerivedFunctor_unboundedUnit :
    (DerivedCategory.Plus.ι ⋙ derivedSectionsWithSupportIn.{u, v} A T).IsRightDerivedFunctor
      (unboundedUnit.{u, v} A T)
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} A)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (plusSectionsToUnbounded.{u, v} A T)).isRightDerivedFunctor_of_isIso _
    fun _ ↦ isIso_unboundedUnit_app_of_injective A T _

/-- The bounded-below derived functor, pushed into the unbounded derived category, is a right
derived functor of the same functor. -/
private instance isRightDerivedFunctor_plusUnit :
    (derivedSectionsWithSupportInPlus.{u, v} A T ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (plusUnit.{u, v} A T)
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} A)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (plusSectionsToUnbounded.{u, v} A T)).isRightDerivedFunctor_of_isIso _
    fun _ ↦ by dsimp [plusUnit]; infer_instance

/-- The bounded-below and unbounded right derived functors of sections with support in `T` agree
after including bounded-below complexes in the unbounded derived category. -/
@[stacks 0EF4 "cohomology_calculation", sga "4 XVII 1.2.4" "special case"]
theorem nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso :
    Nonempty
      (derivedSectionsWithSupportInPlus.{u, v} A T ⋙ DerivedCategory.Plus.ι ≅
        DerivedCategory.Plus.ι ⋙ derivedSectionsWithSupportIn.{u, v} A T) :=
  ⟨Functor.rightDerivedUnique _ _ (plusUnit.{u, v} A T) (unboundedUnit.{u, v} A T)
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} A))⟩

add_to_stacks 0EF4 "cohomology_calculation"
  colimitClosedSupportComparison_isIso

end Stacks.LocalCohomology
