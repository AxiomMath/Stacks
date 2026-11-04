module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.GeneralSupports.SupportedDerivedCategory
public import StacksFrontier.Algebra.Module.Matlis.DerivedPlusComparison
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedModulesComparison

/-!
# The bounded-below part of the comparison for modules supported in a subset

Let `A` be a commutative ring and `T ⊆ Spec(A)` a subset. The comparison functor
$$ D(\mathrm{Mod}_{A,T}) \longrightarrow D_T(A) $$
induced by the inclusion of the Serre subcategory of modules supported in `T` (Tag 0EEZ) restricts
to bounded-below objects, giving
$$ D^{+}(\mathrm{Mod}_{A,T}) \longrightarrow D^{+}_T(A), $$
and this restriction is an equivalence when `A` is Noetherian and `T` is stable under
specialization.

## Main definitions

* `Stacks.LocalCohomology.supportedModulesComparisonPlus` — the comparison functor
  `D^+(Mod_{A,T}) ⥤ D^+_T(A)`, defined as the canonical lift of
  `DerivedCategory.Plus.ι ⋙ (supportModuleProperty A T).ι.mapDerivedCategory`.

## Main results

* `Stacks.LocalCohomology.supportedModulesComparisonPlus_isEquivalence` — the bounded-below
  comparison functor is an equivalence for a Noetherian ring and a specialization-stable subset.

## References

* [Stacks Project, Tag 0EF2](https://stacks.math.columbia.edu/tag/0EF2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-- The inclusion of the modules supported in `T` carries a bounded-below object of
`D(Mod_{A,T})` to a bounded-below object of `D(A)`. -/
theorem isBoundedBelow_mapDerivedCategory_obj
    (X : DerivedCategory (ModulesSupportedIn.{u, v} A T))
    (hX : DerivedCategoryB.IsBoundedBelow X) :
    DerivedCategoryB.IsBoundedBelow
      ((supportModuleProperty A T).ι.mapDerivedCategory.obj X) := by
  obtain ⟨n₀, hn₀⟩ := hX
  exact ⟨n₀, fun n hn => ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (supportModuleProperty A T).ι n).app X).isZero_iff.mpr
      ((supportModuleProperty A T).ι.map_isZero (hn₀ n hn))⟩

/-- The image in `D(A)` of a bounded-below object of `D(Mod_{A,T})` lies in `D^+_T(A)`. -/
theorem derivedCategoryBPlus_mapDerivedCategory_obj
    (X : DerivedCategory.Plus (ModulesSupportedIn.{u, v} A T)) :
    DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty A T)
      ((supportModuleProperty A T).ι.mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj X)) := by
  obtain ⟨n₀, hn₀⟩ := X.2
  refine ⟨isBoundedBelow_mapDerivedCategory_obj A T _
    ⟨n₀, fun n hn => (DerivedCategory.isGE_iff _ n₀).1 hn₀ n hn⟩, fun i => ?_⟩
  exact (supportModuleProperty A T).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (supportModuleProperty A T).ι i).app (DerivedCategory.Plus.ι.obj X)).symm
    ((supportModuleProperty A T).prop_ι_obj
      ((homologyFunctor (ModulesSupportedIn.{u, v} A T) i).obj
        (DerivedCategory.Plus.ι.obj X)))

/-- The canonical functor from the bounded-below derived category of modules supported in `T` to
the bounded-below part of `D(A)` with cohomology supported in `T`. -/
def supportedModulesComparisonPlus :
    DerivedCategory.Plus (ModulesSupportedIn.{u, v} A T) ⥤
      (DerivedCategoryB.derivedCategoryBPlus
        (supportModuleProperty.{u, v} A T)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBPlus
      (supportModuleProperty.{u, v} A T)).lift
    (DerivedCategory.Plus.ι ⋙ (supportModuleProperty A T).ι.mapDerivedCategory)
    (derivedCategoryBPlus_mapDerivedCategory_obj.{u, v} A T)

/-- **Stacks Project, Tag 0EF2.** For a Noetherian ring `A` and a subset `T` of its spectrum
stable under specialization, the canonical comparison functor
`D^+(Mod_{A,T}) ⥤ D^+_T(A)` is an equivalence. -/
theorem supportedModulesComparisonPlus_isEquivalence [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) :
    (supportedModulesComparisonPlus.{u, v} A T).IsEquivalence := by
  obtain ⟨e, ⟨he⟩⟩ :=
    Module.exists_supportedModulesDerivedPlusEquivalence.{u, v} A T hT
  have hiso : e.functor ≅ supportedModulesComparisonPlus.{u, v} A T :=
    Functor.fullyFaithfulCancelRight
      (DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty.{u, v} A T)).ι
      (he ≪≫ ((DerivedCategoryB.derivedCategoryBPlus
        (supportModuleProperty.{u, v} A T)).liftCompιIso _
          (derivedCategoryBPlus_mapDerivedCategory_obj.{u, v} A T)).symm)
  exact Functor.isEquivalence_of_iso hiso

/-- `D^+_T(A)` is a subcategory of `D_T(A)`. -/
theorem derivedCategoryBPlus_le_derivedCategoryB :
    DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty.{u, v} A T) ≤
      DerivedCategoryB.derivedCategoryB (supportModuleProperty.{u, v} A T) :=
  fun _ hX => hX.2

/-- The bounded-below comparison functor is the restriction of the unbounded comparison functor
`supportedModulesComparison` along the inclusion `D^+(Mod_{A,T}) ⥤ D(Mod_{A,T})`. -/
def supportedModulesComparisonPlusCompIsoRestriction :
    supportedModulesComparisonPlus.{u, v} A T ⋙
        ObjectProperty.ιOfLE (derivedCategoryBPlus_le_derivedCategoryB.{u, v} A T) ≅
      DerivedCategory.Plus.ι ⋙ supportedModulesComparison.{u, v} A T :=
  (DerivedCategoryB.derivedCategoryBPlus (supportModuleProperty.{u, v} A T)).liftCompιOfLEIso
    (DerivedCategory.Plus.ι ⋙ (supportModuleProperty A T).ι.mapDerivedCategory)
    (derivedCategoryBPlus_mapDerivedCategory_obj.{u, v} A T)
    (derivedCategoryBPlus_le_derivedCategoryB.{u, v} A T)

end Stacks.LocalCohomology
