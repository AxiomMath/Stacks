module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RestrictOpen

/-!
# Restriction to an open subscheme on the bounded coherent derived category

Let `X` be a locally Noetherian scheme and `U ⊆ X` an open subscheme. Restriction of modules
along `U.ι` is exact, so it induces a functor `D(𝒪_X) ⥤ D(𝒪_U)`, and that functor carries
`D^b_Coh(𝒪_X)` into `D^b_Coh(𝒪_U)`.

## Main definitions

* `AlgebraicGeometry.coherentDerivedBoundedRestrict` is the restriction functor
  `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_U)`.

## Main results

* `AlgebraicGeometry.derivedCategoryBBounded_coherentInModules_modulesRestrict`: the restriction
  of a bounded complex with coherent cohomology is again bounded with coherent cohomology.

## References

* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)

/-- **The restriction of a bounded complex with coherent cohomology to an open subscheme is
again bounded with coherent cohomology.** -/
theorem derivedCategoryBBounded_coherentInModules_modulesRestrict
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : DerivedCategoryB.derivedCategoryBBounded (coherentInModules X) E) :
    DerivedCategoryB.derivedCategoryBBounded (coherentInModules U.toScheme)
      ((Stacks.DerivedQCoh.modulesRestrict U).mapDerivedCategory.obj E) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hE
  have e := fun i => ((Stacks.DerivedQCoh.modulesRestrict U).mapDerivedCategoryHomologyIso i).app E
  refine ⟨⟨⟨a, fun i hi => ?_⟩, ⟨b, fun i hi => ?_⟩⟩, fun i => ?_⟩
  · exact ((Stacks.DerivedQCoh.modulesRestrict U).map_isZero (ha i hi)).of_iso (e i)
  · exact ((Stacks.DerivedQCoh.modulesRestrict U).map_isZero (hb i hi)).of_iso (e i)
  · let : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsCoherent := hc i
    exact (coherentInModules U.toScheme).prop_of_iso (e i).symm
      (Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion U.ι _)

/-- **Restriction to an open subscheme as a functor `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_U)`**, obtained
by corestricting the functor induced on unbounded derived categories by the exact restriction
of modules. -/
def coherentDerivedBoundedRestrict :
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules U.toScheme)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBBounded (coherentInModules U.toScheme)).lift
    ((DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι ⋙
      (Stacks.DerivedQCoh.modulesRestrict U).mapDerivedCategory)
    fun E => derivedCategoryBBounded_coherentInModules_modulesRestrict U E.obj E.property

/-- Forgetting the boundedness and coherence conditions on the target of
`AlgebraicGeometry.coherentDerivedBoundedRestrict` returns the inclusion of `D^b_Coh(𝒪_X)` into
`D(𝒪_X)` followed by restriction of unbounded derived modules. -/
theorem coherentDerivedBoundedRestrict_comp_ι :
    coherentDerivedBoundedRestrict U ⋙
        (DerivedCategoryB.derivedCategoryBBounded (coherentInModules U.toScheme)).ι =
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι ⋙
        (Stacks.DerivedQCoh.modulesRestrict U).mapDerivedCategory := rfl

end AlgebraicGeometry

end
