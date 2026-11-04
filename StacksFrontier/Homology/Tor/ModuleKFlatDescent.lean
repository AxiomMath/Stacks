module

public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import Mathlib.CategoryTheory.Localization.Prod
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# Descending an equality of transformations on `D(R)` to K-flat complexes

Let `R` be a commutative ring.  By Stacks 06Y4 every complex of `R`-modules receives a
quasi-isomorphism from a K-flat one
(`CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions`), so `D(R)` is the
localization of the K-flat objects of the homotopy category at the quasi-isomorphisms
(`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions`), and a product of
two copies of that localization is a localization of pairs.  A natural transformation between
functors on `D(R)`, or on `D(R) × D(R)`, is therefore determined by its components at K-flat
complexes.

This is the module-side counterpart of
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`, which says the same thing for
complexes of `𝒪_Y`-modules on a ringed space.

## Main results

* `CochainComplex.DerivedTensor.OneSided.natTrans_ext_of_kFlat`: two natural transformations
  between functors on `D(R)` which agree at `QK` for every K-flat cochain complex `K` are equal.
* `CochainComplex.DerivedTensor.OneSided.natTrans_ext_of_kFlatPair`: the same on
  `D(R) × D(R)`, at pairs of K-flat complexes.

## References

* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor
open scoped CategoryTheory.Prod

universe v w u

namespace CochainComplex.DerivedTensor.OneSided

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The K-flat objects of `K(Mod R)`, viewed in `D(R)`. -/
abbrev kFlatQModules := kFlatQ (curriedTensor (ModuleCat.{u} R))

/-- The quasi-isomorphisms between K-flat objects of `K(Mod R)`. -/
abbrev kFlatQuasiIsoModules := kFlatQuasiIso (curriedTensor (ModuleCat.{u} R))

/-- Pairs of K-flat objects of `K(Mod R)`, viewed in `D(R) × D(R)`. -/
abbrev kFlatQModulesPair := (kFlatQModules R).prod (kFlatQModules R)

/-- The quasi-isomorphisms between pairs of K-flat objects of `K(Mod R)`. -/
abbrev kFlatQuasiIsoModulesPair := (kFlatQuasiIsoModules R).prod (kFlatQuasiIsoModules R)

/-- The image in `D(R)` of a K-flat object of the homotopy category is the image of the underlying
complex. -/
def kFlatQModulesIso
    (M : (kFlatObjects (curriedTensor (ModuleCat.{u} R))).FullSubcategory) :
    (kFlatQModules R).obj M ≅ DerivedCategory.Q.obj M.obj.as :=
  (DerivedCategory.quotientCompQhIso _).app M.obj.as

/-- The image in `D(R) × D(R)` of a pair of K-flat objects of the homotopy category is the pair of
images of the underlying complexes. -/
def kFlatQModulesPairIso
    (M : (kFlatObjects (curriedTensor (ModuleCat.{u} R))).FullSubcategory ×
      (kFlatObjects (curriedTensor (ModuleCat.{u} R))).FullSubcategory) :
    (kFlatQModulesPair R).obj M ≅
      (DerivedCategory.Q.obj M.1.obj.as, DerivedCategory.Q.obj M.2.obj.as) :=
  (kFlatQModulesIso R M.1).prod (kFlatQModulesIso R M.2)

/-- **`D(R) × D(R)` is the localization of the pairs of K-flat objects at the
quasi-isomorphisms.** -/
theorem kFlatQModulesPair_isLocalization :
    (kFlatQModulesPair R).IsLocalization (kFlatQuasiIsoModulesPair R) := by
  have : (kFlatQuasiIsoModules R).ContainsIdentities := by infer_instance
  exact Functor.IsLocalization.prod (kFlatQModules R) _ (kFlatQModules R) _

/-- **An equality of natural transformations on `D(R)` may be checked on K-flat complexes.**
Two natural transformations between functors on `D(R)` whose components at `QK` agree for every
K-flat cochain complex `K` of `R`-modules are equal. -/
theorem natTrans_ext_of_kFlat {E : Type*} [Category E]
    {A B : DerivedCategory (ModuleCat.{u} R) ⥤ E} (α β : A ⟶ B)
    (h : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (ModuleCat.{u} R)) K →
      α.app (DerivedCategory.Q.obj K) = β.app (DerivedCategory.Q.obj K)) :
    α = β :=
  Localization.natTrans_ext (kFlatQModules R) (kFlatQuasiIsoModules R)
    (fun M => CategoryTheory.NatTrans.app_eq_of_iso α β (kFlatQModulesIso R M)
      (h M.obj.as M.property))

/-- **An equality of natural transformations on `D(R) × D(R)` may be checked on pairs of K-flat
complexes.**  The two-variable form of
`CochainComplex.DerivedTensor.OneSided.natTrans_ext_of_kFlat`. -/
theorem natTrans_ext_of_kFlatPair {E : Type*} [Category E]
    {A B : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤ E}
    (α β : A ⟶ B)
    (h : ∀ K L : CochainComplex (ModuleCat.{u} R) ℤ,
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (ModuleCat.{u} R)) K →
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (ModuleCat.{u} R)) L →
      α.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
        β.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) :
    α = β :=
  have := kFlatQModulesPair_isLocalization R
  Localization.natTrans_ext (kFlatQModulesPair R) (kFlatQuasiIsoModulesPair R)
    (fun M => CategoryTheory.NatTrans.app_eq_of_iso α β (kFlatQModulesPairIso R M)
      (h M.1.obj.as M.2.obj.as M.1.property M.2.property))

end CochainComplex.DerivedTensor.OneSided

end
