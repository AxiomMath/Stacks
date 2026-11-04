module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointDerivedTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductTensorConstraints
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.UnitalComparisonKFlatDescent

/-!
# The unit of the one-point comparison, and unitality on K-flat representatives

Let `R` be a commutative ring, `({*}, R)` the one-point ringed space and `A = Γ({*}, 𝒪)`.  The
one-point comparison `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointComparisonWithTensor`
carries the comparison of derived tensor products
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparison`.  Its global cup product is
unital in the sense of `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison.IsUnitalWith`
for the isomorphism `u : E(A[0]) ≅ 𝒪[0]` given by the counit of the one-point identification at
the structure sheaf, provided the oplax right unit law and the oplax commutativity law hold at
K-flat representatives.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointUnitSheafIso`: `E(A) ≅ 𝒪`, the counit of
  the one-point identification at the structure sheaf.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedUnitIso`: `E(A[0]) ≅ 𝒪[0]` in
  `D(𝒪_{({*}, R)})`, with underlying morphism `onePointUnitMap`.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.ModelRightUnitLaw`,
  `Stacks.Cohomology.DerivedSectionsOnAPoint.ModelBraidingLaw`: the oplax right unit law and the
  oplax commutativity law at K-flat representatives.

## Main results

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparison_app_of_kFlat`: the
  comparison at a pair of K-flat representatives is `modelComparison`, the K-flat comparisons of
  Tags 064M and 06YU joined by the comparison of total tensor complexes.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.isUnitalWith_onePointUnitMap_of_model`: the
  one-point comparison is unital with `onePointUnitMap`, given the two laws at K-flat
  representatives.
* `globalCupProduct_onePointComparisonWithTensor_ne_zero_of_model`: for a nontrivial ring, the
  global cup product of the one-point comparison is then nonzero.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open CochainComplex.KFlatBifunctor
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-! ### The unit `u : E(A[0]) ⟶ 𝒪[0]` -/

/-- **The one-point identification carries `A` to the structure sheaf**: `E(A) ≅ 𝒪`, the counit
of the identification at the structure sheaf. -/
def onePointUnitSheafIso :
    (onePointSectionsEquivalence R).functor.obj
        (ModuleCat.of ↥(baseRing (onePointRingedSpace R)) ↥(baseRing (onePointRingedSpace R))) ≅
      SheafOfModules.unit (structureSheafRing (onePointRingedSpace R)) :=
  (onePointSectionsEquivalence R).counitIso.app
    (SheafOfModules.unit (structureSheafRing (onePointRingedSpace R)))

/-- **The unit of the one-point comparison**, `E(A[0]) ≅ 𝒪[0]` in `D(𝒪_{({*}, R)})`: the
identification `E(A) ≅ 𝒪` of `onePointUnitSheafIso`, placed in degree zero. -/
def onePointDerivedUnitIso :
    (onePointComparisonWithTensor R).pullback.obj (unitBase (onePointRingedSpace R)) ≅
      unitSheaf (onePointRingedSpace R) :=
  ((onePointSectionsEquivalence R).functor.mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of ↥(baseRing (onePointRingedSpace R))
        ↥(baseRing (onePointRingedSpace R))) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (onePointUnitSheafIso R)

/-- **The unit morphism `u : E(A[0]) ⟶ 𝒪[0]` of the one-point comparison**: the morphism
underlying `onePointDerivedUnitIso`. -/
abbrev onePointUnitMap :
    (onePointComparisonWithTensor R).pullback.obj (unitBase (onePointRingedSpace R)) ⟶
      unitSheaf (onePointRingedSpace R) :=
  (onePointDerivedUnitIso R).hom

/-! ### The comparison at a pair of K-flat representatives -/

attribute [local instance] kFlatQModulesPair_isLocalization

/-- The component of `modelsComparison` at a pair of K-flat objects of the homotopy category. -/
theorem modelsComparison_hom_app
    (M : (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory ×
      (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory) :
    (modelsComparison R).hom.app M =
      (sectionsOfDerivedTensor R).map (kFlatQModulesPairIso R M).hom ≫
        (modelComparison R M.1.obj.as M.2.obj.as M.1.property M.2.property).hom ≫
          ((derivedTensorOfSections R).mapIso (kFlatQModulesPairIso R M)).inv :=
  rfl

/-- The descended comparison at an object of the full subcategory of K-flat objects of the
homotopy category is `modelsComparison`. -/
theorem onePointDerivedTensorIso_hom_app_kFlatQ
    (M : (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory ×
      (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory) :
    (onePointDerivedTensorIso R).hom.app ((kFlatQModulesPair R).obj M) =
      (modelsComparison R).hom.app M := by
  dsimp only [onePointDerivedTensorIso, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp

/-- If the component of `α` at `Z` is the conjugate of `m` by an isomorphism `e : Z ≅ Z'`, then
the component of `α` at `Z'` is `m`. -/
private lemma app_eq_of_conjugate {C E : Type*} [Category C] [Category E] {A B : C ⥤ E}
    (α : A ⟶ B) {Z Z' : C} (e : Z ≅ Z') (m : A.obj Z' ⟶ B.obj Z')
    (h : α.app Z = A.map e.hom ≫ m ≫ B.map e.inv) : α.app Z' = m := by
  have hnat := α.naturality e.hom
  rw [h] at hnat
  refine (cancel_epi (A.map e.hom)).1 (hnat.trans ?_)
  simp

/-- **The comparison `E(x ⊗^𝐋_A y) ⟶ E x ⊗^𝐋_{𝒪} E y` at a pair of K-flat representatives is
`modelComparison`**: the K-flat comparison of Tag 064M carried over by `E`, the comparison of
total tensor complexes, and the inverse K-flat comparison of Tag 06YU. -/
theorem onePointTensorComparison_app_of_kFlat
    (K L : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (hL : CochainComplex.KFlat.{u, u} L) :
    (onePointTensorComparison R).app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (modelComparison R K L hK hL).hom :=
  app_eq_of_conjugate (onePointDerivedTensorIso R).hom
    (kFlatQModulesPairIso R (⟨(HomotopyCategory.quotient _ _).obj K, hK⟩,
      ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩))
    (modelComparison R K L hK hL).hom
    ((onePointDerivedTensorIso_hom_app_kFlatQ R _).trans (modelsComparison_hom_app R _))

/-- The unit `onePointUnitMap` of the one-point comparison is an isomorphism. -/
instance isIso_onePointUnitMap : IsIso (onePointUnitMap R) :=
  inferInstanceAs (IsIso (onePointDerivedUnitIso R).hom)

/-- **The unit of `⊗^𝐋_A` is the image of the monoidal unit of `CochainComplex (Mod A) ℤ`**,
by definition. -/
theorem unitBase_eq_q_tensorUnit :
    unitBase (onePointRingedSpace R) =
      DerivedCategory.Q.obj (𝟙_ (CochainComplex (onePointModuleCat R) ℤ)) :=
  rfl

/-- **The comparison at `(QK, A[0])` for K-flat `K` is `modelComparison` at `(K, 𝟙_)`.** -/
theorem onePointTensorComparison_app_unit_of_kFlat
    (K : CochainComplex (onePointModuleCat R) ℤ) (hK : CochainComplex.KFlat.{u, u} K) :
    (onePointTensorComparison R).app
        (DerivedCategory.Q.obj K, unitBase (onePointRingedSpace R)) =
      (modelComparison R K (𝟙_ (CochainComplex (onePointModuleCat R) ℤ)) hK
        (CochainComplex.KFlatMonoidal.kFlat_tensorUnit (onePointModuleCat R))).hom :=
  onePointTensorComparison_app_of_kFlat R K _ hK _

/-! ### Unitality of the one-point comparison, given the two laws at K-flat representatives -/

/-- **The oplax right unit law of the one-point comparison, read at a K-flat representative**:
for every K-flat complex `K`, `modelComparison` at `(K, 𝟙_)` followed by `u` and the right unitor
of the sheaf-side derived tensor product is `E` of the right unitor of `⊗^𝐋_A` at `QK`. -/
def ModelRightUnitLaw : Prop :=
  ∀ (K : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (MonoidalCategory.curriedTensor (onePointModuleCat R)) K),
    (modelComparison R K (𝟙_ (CochainComplex (onePointModuleCat R) ℤ)) hK
          (CochainComplex.KFlatMonoidal.kFlat_tensorUnit (onePointModuleCat R))).hom ≫
        ((derivedTensorProductFunctor (onePointRingedSpace R).sheaf).obj
          ((onePointComparisonWithTensor R).pullback.obj
            (DerivedCategory.Q.obj K))).map (onePointUnitMap R) ≫
          (sheafRightUnitor (onePointRingedSpace R)
            ((onePointComparisonWithTensor R).pullback.obj
              (DerivedCategory.Q.obj K))).hom =
      (onePointComparisonWithTensor R).pullback.map
        (baseRightUnitor (onePointRingedSpace R) (DerivedCategory.Q.obj K)).hom

/-- **The oplax commutativity law of the one-point comparison, read at a pair of K-flat
representatives**: for K-flat complexes `K` and `L`, `modelComparison` at `(K, L)` followed by the
symmetry of the sheaf-side derived tensor product is `E` of the symmetry of `⊗^𝐋_A` followed by
`modelComparison` at `(L, K)`. -/
def ModelBraidingLaw : Prop :=
  ∀ (K L : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (MonoidalCategory.curriedTensor (onePointModuleCat R)) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (MonoidalCategory.curriedTensor (onePointModuleCat R)) L),
    (modelComparison R K L hK hL).hom ≫
        (sheafComm (onePointRingedSpace R)
          ((onePointComparisonWithTensor R).pullback.obj (DerivedCategory.Q.obj K))
          ((onePointComparisonWithTensor R).pullback.obj
            (DerivedCategory.Q.obj L))).hom =
      (onePointComparisonWithTensor R).pullback.map
          (baseComm (onePointRingedSpace R) (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj L)).hom ≫
        (modelComparison R L K hL hK).hom

/-- **The one-point comparison is unital with `onePointUnitMap`, given the oplax right unit law
`ModelRightUnitLaw` and the oplax commutativity law `ModelBraidingLaw` at K-flat
representatives.** -/
theorem isUnitalWith_onePointUnitMap_of_model
    (hr : ModelRightUnitLaw R) (hb : ModelBraidingLaw R) :
    (onePointComparisonWithTensor R).IsUnitalWith (onePointUnitMap R) :=
  OnePointComparison.isUnitalWith_of_kFlat _ _
    (fun K hK =>
      (congrArg (fun m => m ≫
            ((derivedTensorProductFunctor (onePointRingedSpace R).sheaf).obj
              ((onePointComparisonWithTensor R).pullback.obj
                (DerivedCategory.Q.obj K))).map (onePointUnitMap R) ≫
              (sheafRightUnitor (onePointRingedSpace R)
                ((onePointComparisonWithTensor R).pullback.obj
                  (DerivedCategory.Q.obj K))).hom)
          (onePointTensorComparison_app_unit_of_kFlat R K hK)).trans (hr K hK))
    (fun K L hK hL =>
      ((congrArg (fun m => m ≫
            (sheafComm (onePointRingedSpace R)
              ((onePointComparisonWithTensor R).pullback.obj (DerivedCategory.Q.obj K))
              ((onePointComparisonWithTensor R).pullback.obj
                (DerivedCategory.Q.obj L))).hom)
          (onePointTensorComparison_app_of_kFlat R K L hK hL)).trans
        ((hb K L hK hL).trans
          (congrArg (fun m => (onePointComparisonWithTensor R).pullback.map
                (baseComm (onePointRingedSpace R) (DerivedCategory.Q.obj K)
                  (DerivedCategory.Q.obj L)).hom ≫ m)
            (onePointTensorComparison_app_of_kFlat R L K hL hK).symm))))

/-- **The global cup product of the one-point comparison with a genuine tensor comparison is a
unital global cup product, given the two laws at K-flat representatives.** -/
theorem isGlobalCupProduct_globalCupProduct_onePointComparisonWithTensor_of_model
    (hr : ModelRightUnitLaw R) (hb : ModelBraidingLaw R) :
    IsGlobalCupProduct (globalCupProduct (onePointComparisonWithTensor R)) :=
  isGlobalCupProduct_of_isUnitalWith (isUnitalWith_onePointUnitMap_of_model R hr hb)

/-- **The global cup product of the one-point comparison with a genuine tensor comparison is
nonzero**, for a nontrivial ring, given the two laws at K-flat representatives. -/
theorem globalCupProduct_onePointComparisonWithTensor_ne_zero_of_model [Nontrivial R]
    (hr : ModelRightUnitLaw R) (hb : ModelBraidingLaw R) :
    globalCupProduct (onePointComparisonWithTensor R) ≠ 0 := by
  obtain ⟨U, hU⟩ := not_forall.1 (not_forall_isZero_baseSections R)
  exact globalCupProduct_ne_zero_of_isUnitalWith
    (isUnitalWith_onePointUnitMap_of_model R hr hb) hU

end Stacks.Cohomology.DerivedSectionsOnAPoint

end
