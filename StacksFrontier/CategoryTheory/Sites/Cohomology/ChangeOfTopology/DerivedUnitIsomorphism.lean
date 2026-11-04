module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparingCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# The derived change-of-topology unit is an isomorphism

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in the situation of
Stacks 0EZ3, let `X` be an object of `C` and write `ε_X : C_τ/X ⟶ C_τ'/X` for the
change-of-topology morphism. Assume the vanishing condition `(V_n)` of that situation for
**every** `n`.

Then, for an object `K'` of `D⁺_{𝒜'_X}(C_{τ'}/X)` — a bounded below object of the derived
category of abelian sheaves on the coarser localized site all of whose cohomology sheaves lie in
the weak Serre class `𝒜'_X` — the canonical map

`K' ⟶ Rε_{X,*}(ε_X^{-1} K')`

of `Stacks.ComparingTopologies.derivedComparisonUnit` is an isomorphism. This is clause (1) of
Stacks 0EZF.

## Main results

* `CategoryTheory.Functor.isGE_mapDerivedCategoryPlus_obj_of_exactFunctor`: an exact functor
  keeps an object of `D^{≥a}` in `D^{≥a}`.
* `CategoryTheory.NatTrans.isIso_app_of_isGE_plus`: a shift-compatible transformation `𝟭 ⟶ F` of
  triangulated endofunctors of `D⁺(A)` preserving `D^{≥m}` is invertible at every object whose
  cohomology lies in a class at which it is invertible in degree zero.
* `Stacks.ComparingTopologies.isTriangulated_abelianComparisonPullback_mapDerivedCategoryPlus`:
  the action of `ε_X^{-1}` on bounded below derived categories is triangulated.
* `Stacks.ComparingTopologies.isGE_derivedComparisonUnitTarget_obj`: the functor
  `K' ↦ Rε_{X,*}(ε_X^{-1}K')` keeps an object of `D^{≥a}` in `D^{≥a}`.
* `Stacks.ComparingTopologies.isIso_derivedComparisonUnit_app_single`: the derived unit is
  invertible at a sheaf of `𝒜'_X` placed in degree zero.
* `Stacks.ComparingTopologies.isIso_derivedComparisonUnit_app_of_vanishingCondition`: the derived
  unit is invertible at every object of `D⁺_{𝒜'_X}(C_{τ'}/X)`.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0EZB](https://stacks.math.columbia.edu/tag/0EZB)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public noncomputable section

universe u₁ v₁ u₂ v₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]

/-- An exact functor keeps an object of `D^{≥a}` in `D^{≥a}`, on bounded below derived
categories. -/
theorem isGE_mapDerivedCategoryPlus_obj_of_exactFunctor (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory.Plus A) (a : ℤ) [K.IsGE a] :
    (F.mapDerivedCategoryPlus.obj K).IsGE a := by
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  show (F.mapDerivedCategory.obj K.obj).IsGE a
  have hK : K.obj.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).2 inferInstance
  obtain ⟨M, hM, ⟨e⟩⟩ := K.obj.exists_iso_Q_obj_of_isGE a
  have := hM
  have hQ : ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).obj M).IsGE a := by
    dsimp only [Functor.comp_obj]
    infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app M).symm a

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
  {F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus A} [F.CommShift ℤ] [F.IsTriangulated]
  (α : 𝟭 (DerivedCategory.Plus A) ⟶ F) [NatTrans.CommShift α ℤ]

/-- The objects of `D⁺(A)` at which `α` is invertible. -/
private abbrev plusIsoLocus : ObjectProperty (DerivedCategory.Plus A) :=
  fun K ↦ IsIso (α.app K)

private instance plusIsoLocus_isClosedUnderIsomorphisms :
    (plusIsoLocus α).IsClosedUnderIsomorphisms :=
  Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms α

private instance plusIsoLocus_isTriangulated : (plusIsoLocus α).IsTriangulated :=
  Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated _ _ α

/-- Let `α : 𝟭 ⟶ F` be a shift-compatible natural transformation from the
identity to a triangulated endofunctor of `D⁺(A)` which carries `D^{≥m}` into `D^{≥m}`, let `P`
be an isomorphism-closed class of objects of `A` containing a zero object at which `α` is
invertible on single objects in degree zero, and let `K` be an object of `D⁺(A)` all of whose
cohomology lies in `P`. Then `α` is invertible at `K`. -/
theorem isIso_app_of_isGE_plus
    (hF : ∀ (L : DerivedCategory.Plus A) (m : ℤ), L.IsGE m → (F.obj L).IsGE m)
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hsingle : ∀ M : A, P M → IsIso (α.app ((DerivedCategory.Plus.singleFunctor A 0).obj M)))
    (K : DerivedCategory.Plus A)
    (hK : ∀ i : ℤ, P ((DerivedCategory.Plus.homologyFunctor A i).obj K)) :
    IsIso (α.app K) := by
  obtain ⟨a, ha⟩ := K.property
  have hGE : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).1 ha
  have := hGE
  rw [DerivedCategory.Plus.isIso_iff]
  intro q
  by_cases haq : a ≤ q
  · have hT := DerivedCategory.Plus.TStructure.t.triangleLEGT_distinguished q K
    have hn : a + ((q - a).toNat : ℤ) = q := by omega
    have hcut : IsIso (α.app ((DerivedCategory.Plus.TStructure.t.truncLE q).obj K)) := by
      refine DerivedCategory.Plus.prop_of_isGE_of_isLE (plusIsoLocus α) a (q - a).toNat _
        inferInstance ?_ fun p _ _ ↦ ?_
      · rw [hn]
        infer_instance
      · exact hsingle _
          (DerivedCategory.Plus.prop_homology_truncLE_obj P K q (fun j _ ↦ hK j) p)
    have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor A q).map
        ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K)) :=
      DerivedCategory.Plus.isIso_homologyMap_truncLEι_app K q q le_rfl
    have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor A q).map
        (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K))) :=
      DerivedCategory.Plus.isIso_homologyMap_mor₁_of_isGE₃
        (F.mapTriangle.obj ((DerivedCategory.Plus.TStructure.t.triangleLEGT q).obj K))
        (F.map_distinguished _ hT) q (q + 1)
        (hF ((DerivedCategory.Plus.TStructure.t.truncGT q).obj K) (q + 1) inferInstance)
        (by omega)
    have hcomm : (DerivedCategory.Plus.homologyFunctor A q).map
          ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K) ≫
        (DerivedCategory.Plus.homologyFunctor A q).map (α.app K) =
      (DerivedCategory.Plus.homologyFunctor A q).map
          (α.app ((DerivedCategory.Plus.TStructure.t.truncLE q).obj K)) ≫
        (DerivedCategory.Plus.homologyFunctor A q).map
          (F.map ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K)) := by
      simpa only [Functor.map_comp, Functor.id_map, Functor.id_obj] using
        congrArg (DerivedCategory.Plus.homologyFunctor A q).map
          (α.naturality ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K))
    have hfac : IsIso ((DerivedCategory.Plus.homologyFunctor A q).map
          ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K) ≫
        (DerivedCategory.Plus.homologyFunctor A q).map (α.app K)) := by
      rw [hcomm]
      infer_instance
    exact IsIso.of_isIso_comp_left ((DerivedCategory.Plus.homologyFunctor A q).map
      ((DerivedCategory.Plus.TStructure.t.truncLEι q).app K))
      ((DerivedCategory.Plus.homologyFunctor A q).map (α.app K))
  · have hFK := hF K a hGE
    exact IsZero.isIso (DerivedCategory.Plus.isZero_homology_of_isGE K a q (by omega))
      (DerivedCategory.Plus.isZero_homology_of_isGE (F.obj K) a q (by omega)) _

end CategoryTheory.NatTrans

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus
attribute [local instance] commShiftMapDerivedCategoryPlus
attribute [local instance] commShiftMapDerivedCategoryPlusFactorsh

/-- The action of `ε_X^{-1}` on bounded below derived categories is triangulated. -/
theorem isTriangulated_abelianComparisonPullback_mapDerivedCategoryPlus
    (S : CohomologyComparison C) (X : C) :
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapDerivedCategoryPlus.IsTriangulated := by
  have hhomotopy : (abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapHomotopyCategoryPlus.IsTriangulated := inferInstance
  have hcomp : ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsTriangulated :=
    Functor.IsTriangulated.instComp _ _
  exact Functor.isTriangulated_of_precomp_iso (abelianComparisonPullback S.fineCoverage
    S.coarseCoverage X).mapDerivedCategoryPlusFactorsh

/-- The functor `K' ↦ Rε_{X,*}(ε_X^{-1}K')` keeps an object of `D^{≥a}` in `D^{≥a}`. -/
theorem isGE_derivedComparisonUnitTarget_obj (S : CohomologyComparison C) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X)) (a : ℤ)
    (hGE : K.IsGE a) :
    (((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus ⋙
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerivedFunctorPlus).obj K).IsGE a := by
  have := hGE
  have hpull := Functor.isGE_mapDerivedCategoryPlus_obj_of_exactFunctor
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage X) K a
  exact Functor.isGE_rightDerivedFunctorPlus_obj _ _ a

/-- Assume the vanishing condition `(V_n)` for every `n`. The derived change-of-topology unit
is invertible at a sheaf of `𝒜'_X` placed in degree zero. -/
theorem isIso_derivedComparisonUnit_app_single (S : CohomologyComparison C)
    (hV : ∀ n : ℕ, S.vanishingCondition n) (X : C)
    (M : AbelianSheaves S.coarseCoverage.toGrothendieck X) (hM : S.weakSerre X M) :
    IsIso ((derivedComparisonUnit S X).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) :=
  (DerivedCategory.Plus.isIso_iff _).2 fun i ↦
    isIso_homology_derivedComparisonUnit_single S i.toNat (hV i.toNat) X M hM i
      (Int.self_le_toNat i)

/-- In the comparison situation of Stacks 0EZ3, assume the
vanishing condition `(V_n)` for every `n`. Let `X` be an object of `C` and let `K'` be a bounded
below object of the derived category of abelian sheaves on `C_{τ'}/X` all of whose cohomology
sheaves lie in the weak Serre class `𝒜'_X`, that is, an object of `D⁺_{𝒜'_X}(C_{τ'}/X)`. Then the
canonical map

`K' ⟶ Rε_{X,*}(ε_X^{-1}K')`

of `Stacks.ComparingTopologies.derivedComparisonUnit` is an isomorphism. This is clause (1) of
Stacks 0EZF. -/
theorem isIso_derivedComparisonUnit_app_of_vanishingCondition (S : CohomologyComparison C)
    (hV : ∀ n : ℕ, S.vanishingCondition n) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso ((derivedComparisonUnit S X).app K) := by
  have hwsc : (S.weakSerre X).IsWeakSerreClass := S.weakSerreClass X
  have hpullTri := isTriangulated_abelianComparisonPullback_mapDerivedCategoryPlus S X
  exact NatTrans.isIso_app_of_isGE_plus (derivedComparisonUnit S X)
    (isGE_derivedComparisonUnitTarget_obj S X) (S.weakSerre X)
    (fun M hM ↦ isIso_derivedComparisonUnit_app_single S hV X M hM) K hK

end Stacks.ComparingTopologies

end
