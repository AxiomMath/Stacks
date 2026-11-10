module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonClassWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedUnitIsomorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict
import StacksCore.Tactic.StacksAttribute

/-!
# Change of topology is an equivalence on bounded below derived categories

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in the situation of Stacks
0EZ3, let `X` be an object of `C` and write `ε_X : C_τ/X ⟶ C_{τ'}/X` for the change-of-topology
morphism. This file prepares the second assertion of Stacks 0EZG: the derived direct image

`Rε_{X,*} : D⁺_{𝒜_X}(C_τ/X) ⟶ D⁺_{𝒜'_X}(C_{τ'}/X)`

is an equivalence, with quasi-inverse `ε_X^{-1}`. The equivalence itself is built in
`DerivedComparisonEquivalence`, once `(V_n)` is known in every degree.

## Main definitions

* `Stacks.ComparingTopologies.derivedFineWeakSerre` and
  `Stacks.ComparingTopologies.derivedWeakSerre`: the two subcategories `D⁺_{𝒜_X}(C_τ/X)` and
  `D⁺_{𝒜'_X}(C_{τ'}/X)`, as classes of bounded below derived objects whose cohomology sheaves
  lie in `𝒜_X` resp. `𝒜'_X`.
* `Stacks.ComparingTopologies.derivedComparisonAdjunction`: the adjunction
  `ε_X^{-1} ⊣ Rε_{X,*}` on bounded below derived categories.
* `Stacks.ComparingTopologies.derivedComparisonPullbackLift`: the restriction of `ε_X^{-1}` to
  those two subcategories.

## Main results

* `Stacks.ComparingTopologies.isIso_derivedComparisonAdjunction_counit_app`: the counit of the
  derived adjunction is invertible at every object.
* `Stacks.ComparingTopologies.isIso_derivedComparisonAdjunction_unit_app`: its unit is
  invertible on `D⁺_{𝒜'_X}(C_{τ'}/X)`.

## The argument

The underived adjunction `ε_X^{-1} ⊣ ε_{X,*}` descends to bounded below derived categories by
`CategoryTheory.Adjunction.derived`, because `ε_X^{-1}` is exact and `ε_{X,*}` has a right
derived functor. Its counit is invertible at *every* object, since every bounded below object is
represented by a complex of injectives, where the unit of right derivation is invertible and the
derived counit is the degreewise one — invertible because `ε_{X,*}` is fully faithful. Its unit
is invertible on `D⁺_{𝒜'_X}` by clause (1) of Stacks 0EZF together with the right triangle
identity. Both functors preserve the two subcategories: `ε_X^{-1}` because it is exact and
carries `𝒜'_X` into `𝒜_X` by the definition of the latter, and `Rε_{X,*}` because a sheaf of
`𝒜_X` is `ε_{X,*}`-acyclic, so that `H^n(Rε_{X,*}K) = ε_{X,*}H^n(K)` lies in `𝒜'_X`. Restricting
the adjunction along the two fully faithful inclusions then gives an adjunction whose unit and
counit are invertible, hence an equivalence.

## Hypotheses

`isIso_derivedComparisonAdjunction_unit_app` carries `hV : ∀ n, S.vanishingCondition n`; that
condition is `CohomologyComparison.vanishingCondition_all` (Stacks 0EZF), proved downstream.

## References

* [Stacks Project, Tag 0EZG](https://stacks.math.columbia.edu/tag/0EZG)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZ9](https://stacks.math.columbia.edu/tag/0EZ9)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section AcyclicHomology

/-- Injective objects are right acyclic for functors preserving finite limits. -/
private theorem rightAcyclic_of_injective
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (I : A) [Injective I] :
    F.rightAcyclic I :=
  ((F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _).2
    (inferInstance : PreservesFiniteLimits F)).2
      (fun j hj => F.isZero_rightDerivedPlus_obj_injective j (ne_of_gt hj) _)

private theorem rightAcyclic_target_and_preservesCokernel
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {M N : A} (f : M ⟶ N) (hk : F.rightAcyclic (kernel f))
    (hM : F.rightAcyclic M) (hc : F.rightAcyclic (cokernel f)) :
    F.rightAcyclic N ∧ PreservesColimit (parallelPair f 0) F := by
  obtain ⟨hi, h₁⟩ := (F.rightAcyclic_and_shortExact_map_of_shortExact _
    (kernelCoimageShortExact f)).2.1 hk hM
  obtain ⟨hN, h₂⟩ := (F.rightAcyclic_and_shortExact_map_of_shortExact _
    (coimageCokernelShortExact f)).1 hi hc
  refine ⟨hN, ?_⟩
  have : Epi (F.map (Abelian.coimage.π f)) := h₁.epi_g
  have : Epi (F.map (cokernel.π f)) := h₂.epi_g
  let T := (ShortComplex.mk f (cokernel.π f) (by simp)).map F
  have ht : T.Exact := by
    let φ : T ⟶ (coimageCokernelShortComplex f).map F :=
      { τ₁ := F.map (Abelian.coimage.π f)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [T, coimageCokernelShortComplex, ← F.map_comp]
        comm₂₃ := by simp [T, coimageCokernelShortComplex] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h₂.exact
  have : Epi T.g := inferInstanceAs (Epi (F.map (cokernel.π f)))
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((isColimitMapCoconeCoforkEquiv' F (cokernel.condition f)).symm ht.gIsCokernel)

private theorem cycles_rightAcyclic_and_preservesCokernel
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ i, F.rightAcyclic (K.X i))
    (hH : ∀ i, F.rightAcyclic (K.homology i)) (n : ℤ) :
    F.rightAcyclic (K.cycles n) ∧
      PreservesColimit (parallelPair (K.toCycles (n - 1) n) 0) F := by
  have step (n : ℤ) (hn : F.rightAcyclic (K.cycles (n - 1))) :
      F.rightAcyclic (K.cycles n) ∧
        PreservesColimit (parallelPair (K.toCycles (n - 1) n) 0) F := by
    have hk : F.rightAcyclic (kernel (K.toCycles (n - 1) n)) := by
      let T := ShortComplex.mk (K.iCycles (n - 1)) (K.toCycles (n - 1) n)
        (by simp [← cancel_mono (K.iCycles n)])
      have ht : T.Exact := by
        let T' := ShortComplex.mk (K.iCycles (n - 1)) (K.d (n - 1) n) (by simp)
        let φ : T ⟶ T' :=
          { τ₁ := 𝟙 _
            τ₂ := 𝟙 _
            τ₃ := K.iCycles n
            comm₂₃ := by simp [T, T'] }
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
          (T'.exact_of_f_is_kernel (K.cyclesIsKernel (n - 1) n (by simp)))
      exact F.rightAcyclic.prop_of_iso
        (ht.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)) hn
    have hc : F.rightAcyclic (cokernel (K.toCycles (n - 1) n)) :=
      F.rightAcyclic.prop_of_iso
        ((K.homologyIsCokernel (n - 1) n (by simp)).coconePointUniqueUpToIso
          (colimit.isColimit _)) (hH n)
    exact rightAcyclic_target_and_preservesCokernel F _ hk (hK _) hc
  have hz (i : ℤ) (hi : i < a) : F.rightAcyclic (K.cycles i) := by
    have hzero : IsZero (K.cycles i) :=
      (CochainComplex.isStrictlyGE_iff K a).1 inferInstance i hi |>.of_mono (K.iCycles i)
    have : Injective (K.cycles i) := hzero.injective
    exact rightAcyclic_of_injective F _
  by_cases hn : n < a
  · exact step n (hz _ (by omega))
  · replace hn : a ≤ n := not_lt.1 hn
    induction n, hn using Int.leInduction with
    | base => exact step a (hz _ (by omega))
    | succ n hn ih => exact step (n + 1) (by simpa using ih.1)

private def mapHomologyIso_of_rightAcyclic
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ i, F.rightAcyclic (K.X i))
    (hH : ∀ i, F.rightAcyclic (K.homology i)) (n : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n ≅
      F.obj (K.homology n) := by
  let h := ShortComplex.LeftHomologyData.canonical (K.sc n)
  have : h.IsPreservedBy F :=
    { g := inferInstance
      f' := by
        change PreservesColimit
          (parallelPair (K.toCycles ((ComplexShape.up ℤ).prev n) n) 0) F
        have hp : (ComplexShape.up ℤ).prev n = n - 1 :=
          (ComplexShape.up ℤ).prev_eq' (by simp)
        rw [hp]
        exact (cycles_rightAcyclic_and_preservesCokernel F K a hK hH n).2 }
  exact (h.map F).homologyIso ≪≫ F.mapIso h.homologyIso.symm

private def rightDerivedFunctorPlus_homologyIso_of_rightAcyclic
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : DerivedCategory.Plus A)
    (hH : ∀ n, F.rightAcyclic ((DerivedCategory.Plus.homologyFunctor A n).obj K))
    (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).obj (F.rightDerivedFunctorPlus.obj K) ≅
      F.obj ((DerivedCategory.Plus.homologyFunctor A n).obj K) := by
  apply Classical.choice
  obtain ⟨a, ha⟩ := K.property
  have : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).1 ha
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K a
  let M := (InjectiveObject.ι A).mapCochainComplexPlus.obj I
  let N := (HomotopyCategory.Plus.quotient A).obj M
  have : I.obj.IsStrictlyGE a := hI
  have : M.obj.IsStrictlyGE a := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj) a
    infer_instance
  have : ∀ i : ℤ, Injective (N.obj.as.X i) := fun _ => inferInstance
  let eF : F.rightDerivedFunctorPlus.obj K ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj M) :=
    F.rightDerivedFunctorPlus.mapIso (((ObjectProperty.isoMk _
      ((DerivedCategory.quotientCompQhIso A).app M.obj)) ≪≫ e).symm) ≪≫
      (asIso (F.rightDerivedFunctorPlusUnith.app N)).symm ≪≫
      ObjectProperty.isoMk _
        (DerivedCategory.Qh.mapIso
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app M.obj) ≪≫
            (DerivedCategory.quotientCompQhIso B).app _)
  have hm (i : ℤ) : F.rightAcyclic (M.obj.X i) := by
    have : Injective (M.obj.X i) :=
      inferInstanceAs (Injective (I.obj.X i).obj)
    exact rightAcyclic_of_injective F _
  have hh (i : ℤ) : F.rightAcyclic (M.obj.homology i) :=
    F.rightAcyclic.prop_of_iso
      (((DerivedCategory.Plus.homologyFunctor A i).mapIso e).symm ≪≫
        (DerivedCategory.homologyFunctorFactors A i).app M.obj) (hH i)
  exact ⟨(DerivedCategory.Plus.homologyFunctor B n).mapIso eF ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app _ ≪≫
    mapHomologyIso_of_rightAcyclic F M.obj a hm hh n ≪≫
    F.mapIso (((DerivedCategory.homologyFunctorFactors A n).app M.obj).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor A n).mapIso e)⟩

end AcyclicHomology

/-- `D⁺_{𝒜_X}(C_τ/X)`: the bounded below derived objects on the finer localized site whose
cohomology sheaves all lie in the class `𝒜_X` of Stacks 0EZ9. -/
def derivedFineWeakSerre (S : CohomologyComparison C) (X : C) :
    ObjectProperty (DerivedCategory.Plus (AbelianSheaves S.fineCoverage.toGrothendieck X)) :=
  fun K ↦ ∀ i : ℤ, S.fineWeakSerre X
    ((DerivedCategory.Plus.homologyFunctor _ i).obj K)

/-- `D⁺_{𝒜'_X}(C_{τ'}/X)`: the bounded below derived objects on the coarser localized site
whose cohomology sheaves all lie in the given weak Serre class `𝒜'_X`. -/
def derivedWeakSerre (S : CohomologyComparison C) (X : C) :
    ObjectProperty (DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X)) :=
  fun K ↦ ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K)

/-- **The derived change-of-topology inverse image carries `D⁺_{𝒜'_X}` into `D⁺_{𝒜_X}`.** The
functor is exact, so its cohomology sheaves are `ε_X^{-1}` of those of its argument, and `𝒜_X`
is by definition the image of `𝒜'_X` under `ε_X^{-1}`. -/
theorem derivedFineWeakSerre_mapDerivedCategoryPlus_obj (S : CohomologyComparison C) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : derivedWeakSerre S X K) :
    derivedFineWeakSerre S X
      ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
        X).mapDerivedCategoryPlus.obj K) := by
  intro i
  let L := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  exact (S.fineWeakSerre X).prop_of_iso ((L.mapDerivedCategoryHomologyIso i).app K.obj).symm
    ((S.weakSerre X).prop_map_obj L (hK i))

/-- **The derived change-of-topology direct image carries `D⁺_{𝒜_X}` into `D⁺_{𝒜'_X}`**, granted
that every sheaf of `𝒜_X` is `ε_{X,*}`-acyclic. Acyclicity makes `H^n(Rε_{X,*}K)` equal to
`ε_{X,*}H^n(K)`, which lies in `𝒜'_X` by the membership criterion of Stacks 0EZ9. -/
theorem derivedWeakSerre_rightDerivedFunctorPlus_obj (S : CohomologyComparison C) (X : C)
    (hac : ∀ F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}, S.fineWeakSerre X F →
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightAcyclic F)
    (K : DerivedCategory.Plus (AbelianSheaves S.fineCoverage.toGrothendieck X))
    (hK : derivedFineWeakSerre S X K) :
    derivedWeakSerre S X
      ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerivedFunctorPlus.obj K) := by
  intro i
  let R := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let e := rightDerivedFunctorPlus_homologyIso_of_rightAcyclic R K
    (fun n => hac _ (hK n)) i
  exact (S.weakSerre X).prop_of_iso e.symm
    ((S.fineWeakSerre_iff_weakSerre_pushforward X _).1 (hK i))
/-- **An adjunction of additive functors whose left adjoint is exact descends to the bounded
below derived categories.** The degreewise adjunction on bounded below homotopy categories is
derived by `CategoryTheory.Adjunction.derived`: the left adjoint acts degreewise, so its
bounded below derived action is a left derived functor of that degreewise action (and remains
one after postcomposition by the right derived functor of `R`), while postcomposing the right
derived functor of `R` with the exact action of `L` is again a right derived functor because
the unit of right derivation is invertible on complexes of injectives. -/
def derivedPlusAdjunction {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus := by
  have : L.mapDerivedCategoryPlus.IsLeftDerivedFunctor
      L.mapDerivedCategoryPlusFactorsh.hom (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      L.mapDerivedCategoryPlusFactorsh
  have : (L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        L.mapDerivedCategoryPlusFactorsh R.rightDerivedFunctorPlus)
  have : (R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorPlusUnith L.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B) := by
    apply (HomotopyCategory.Plus.localizerMorphism_derives
      ((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        L.mapDerivedCategoryPlus)).isRightDerivedFunctor_of_isIso
    intro K
    dsimp
    infer_instance
  exact adj.mapHomotopyCategoryPlus.derived (HomotopyCategory.Plus.quasiIso A)
    (HomotopyCategory.Plus.quasiIso B) L.mapDerivedCategoryPlusFactorsh.hom
    R.rightDerivedFunctorPlusUnith

/-- **The counit of `derivedPlusAdjunction` is invertible when `R` is fully faithful.** Every
object of `D⁺(B)` is isomorphic to the image of a bounded below complex of injectives `N`, and
there the unit of right derivation of `R` is invertible; by
`CategoryTheory.Adjunction.derivedε_fac_app` the derived counit at `N` is then identified with
the counit of the degreewise adjunction on bounded below homotopy categories, which is
invertible because `R.mapHomotopyCategoryPlus` is fully faithful. -/
private theorem isIso_derivedPlusAdjunction_counit_app {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [R.Full] [R.Faithful]
    (adj : L ⊣ R) (Y : DerivedCategory.Plus B) :
    IsIso ((derivedPlusAdjunction adj).counit.app Y) := by
  obtain ⟨a, ha⟩ := Y.property
  have : Y.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Y a).1 ha
  obtain ⟨I, _, ⟨eY⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Y a
  let M := (InjectiveObject.ι B).mapCochainComplexPlus.obj I
  let N := (HomotopyCategory.Plus.quotient B).obj M
  have : ∀ i : ℤ, Injective (N.obj.as.X i) := fun _ => inferInstance
  have : IsIso (R.rightDerivedFunctorPlusUnith.app N) := inferInstance
  have : (R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorPlusUnith L.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B) := by
    apply (HomotopyCategory.Plus.localizerMorphism_derives
      ((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        L.mapDerivedCategoryPlus)).isRightDerivedFunctor_of_isIso
    intro K
    dsimp
    infer_instance
  have hfac := adj.mapHomotopyCategoryPlus.derivedε_fac_app
    (HomotopyCategory.Plus.quasiIso B) L.mapDerivedCategoryPlusFactorsh.hom
    R.rightDerivedFunctorPlusUnith N
  change L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N) ≫
    (derivedPlusAdjunction adj).counit.app (DerivedCategory.Plus.Qh.obj N) = _ at hfac
  have : IsIso ((derivedPlusAdjunction adj).counit.app (DerivedCategory.Plus.Qh.obj N)) := by
    have : IsIso (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N) ≫
        (derivedPlusAdjunction adj).counit.app (DerivedCategory.Plus.Qh.obj N)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N)) _
  exact (NatTrans.isIso_app_iff_of_iso _ ((ObjectProperty.isoMk _
    ((DerivedCategory.quotientCompQhIso B).app M.obj) :
      DerivedCategory.Plus.Qh.obj N ≅ DerivedCategory.Plus.Q.obj M) ≪≫ eY)).1 inferInstance

/-- **An adjunction whose counit is invertible everywhere has invertible unit at every object
isomorphic to one in the image of the right adjoint.** An invertible counit makes the right
adjoint fully faithful, and the unit of an adjunction with fully faithful right adjoint is
invertible exactly on the essential image of that right adjoint. -/
private theorem isIso_unit_app_of_isIso_counit {A B : Type*} [Category A] [Category B]
    {LF : A ⥤ B} {RF : B ⥤ A} (adj : LF ⊣ RF) (hc : ∀ Y, IsIso (adj.counit.app Y)) {K : A}
    (e : K ≅ RF.obj (LF.obj K)) :
    IsIso (adj.unit.app K) := by
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app adj.counit
  have hff : RF.FullyFaithful := adj.fullyFaithfulROfIsIsoCounit
  have : RF.Full := hff.full
  have : RF.Faithful := hff.faithful
  exact adj.isIso_unit_app_of_iso e

/-- **The adjunction `ε_X^{-1} ⊣ Rε_{X,*}` on bounded below derived categories**, obtained from
the change-of-topology adjunction on abelian sheaves. -/
def derivedComparisonAdjunction (S : CohomologyComparison C) (X : C) :
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus ⊣
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerivedFunctorPlus :=
  derivedPlusAdjunction
    (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine X)

/-- The unit of the degreewise change-of-topology adjunction on bounded below homotopy categories
is `Stacks.ComparingTopologies.abelianComparisonHomotopyUnit`, up to the two identifications of
the functors induced by an identity and by a composite. -/
private theorem mapHomotopyCategoryPlus_unit_app (S : CohomologyComparison C) (X : C)
    (K : HomotopyCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X)) :
    (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine
        X).mapHomotopyCategoryPlus.unit.app K =
      (Functor.mapHomotopyCategoryPlusIdComparison _).app K ≫
        (abelianComparisonHomotopyUnit S X).app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
            abelianComparisonPushforward S.fineCoverage S.coarseCoverage
              S.coarse_le_fine X))).inv.app K := by
  apply (HomotopyCategory.Plus.fullyFaithfulι _).map_injective
  let A := AbelianSheaves S.coarseCoverage.toGrothendieck X
  let εq := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let εp := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let adj := abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  change (adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K.obj ≫ 𝟙 _ ≫ 𝟙 _ =
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).inv.app K.obj.as) ≫
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K.obj.as) ≫
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (εq ⋙ εp))
          (ComplexShape.up ℤ)).inv.app K.obj.as)
  simp only [Adjunction.mapHomotopyCategory_unit_app, Category.comp_id, ← Functor.map_comp]
  congr 1

/-- **The unit of the derived change-of-topology adjunction is the canonical map**
`K' ⟶ Rε_{X,*}(ε_X^{-1}K')` of `Stacks.ComparingTopologies.derivedComparisonUnit`. Both are
transformations out of the identity of `D⁺(Ab(C_{τ'}/X))`, so they agree once they agree after
restriction along the localization functor, and there both are the degreewise unit followed by
the unit of right derivation of `ε_{X,*}`. -/
theorem derivedComparisonAdjunction_unit (S : CohomologyComparison C) (X : C) :
    (derivedComparisonAdjunction S X).unit = derivedComparisonUnit S X := by
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    _).map_injective
  refine NatTrans.ext (funext fun K => ?_)
  let εq := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let εp := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  have : (εq.mapDerivedCategoryPlus ⋙ εp.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        εq.mapDerivedCategoryPlusFactorsh.hom εp.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso _) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso _) _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        εq.mapDerivedCategoryPlusFactorsh εp.rightDerivedFunctorPlus)
  have hη := (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine
    X).mapHomotopyCategoryPlus.derivedη_fac_app
    (HomotopyCategory.Plus.quasiIso (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    εq.mapDerivedCategoryPlusFactorsh.hom εp.rightDerivedFunctorPlusUnith K
  have hu := NatTrans.congr_app (derivedComparisonUnit_fac S X) K
  change (derivedComparisonAdjunction S X).unit.app (DerivedCategory.Plus.Qh.obj K) =
    (derivedComparisonUnit S X).app (DerivedCategory.Plus.Qh.obj K)
  rw [← cancel_mono (εp.rightDerivedFunctorPlus.map (εq.mapDerivedCategoryPlusFactorsh.hom.app K))]
  refine hη.trans ?_
  have hu' : (derivedComparisonUnit S X).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusIdComparison _).app K ≫
          (abelianComparisonHomotopyUnit S X).app K ≫
          (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (εq ⋙ εp))).inv.app K) ≫
        εp.rightDerivedFunctorPlusUnith.app (εq.mapHomotopyCategoryPlus.obj K) ≫
        εp.rightDerivedFunctorPlus.map (εq.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    simpa [Functor.map_comp] using hu
  rw [hu', mapHomotopyCategoryPlus_unit_app S X K]
  simp [← Functor.map_comp]
  rfl

/-- **The counit of the derived change-of-topology adjunction is invertible at every object of
`D⁺(Ab(C_τ/X))`**, because `ε_{X,*}` is fully faithful. -/
theorem isIso_derivedComparisonAdjunction_counit_app (S : CohomologyComparison C) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.fineCoverage.toGrothendieck X)) :
    IsIso ((derivedComparisonAdjunction S X).counit.app K) :=
  isIso_derivedPlusAdjunction_counit_app
    (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine X) K

/-- **The unit of the derived change-of-topology adjunction is invertible on
`D⁺_{𝒜'_X}(C_{τ'}/X)`.** Clause (1) of Stacks 0EZF makes the canonical map
`K' ⟶ Rε_{X,*}(ε_X^{-1}K')` of `derivedComparisonUnit` invertible there, which exhibits `K'` as
an object of the essential image of `Rε_{X,*}`. -/
theorem isIso_derivedComparisonAdjunction_unit_app (S : CohomologyComparison C)
    (hV : ∀ n : ℕ, S.vanishingCondition n) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso ((derivedComparisonAdjunction S X).unit.app K) := by
  have : IsIso ((derivedComparisonUnit S X).app K) :=
    isIso_derivedComparisonUnit_app_of_vanishingCondition S hV X K hK
  exact isIso_unit_app_of_isIso_counit (derivedComparisonAdjunction S X)
    (fun Y => isIso_derivedComparisonAdjunction_counit_app S X Y)
    (asIso ((derivedComparisonUnit S X).app K))
/-- `ε_X^{-1} : D⁺_{𝒜'_X}(C_{τ'}/X) ⥤ D⁺_{𝒜_X}(C_τ/X)`, the restriction of the derived action
of the change-of-topology inverse image. -/
abbrev derivedComparisonPullbackLift (S : CohomologyComparison C) (X : C) :
    (derivedWeakSerre S X).FullSubcategory ⥤ (derivedFineWeakSerre S X).FullSubcategory :=
  (derivedFineWeakSerre S X).lift ((derivedWeakSerre S X).ι ⋙
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus)
    fun K ↦ derivedFineWeakSerre_mapDerivedCategoryPlus_obj S X K.obj K.property

end Stacks.ComparingTopologies

end
