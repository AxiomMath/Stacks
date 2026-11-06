module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowComparisonDevissage
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonClass
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPushforwardPreservesComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing cohomology in two topologies

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in the situation of
Stacks 0EZ3, let `X` be an object of `C` and write `ε_X : C_τ/X ⟶ C_τ'/X` for the
change-of-topology morphism. Assume the vanishing condition `(V_n)` of that situation: the
higher direct images `R^i ε_{X,*} ℱ` vanish for `1 ≤ i ≤ n` and every `ℱ` in the class `𝒜_X`.

This file proves **Stacks 0EZB**: for an object `L` of `D(C_{τ'}/X)` whose cohomology sheaves
vanish in negative degrees and lie in the weak Serre class `𝒜'_X` in the degrees `0, …, n`, the
canonical map

`H^n_{τ'}(X, L) ⟶ H^n_τ(X, ε_X^{-1}L)`

is an isomorphism. The map is `Stacks.ComparingTopologies.derivedCohomologyComparison` read on
`H^n`; the hypotheses on `L` are carried exactly as the source states them, in particular
membership in `𝒜'_X` is required **only** in the degrees `0 ≤ i ≤ n`, and the vanishing
condition assumed is `(V_n)` for that single `n`.

## The proof

The source argues with the spectral sequence `E_2^{p,q} = R^p ε_{X,*} ε_X^{-1} H^q(L)`
converging to `H^{p+q}(Rε_{X,*}ε_X^{-1}L)`, concludes from `(V_n)` that the only nonzero terms
with `p + q ≤ n` sit in the row `p = 0`, and reads off that `L ⟶ Rε_{X,*}ε_X^{-1}L` is an
isomorphism in degrees `≤ n`. Here that conclusion is obtained by dévissage instead, in three
steps.

1. **One sheaf.** For `ℱ'` in `𝒜'_X` placed in degree zero, `H^i` of the canonical map
   `L ⟶ Rε_{X,*}ε_X^{-1}L`, that is of `Stacks.ComparingTopologies.derivedComparisonUnit`, is
   invertible for every `i ≤ n`. After restriction along the localization functor the map is the
   composite of five transformations recorded by `derivedComparisonUnit_fac`; on a single sheaf
   of `𝒜'_X` the ordinary unit is invertible by the sheaf-condition assumption of the situation,
   and the unit of right derivation of `ε_{X,*}` is invertible on `H^i` because `R^i ε_{X,*}` of
   the sheaf vanishes — for `i < 0` always, for `i = 0` because `ε_{X,*}` is left exact, and for
   `1 ≤ i ≤ n` by `(V_n)`.
2. **Any single degree.** The same for `ℱ'` placed in a degree `a ≥ 0`, which follows because
   the derived unit commutes with the shift,
   `Stacks.ComparingTopologies.commShift_derivedComparisonUnit`.
3. **Dévissage.** The property "invertible on `H^i` for `i ≤ n` and monomorphic on `H^{n+1}`"
   propagates from single objects to every object with cohomology in a finite window, by
   `DerivedCategory.Plus.isIso_homology_comparison_of_bounded`. Applying it to the truncation
   `τ_{≤n}L`, whose cohomology lies in `𝒜'_X` in every degree, and comparing `τ_{≤n}L` with `L`
   along the truncation morphism, gives the theorem.

## Main results

* `Stacks.ComparingTopologies.isIso_homology_derivedComparisonUnit_single`: step 1.
* `Stacks.ComparingTopologies.isIso_homology_derivedComparisonUnit_single_shift`: step 2.
* `Stacks.ComparingTopologies.isIso_homology_derivedComparisonUnit_of_bounded`: step 3.
* `Stacks.ComparingTopologies.isIso_homology_derivedCohomologyComparison_of_bounded`: the
  conclusion for an object with cohomology in the window `[0, n]`, which is where the dévissage
  lands.
* `Stacks.ComparingTopologies.isIso_homology_derivedCohomologyComparison`: **Stacks 0EZB**.

## Implementation notes

The source writes the conclusion as an equality `H^n_{τ'}(X, L) = H^n_τ(X, ε_X^{-1}L)`; what is
proved is that the canonical map between the two is invertible, which is the content of such an
equality in the source's idiom. There is exactly one such map in this development, the one built
in `DerivedCohomologyComparison`, and nothing is chosen in it.

`L` is taken in the *unbounded* derived category, as the source does, and the vanishing of its
cohomology in negative degrees is what places it in the bounded below derived category where the
comparison lives; `DerivedCategory.Plus.ofNonnegative` performs that passage and consumes
precisely that hypothesis.

Membership in `𝒜'_X` is indexed by a natural number `i ≤ n`, matching `0 ≤ i ≤ n` in the source.
The truncation `τ_{≤n}L` then has all of its cohomology in `𝒜'_X`: the degrees below `0` and
above `n` contribute zero objects, and a weak Serre class contains the zero object.

The commutation of the three functors involved with the shift is not available by instance
search; the local instances at the top of the file are the same ones
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedUnitCommShift` installs,
and are what makes `commShift_derivedComparisonUnit` applicable here.

## References

* [Stacks Project, Tag 0EZB](https://stacks.math.columbia.edu/tag/0EZB)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus
attribute [local instance] commShiftMapDerivedCategoryPlus
attribute [local instance] commShiftMapDerivedCategoryPlusFactorsh

section Single

/-- The functor induced on bounded below homotopy categories by an additive functor carries a
single complex to the single complex on the image. -/
private def mapHomotopySingleIso {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (M : A) (n : ℤ) :
    F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A n).obj M) ≅
      (HomotopyCategory.Plus.singleFunctor B n).obj (F.obj M) :=
  ObjectProperty.isoMk _
    ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
        ((CochainComplex.singleFunctor A n).obj M) ≪≫
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app M))

/-- The comparison of the identity functor of a bounded below homotopy category with the functor
induced there by the identity functor is invertible: it is the inverse of an isomorphism. -/
private lemma isIso_mapHomotopyCategoryPlusIdComparison_app
    (A : Type*) [Category A] [Preadditive A] (K : HomotopyCategory.Plus A) :
    IsIso ((Functor.mapHomotopyCategoryPlusIdComparison A).app K) := by
  suffices IsIso ((HomotopyCategory.Plus.ι A).map
      ((Functor.mapHomotopyCategoryPlusIdComparison A).app K)) from
    isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι A)
  let e : (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.natIsoLift _
      (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)))
  show IsIso (e.inv.app K.obj)
  infer_instance

/-- **The degreewise change-of-topology unit is invertible on a single sheaf of `𝒜'_X`.** The
unit of the change-of-topology adjunction is invertible at a sheaf of `𝒜'_X` by the
sheaf-condition assumption of Stacks 0EZ3, and at the zero terms of the single complex for
trivial reasons; a morphism of complexes invertible in every degree is invertible. -/
theorem isIso_abelianComparisonHomotopyUnit_single (S : CohomologyComparison C) (X : C)
    (M : AbelianSheaves S.coarseCoverage.toGrothendieck X) (hM : S.weakSerre X M) :
    IsIso ((abelianComparisonHomotopyUnit S X).app
      ((HomotopyCategory.Plus.singleFunctor _ 0).obj M)) := by
  set η := (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
    S.coarse_le_fine X).unit with hη
  set K := (CochainComplex.singleFunctor
    (AbelianSheaves S.coarseCoverage.toGrothendieck X) 0).obj M with hK
  have hunit : IsIso (η.app M) :=
    isIso_abelianComparisonAdjunction_unit_of_weakSerre S X M hM
  have hcomp : ∀ i : ℤ, IsIso (η.app (K.X i)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact (NatTrans.isIso_app_iff_of_iso η
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).2 hunit
    · have hz : IsZero (K.X i) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      exact ⟨0, hz.eq_of_src _ _,
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
          abelianComparisonPushforward S.fineCoverage S.coarseCoverage
            S.coarse_le_fine X).map_isZero hz).eq_of_src _ _⟩
  have hdeg : ∀ i : ℤ, IsIso (((NatTrans.mapHomologicalComplex η
      (ComplexShape.up ℤ)).app K).f i) := hcomp
  have hiso : IsIso ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K) :=
    HomologicalComplex.Hom.isIso_of_components _
  suffices IsIso ((HomotopyCategory.Plus.ι
      (AbelianSheaves S.coarseCoverage.toGrothendieck X)).map
      ((abelianComparisonHomotopyUnit S X).app
        ((HomotopyCategory.Plus.singleFunctor _ 0).obj M))) from
    isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι _)
  show IsIso ((HomotopyCategory.quotient
    (AbelianSheaves S.coarseCoverage.toGrothendieck X) (ComplexShape.up ℤ)).map
    ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K))
  infer_instance

/-- **Step 1 of Stacks 0EZB.** Under `(V_n)`, the canonical map `L ⟶ Rε_{X,*}ε_X^{-1}L` is
invertible on cohomology in every degree `i ≤ n` at a sheaf of `𝒜'_X` placed in degree zero.

After restriction along the localization functor the map is the composite recorded by
`derivedComparisonUnit_fac`. Of its five factors two are comparison isomorphisms, the degreewise
unit is invertible on a single sheaf of `𝒜'_X`, and the unit of right derivation of `ε_{X,*}` is
invertible on `H^i`: in negative degrees both its source and target vanish, in degree zero
because `ε_{X,*}` is left exact, and in a degree `1 ≤ i ≤ n` because `(V_n)` makes
`R^i ε_{X,*}` of the sheaf vanish. -/
theorem isIso_homology_derivedComparisonUnit_single (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C)
    (M : AbelianSheaves S.coarseCoverage.toGrothendieck X) (hM : S.weakSerre X M)
    (i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      ((derivedComparisonUnit S X).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) := by
  set pull := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  set push := abelianComparisonPushforward S.fineCoverage S.coarseCoverage
    S.coarse_le_fine X
  set H := (HomotopyCategory.Plus.singleFunctor
    (AbelianSheaves S.coarseCoverage.toGrothendieck X) 0).obj M
  have hunit : IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      (push.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor _ 0).obj (pull.obj M)))) := by
    by_cases h0 : i = 0
    · subst h0
      exact (Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
        push push.rightDerivedFunctorPlus push.rightDerivedFunctorPlusUnith).2.2.2 inferInstance
        (pull.obj M)
    apply IsZero.isIso
    · refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
        ((Functor.mapSingleFunctorCompQhIso push).app (pull.obj M)))
      rcases lt_or_gt_of_ne h0 with hneg | hpos
      · exact DerivedCategory.Plus.isZero_homology_of_isGE
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (push.obj (pull.obj M))) 0 i hneg
      · exact DerivedCategory.Plus.isZero_homology_of_isLE
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (push.obj (pull.obj M))) 0 i hpos
    · refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
        (push.rightDerivedFunctorPlus.mapIso
          ((Functor.singleFunctorPlusIsoCompQh 0).app (pull.obj M)))).symm
      rcases lt_or_gt_of_ne h0 with hneg | hpos
      · exact ((Functor.isZero_iff _).1
          ((Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
            push push.rightDerivedFunctorPlus push.rightDerivedFunctorPlusUnith).1 i hneg))
          (pull.obj M)
      · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hpos)
        exact IsZero.of_iso (hV X (pull.obj M) ⟨M, hM, ⟨Iso.refl _⟩⟩ degree (by omega) (by omega))
          ((Stacks.DerivedIndexing.rightDerivedIso push degree).app (pull.obj M)).symm
  have h₁ := isIso_mapHomotopyCategoryPlusIdComparison_app
    (AbelianSheaves S.coarseCoverage.toGrothendieck X) H
  have h₂ := isIso_abelianComparisonHomotopyUnit_single S X M hM
  have h₃ : IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      (push.rightDerivedFunctorPlusUnith.app (pull.mapHomotopyCategoryPlus.obj H))) :=
    (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight push.rightDerivedFunctorPlusUnith
        (DerivedCategory.Plus.homologyFunctor _ i)) (mapHomotopySingleIso pull M 0)).2 hunit
  show IsIso ((Functor.whiskerRight (derivedComparisonUnit S X)
    (DerivedCategory.Plus.homologyFunctor _ i)).app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj M))
  rw [NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerRight (derivedComparisonUnit S X)
      (DerivedCategory.Plus.homologyFunctor _ i))
    ((Functor.singleFunctorPlusIsoCompQh 0).app M)]
  have eqn := NatTrans.congr_app (derivedComparisonUnit_fac S X) H
  show IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
    ((derivedComparisonUnit S X).app (DerivedCategory.Plus.Qh.obj H)))
  change (derivedComparisonUnit S X).app (DerivedCategory.Plus.Qh.obj H) = _ at eqn
  rw [eqn]
  dsimp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app]
  simp only [Functor.map_comp]
  infer_instance

/-- **Step 2 of Stacks 0EZB.** Under `(V_n)`, the canonical map `L ⟶ Rε_{X,*}ε_X^{-1}L` is
invertible on cohomology in every degree `i ≤ a + n` at a sheaf of `𝒜'_X` placed in a degree
`a`. The derived unit commutes with the shift, so the statement is the one in degree zero read
`a` degrees up. -/
theorem isIso_homology_derivedComparisonUnit_single_shift (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C)
    (M : AbelianSheaves S.coarseCoverage.toGrothendieck X) (hM : S.weakSerre X M)
    (a i : ℤ) (hi : i ≤ a + n) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      ((derivedComparisonUnit S X).app
        ((DerivedCategory.Plus.singleFunctor _ a).obj M))) := by
  set α := derivedComparisonUnit S X with hα
  set K := (DerivedCategory.Plus.singleFunctor
    (AbelianSheaves S.coarseCoverage.toGrothendieck X) 0).obj M with hK
  have hzero := isIso_homology_derivedComparisonUnit_single S n hV X M hM (i - a) (by omega)
  have hshift : IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map ((α.app K)⟦-a⟧')) :=
    (NatIso.isIso_map_iff
      ((DerivedCategory.Plus.homologyFunctor
        (AbelianSheaves S.coarseCoverage.toGrothendieck X) 0).shiftIso (-a) i (i - a)
          (by omega))
      (α.app K)).2 hzero
  show IsIso ((Functor.whiskerRight α (DerivedCategory.Plus.homologyFunctor _ i)).app
    ((DerivedCategory.Plus.singleFunctor _ a).obj M))
  rw [← NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerRight α (DerivedCategory.Plus.homologyFunctor _ i))
    (((DerivedCategory.Plus.singleFunctors
      (AbelianSheaves S.coarseCoverage.toGrothendieck X)).shiftIso (-a) a 0 (by simp)).app M)]
  show IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map (α.app (K⟦-a⟧)))
  rw [NatTrans.app_shift]
  simp only [Functor.map_comp]
  infer_instance

end Single

section Devissage

/-- **Step 3 of Stacks 0EZB.** Under `(V_n)`, the canonical map `L ⟶ Rε_{X,*}ε_X^{-1}L` is
invertible on cohomology in every degree `i ≤ n` at every object of `D⁺(C_{τ'}/X)` whose
cohomology lies in `𝒜'_X` in every degree and is concentrated in the window `[0, n]`.

This is the dévissage of `DerivedCategory.Plus.isIso_homology_comparison_of_bounded` fed with
`isIso_homology_derivedComparisonUnit_single_shift`. In degree `n + 1` the monomorphism clause
that dévissage also requires holds at a sheaf placed in degree `0` because there the source of
the map vanishes, and at a sheaf placed in a degree `a ≥ 1` because then `n + 1 ≤ a + n`. -/
theorem isIso_homology_derivedComparisonUnit_of_bounded (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    [K.IsGE 0] [K.IsLE (n : ℤ)]
    (hK : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    ∀ i : ℤ, i ≤ (n : ℤ) → IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      ((derivedComparisonUnit S X).app K)) := by
  have hwsc : (S.weakSerre X).IsWeakSerreClass := S.weakSerreClass X
  have hhomotopy : (abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapHomotopyCategoryPlus.IsTriangulated := inferInstance
  have hcomp : ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsTriangulated :=
    Functor.IsTriangulated.instComp _ _
  have hpullTri : (abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapDerivedCategoryPlus.IsTriangulated :=
    Functor.isTriangulated_of_precomp_iso (abelianComparisonPullback S.fineCoverage
      S.coarseCoverage X).mapDerivedCategoryPlusFactorsh
  have hsingle : ∀ M : AbelianSheaves S.coarseCoverage.toGrothendieck X,
      S.weakSerre X M → ∀ a : ℤ, 0 ≤ a →
      (∀ i ≤ (n : ℤ), IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
        ((derivedComparisonUnit S X).app
          ((DerivedCategory.Plus.singleFunctor _ a).obj M)))) ∧
      Mono ((DerivedCategory.Plus.homologyFunctor _ ((n : ℤ) + 1)).map
        ((derivedComparisonUnit S X).app
          ((DerivedCategory.Plus.singleFunctor _ a).obj M))) := by
    intro M hM a ha
    refine ⟨fun i hi ↦ isIso_homology_derivedComparisonUnit_single_shift S n hV X M hM a i
      (by omega), ?_⟩
    by_cases hzero : a = 0
    · subst hzero
      exact (DerivedCategory.Plus.isZero_homology_of_isLE
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) 0 ((n : ℤ) + 1) (by omega)).mono _
    · have := isIso_homology_derivedComparisonUnit_single_shift S n hV X M hM a
        ((n : ℤ) + 1) (by omega)
      infer_instance
  have hLE : K.IsLE (0 + (n : ℤ)) := by simpa using (inferInstance : K.IsLE (n : ℤ))
  exact (DerivedCategory.Plus.isIso_homology_comparison_of_bounded
    ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus ⋙
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerivedFunctorPlus)
    (derivedComparisonUnit S X) (S.weakSerre X) (n : ℤ) hsingle n 0 le_rfl K hK).1

end Devissage

section Main

/-- A commutative square three of whose four sides are invertible has an invertible fourth
side. -/
private lemma isIso_of_comm_square {A : Type*} [Category A] {W X Y Z : A}
    (a : W ⟶ X) (d : X ⟶ Z) (c : W ⟶ Y) (b : Y ⟶ Z)
    (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) (hsq : a ≫ d = c ≫ b) : IsIso d := by
  have := ha
  have := hb
  have := hc
  have hfac : IsIso (a ≫ d) := by
    rw [hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left a d

/-- **Stacks 0EZB for an object with cohomology in the window `[0, n]`.** If every cohomology
sheaf of `K` lies in `𝒜'_X` and `K` has no cohomology outside the degrees `0, …, n`, then the
comparison of cohomology in the two topologies is invertible in degree `n`.

The comparison is `RΓ_{τ'}(X, -)` applied to the canonical map `L ⟶ Rε_{X,*}ε_X^{-1}L` followed
by two isomorphisms, and that canonical map is invertible on cohomology in all degrees `≤ n` by
dévissage; a total right derived functor turns the latter into invertibility on cohomology in
degree `n`. -/
theorem isIso_homology_derivedCohomologyComparison_of_bounded (S : CohomologyComparison C)
    (n : ℕ) (hV : S.vanishingCondition n) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    [K.IsGE 0] [K.IsLE (n : ℤ)]
    (hK : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} (n : ℤ)).map
      ((derivedCohomologyComparison S X).app K)) := by
  have hmap : IsIso ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} (n : ℤ)).map
      ((globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerivedFunctorPlus.map
        ((derivedComparisonUnit S X).app K))) :=
    DerivedCategory.Plus.isIso_homology_rightDerivedFunctorPlus_map_of_isIso_homology_le
      (globalSectionsOver S.coarseCoverage.toGrothendieck X) _ (n : ℤ)
      (isIso_homology_derivedComparisonUnit_of_bounded S n hV X K hK)
  dsimp only [derivedCohomologyComparison]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp]
  infer_instance

/-- **Stacks 0EZB.** In the comparison situation of Stacks 0EZ3, assume the vanishing condition
`(V_n)`. Let `X` be an object of `C` and let `L` be an object of `D(C_{τ'}/X)` whose cohomology
sheaves vanish in negative degrees and lie in the weak Serre class `𝒜'_X` in the degrees
`0 ≤ i ≤ n`. Then the canonical map

`H^n_{τ'}(X, L) ⟶ H^n_τ(X, ε_X^{-1}L)`

of `Stacks.ComparingTopologies.derivedCohomologyComparison` is an isomorphism.

The truncation `τ_{≤n}L` has all of its cohomology in `𝒜'_X` and none outside the degrees
`0, …, n`, so the comparison is invertible in degree `n` there; and the truncation morphism
`τ_{≤n}L ⟶ L` becomes invertible on `H^n` after applying either `RΓ_{τ'}(X, -)` or `ε_X^{-1}`
followed by `RΓ_τ(X, -)`. The naturality square of the comparison then carries the conclusion
from `τ_{≤n}L` to `L`. -/
@[stacks 0EZB]
theorem isIso_homology_derivedCohomologyComparison (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C)
    (L : DerivedCategory (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hneg : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) i).obj L))
    (hmem : ∀ i : ℕ, i ≤ n → S.weakSerre X ((DerivedCategory.homologyFunctor
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) (i : ℤ)).obj L)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} (n : ℤ)).map
      ((derivedCohomologyComparison S X).app
        (DerivedCategory.Plus.ofNonnegative L hneg))) := by
  have hwsc : (S.weakSerre X).IsWeakSerreClass := S.weakSerreClass X
  have hKGE : (DerivedCategory.Plus.ofNonnegative L hneg).IsGE 0 :=
    DerivedCategory.Plus.isGE_ofNonnegative L hneg
  -- every cohomology sheaf of the truncation lies in `𝒜'_X`
  have hcutMem : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((DerivedCategory.Plus.TStructure.t.truncLE (n : ℤ)).obj
        (DerivedCategory.Plus.ofNonnegative L hneg))) := by
    refine DerivedCategory.Plus.prop_homology_truncLE_obj (S.weakSerre X)
      (DerivedCategory.Plus.ofNonnegative L hneg) (n : ℤ) ?_
    intro j hjn
    by_cases hjneg : j < 0
    · exact (S.weakSerre X).prop_of_isZero (hneg j hjneg)
    · have hj : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
      have hmemj := hmem j.toNat (by omega)
      rw [hj] at hmemj
      exact hmemj
  -- the comparison is invertible in degree `n` at the truncation
  have hcut := isIso_homology_derivedCohomologyComparison_of_bounded S n hV X
    ((DerivedCategory.Plus.TStructure.t.truncLE (n : ℤ)).obj
      (DerivedCategory.Plus.ofNonnegative L hneg)) hcutMem
  -- the truncation morphism becomes invertible on `H^n` on both sides of the comparison
  have hsource : IsIso ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} (n : ℤ)).map
      ((globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLEι (n : ℤ)).app
          (DerivedCategory.Plus.ofNonnegative L hneg)))) :=
    DerivedCategory.Plus.isIso_homology_rightDerivedFunctorPlus_map_truncLEι_app
      (globalSectionsOver S.coarseCoverage.toGrothendieck X) _ (n : ℤ) (n : ℤ) le_rfl
  have hinput : ∀ i : ℤ, i ≤ (n : ℤ) →
      IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
          X).mapDerivedCategoryPlus.map
          ((DerivedCategory.Plus.TStructure.t.truncLEι (n : ℤ)).app
            (DerivedCategory.Plus.ofNonnegative L hneg)))) := fun i hi ↦
    DerivedCategory.Plus.isIso_homology_mapDerivedCategoryPlus_map _ _ i
      (DerivedCategory.Plus.isIso_homologyMap_truncLEι_app _ i (n : ℤ) hi)
  have htarget : IsIso ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} (n : ℤ)).map
      ((globalSectionsOver S.fineCoverage.toGrothendieck X).rightDerivedFunctorPlus.map
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage
          X).mapDerivedCategoryPlus.map
          ((DerivedCategory.Plus.TStructure.t.truncLEι (n : ℤ)).app
            (DerivedCategory.Plus.ofNonnegative L hneg))))) :=
    DerivedCategory.Plus.isIso_homology_rightDerivedFunctorPlus_map_of_isIso_homology_le
      (globalSectionsOver S.fineCoverage.toGrothendieck X) _ (n : ℤ) hinput
  refine isIso_of_comm_square _ _ _ _ hsource htarget hcut ?_
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (DerivedCategory.Plus.homologyFunctor Ab.{max u v} (n : ℤ)).map
    ((derivedCohomologyComparison S X).naturality
      ((DerivedCategory.Plus.TStructure.t.truncLEι (n : ℤ)).app
        (DerivedCategory.Plus.ofNonnegative L hneg)))

end Main

end Stacks.ComparingTopologies

end
