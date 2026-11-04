module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedComparisonConservative
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The comparison theorems of Stacks 0EZF read along an exact functor into `𝒜'`

Situation 0EZ3 fixes a finer coverage `τ` and a coarser coverage `τ'` on a category `C`, with a
weak Serre class `𝒜'_X` of abelian sheaves on each `C_{τ'}/X`. In the applications, `𝒜'_X` is the
essential image of an exact functor `P : 𝒜 ⥤ Ab(C_{τ'}/X)`. For example, `P` is the inverse image
`π_X^{-1}` from the small étale site, and `𝒜'_X` is its essential image. The composite
`a_X^{-1} = ε_X^{-1} ∘ P` is the inverse image to the finer site. This file reads clause (1) and
the base change clause (2) of Stacks 0EZF through such a `P`.

1. For `K` in `D⁺(𝒜)` the canonical map `P K ⟶ Rε_{X,*}(a_X^{-1} K)` is an isomorphism.
2. For a morphism `f : X ⟶ Y` of `C`, an additive `g : 𝒜_X ⥤ 𝒜_Y`, and an identification
   `P_Y ∘ Rg = Rf_{τ',*} ∘ P_X` on `D⁺(𝒜_X)`, there is an identification
   `a_Y^{-1} ∘ Rg = Rf_{τ,*} ∘ a_X^{-1}` on `D⁺(𝒜_X)`.

These are the shapes of parts (3) and (4) of Stacks 0DDS, where `g = f_{small,*}` and the
identification is Stacks 0DDJ (4).

## Main definitions

* `Stacks.ComparingTopologies.CohomologyComparison.derivedComparisonUnitAlong`: the map
  `P K ⟶ Rε_{X,*}(a_X^{-1} K)`.
* `Stacks.ComparingTopologies.CohomologyComparison.derivedBaseChangeAlongIso`: the
  identification `Rg ⋙ a_Y^{-1} ≅ a_X^{-1} ⋙ Rf_{τ,*}`.

## Main results

* `Stacks.ComparingTopologies.CohomologyComparison.derivedWeakSerre_mapDerivedCategoryPlus_obj`:
  `P` carries `D⁺(𝒜)` into `D⁺_{𝒜'_X}`.
* `Stacks.ComparingTopologies.CohomologyComparison.isIso_derivedComparisonUnitAlong`: the map of
  clause 1 is an isomorphism.

## Implementation notes

The derived categories are those of `HasDerivedCategory.standard`, the model in which Stacks 0EZF,
`Stacks.ComparingTopologies.isIso_derivedComparisonUnit_app`
(`ChangeOfTopology/HigherDirectImageVanishing.lean:78`), is stated.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

-- Stacks 0EZF, `isIso_derivedComparisonUnit_app` (HigherDirectImageVanishing.lean:78), is stated
-- in the standard model.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace CohomologyComparison

section Unit

variable (S : CohomologyComparison C) (X : C) {A : Type*} [Category A] [Abelian A]
  (P : A ⥤ AbelianSheaves S.coarseCoverage.toGrothendieck X) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- An exact functor landing in `𝒜'_X` carries every bounded below complex into `D⁺_{𝒜'_X}`. Its
cohomology sheaves are the images under `P` of those of the complex. -/
theorem derivedWeakSerre_mapDerivedCategoryPlus_obj (hP : ∀ F : A, S.weakSerre X (P.obj F))
    (K : DerivedCategory.Plus A) :
    derivedWeakSerre S X (P.mapDerivedCategoryPlus.obj K) := fun i ↦
  (S.weakSerreClass X).toIsClosedUnderIsomorphisms.of_iso
    ((P.mapDerivedCategoryHomologyIso i).app K.obj).symm (hP _)

/-- **The map `P K ⟶ Rε_{X,*}(a_X^{-1} K)`** for `a_X^{-1} = P ⋙ ε_X^{-1}`. It is the unit
`P K ⟶ Rε_{X,*}(ε_X^{-1}(P K))` of the change of topology, followed by `Rε_{X,*}` of the
identification `ε_X^{-1}(P K) ≅ a_X^{-1} K` of the derived actions of the exact functors. -/
def derivedComparisonUnitAlong :
    P.mapDerivedCategoryPlus ⟶
      (P ⋙ abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus ⋙
        (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).rightDerivedFunctorPlus :=
  Functor.whiskerLeft P.mapDerivedCategoryPlus (derivedComparisonUnit S X) ≫
    Functor.whiskerRight (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso P
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage X)).hom
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerivedFunctorPlus

/-- **The map `P K ⟶ Rε_{X,*}(a_X^{-1} K)` is an isomorphism** for every `K` in `D⁺(𝒜)`, when
`P` lands in `𝒜'_X`. This is Stacks 0EZF (1) at `P K`, which lies in `D⁺_{𝒜'_X}`. -/
theorem isIso_derivedComparisonUnitAlong (hP : ∀ F : A, S.weakSerre X (P.obj F)) :
    IsIso (derivedComparisonUnitAlong S X P) := by
  have (K : DerivedCategory.Plus A) :
      IsIso ((derivedComparisonUnit S X).app (P.mapDerivedCategoryPlus.obj K)) :=
    isIso_derivedComparisonUnit_app S X _ (derivedWeakSerre_mapDerivedCategoryPlus_obj S X P hP K)
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  dsimp [derivedComparisonUnitAlong]
  infer_instance

end Unit

section BaseChange

variable (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
  {A : Type*} [Category A] [Abelian A] [EnoughInjectives A]
  {A' : Type*} [Category A'] [Abelian A']
  (PX : A ⥤ AbelianSheaves S.coarseCoverage.toGrothendieck X) [PX.Additive]
  [PreservesFiniteLimits PX] [PreservesFiniteColimits PX]
  (PY : A' ⥤ AbelianSheaves S.coarseCoverage.toGrothendieck Y) [PY.Additive]
  [PreservesFiniteLimits PY] [PreservesFiniteColimits PY]
  (g : A ⥤ A') [g.Additive]

/-- **Base change along an exact functor into `𝒜'`.** Let `f : X ⟶ Y` be a morphism of `C`, let
`P_X` be an exact functor landing in `𝒜'_X` and `P_Y` an exact functor, and let `g : 𝒜_X ⥤ 𝒜_Y`
be additive. An identification `β : Rg ⋙ P_Y ≅ P_X ⋙ Rf_{τ',*}` on `D⁺(𝒜_X)` gives the
identification

`Rg ⋙ a_Y^{-1} ≅ a_X^{-1} ⋙ Rf_{τ,*}`, where `a^{-1} = P ⋙ ε^{-1}`.

It is `β` followed by the base change of Stacks 0EZF (2) at `P_X K`, which lies in `D⁺_{𝒜'_X}`.
The derived actions of the exact functors `P` and `ε^{-1}` are identified with each other and
with their right derived functors. -/
def derivedBaseChangeAlongIso (hPX : ∀ F : A, S.weakSerre X (PX.obj F))
    (β : g.rightDerivedFunctorPlus ⋙ PY.mapDerivedCategoryPlus ≅
      PX.mapDerivedCategoryPlus ⋙
        (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlus) :
    g.rightDerivedFunctorPlus ⋙
        (PY ⋙ abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).mapDerivedCategoryPlus ≅
      (PX ⋙ abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus ⋙
        (overPushforward S.fineCoverage.toGrothendieck f).rightDerivedFunctorPlus := by
  let εY := abelianComparisonPullback S.fineCoverage S.coarseCoverage Y
  let εX := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let fc := overPushforward S.coarseCoverage.toGrothendieck f
  let ff := overPushforward S.fineCoverage.toGrothendieck f
  have (K : DerivedCategory.Plus A) :
      IsIso ((derivedComparisonBaseChange S f).app (PX.mapDerivedCategoryPlus.obj K)) :=
    isIso_derivedComparisonBaseChange_app S f _
      (derivedWeakSerre_mapDerivedCategoryPlus_obj S X PX hPX K)
  have : IsIso (Functor.whiskerLeft PX.mapDerivedCategoryPlus (derivedComparisonBaseChange S f)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K ↦ this K
  exact Functor.isoWhiskerLeft g.rightDerivedFunctorPlus
      (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso PY εY).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight β εY.mapDerivedCategoryPlus ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft PX.mapDerivedCategoryPlus
      (Functor.isoWhiskerLeft fc.rightDerivedFunctorPlus
        (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus εY).symm) ≪≫
    asIso (Functor.whiskerLeft PX.mapDerivedCategoryPlus (derivedComparisonBaseChange S f)) ≪≫
    Functor.isoWhiskerLeft PX.mapDerivedCategoryPlus
      (Functor.isoWhiskerRight (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus εX)
        ff.rightDerivedFunctorPlus) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso PX εX)
      ff.rightDerivedFunctorPlus

/-- **The degreewise base change along an exact functor into `𝒜'`.** In the situation of
`derivedBaseChangeAlongIso`, taking cohomology in degree `i` of the identification at a complex
concentrated in degree zero gives

`R^i g ⋙ a_Y^{-1} ≅ a_X^{-1} ⋙ R^i f_{τ,*}`, where `a^{-1} = P ⋙ ε^{-1}`.

The two exact functors `a^{-1}` commute with cohomology and with complexes concentrated in one
degree, and `Stacks.DerivedIndexing.rightDerivedIso` identifies the degree-`i` cohomology of a
right derived functor at an object in degree zero with Mathlib's `R^i`. -/
def higherBaseChangeAlongIso [EnoughInjectives A'] (hPX : ∀ F : A, S.weakSerre X (PX.obj F))
    (β : g.rightDerivedFunctorPlus ⋙ PY.mapDerivedCategoryPlus ≅
      PX.mapDerivedCategoryPlus ⋙
        (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlus) (i : ℕ) :
    g.rightDerived i ⋙ (PY ⋙ abelianComparisonPullback S.fineCoverage S.coarseCoverage Y) ≅
      (PX ⋙ abelianComparisonPullback S.fineCoverage S.coarseCoverage X) ⋙
        (overPushforward S.fineCoverage.toGrothendieck f).rightDerived i := by
  let aY := PY ⋙ abelianComparisonPullback S.fineCoverage S.coarseCoverage Y
  let aX := PX ⋙ abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let ff := overPushforward S.fineCoverage.toGrothendieck f
  let single := DerivedCategory.Plus.singleFunctor A 0
  let Hi := DerivedCategory.Plus.homologyFunctor
    (AbelianSheaves S.fineCoverage.toGrothendieck Y) (i : ℤ)
  -- `a^{-1}` commutes with cohomology on `D⁺`.
  let eH : aY.mapDerivedCategoryPlus ⋙ Hi ≅
      DerivedCategory.Plus.homologyFunctor A' (i : ℤ) ⋙ aY :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι (aY.mapDerivedCategoryHomologyIso (i : ℤ))
  -- `a^{-1}` commutes with complexes concentrated in degree zero on `D⁺`.
  let eS : single ⋙ aX.mapDerivedCategoryPlus ≅
      aX ⋙ DerivedCategory.Plus.singleFunctor (AbelianSheaves S.fineCoverage.toGrothendieck X) 0 :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).preimageIso
      (aX.mapDerivedCategorySingleFunctor 0)
  let Φ := derivedBaseChangeAlongIso S f PX PY g hPX β
  exact (Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso g i) aY) ≪≫
    (Functor.isoWhiskerLeft (single ⋙ g.rightDerivedFunctorPlus) eH).symm ≪≫
    Functor.isoWhiskerLeft single (Functor.isoWhiskerRight Φ Hi) ≪≫
    Functor.isoWhiskerRight eS (ff.rightDerivedFunctorPlus ⋙ Hi) ≪≫
    Functor.isoWhiskerLeft aX (Stacks.DerivedIndexing.rightDerivedIso ff i).symm

end BaseChange

end CohomologyComparison

end Stacks.ComparingTopologies
