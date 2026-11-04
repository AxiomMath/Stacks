module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BoundedBelowComparisonEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons

/-!
# The derived change-of-topology direct image reflects isomorphisms

Situation 0EZ3 fixes a finer coverage `τ` and a coarser coverage `τ'` on a category `C`. Write
`ε_X : Sh(C_τ/X) ⟶ Sh(C_{τ'}/X)` for the change-of-topology morphism at an object `X`. Its
direct image `ε_{X,*}` is fully faithful, since it keeps the underlying presheaf. So the
counit of the derived adjunction `ε_X^{-1} ⊣ Rε_{X,*}` on bounded below derived categories is
invertible, which makes

`Rε_{X,*} : D⁺(C_τ/X) ⥤ D⁺(C_{τ'}/X)`

fully faithful. In particular it reflects isomorphisms. This is the remark that closes the
proof of Stacks 0DDS part (5). There it is stated for a morphism `a_Y^{-1}L ⟶ M` and proved by
induction on degrees; the source of the morphism plays no role.

The file also records the two consequences of `(V_n)` for every `n` that Stacks 0DDS part (1)
reads off in the coarse-to-fine direction. For `ℱ` in `𝒜'_X`, the unit
`ℱ ⟶ ε_{X,*} ε_X^{-1} ℱ` is invertible, and `R^i ε_{X,*}(ε_X^{-1} ℱ) = 0` for `i > 0`. It
also records the derived square of topoi on bounded below derived categories, which is the
first step of the computation in the proof of Stacks 0DDS part (5).

## Main results

All in the namespace `Stacks.ComparingTopologies.CohomologyComparison`.

* `derivedComparisonPushforwardFullyFaithful`: `Rε_{X,*}` is fully faithful on `D⁺`.
* `isIso_of_isIso_derivedComparisonPushforward_map`: a morphism of `D⁺(C_τ/X)` whose image
  under `Rε_{X,*}` is invertible is invertible.
* `isZero_rightDerived_abelianComparisonPullback`: `R^i ε_{X,*}(ε_X^{-1} ℱ) = 0` for `ℱ` in
  `𝒜'_X` and `i > 0`.
* `derivedPlusComparisonSquareIso`: `Rf_{τ,*} ⋙ Rε_{Y,*} ≅ Rε_{X,*} ⋙ Rf_{τ',*}` on bounded
  below derived categories.

## Implementation notes

The derived categories are those of `HasDerivedCategory.standard`. The derived adjunction
`Stacks.ComparingTopologies.derivedComparisonAdjunction` is defined in that model, and so is
`Stacks.ComparingTopologies.isIso_derivedComparisonUnit_app`.

## References

* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

namespace CohomologyComparison

/-- **`Rε_{X,*}` is fully faithful on bounded below derived categories.** The counit of the
derived adjunction `ε_X^{-1} ⊣ Rε_{X,*}` is invertible at every object, because `ε_{X,*}` is fully
faithful. -/
def derivedComparisonPushforwardFullyFaithful (S : CohomologyComparison C) (X : C) :
    (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).rightDerivedFunctorPlus.FullyFaithful :=
  haveI : ∀ K, IsIso ((derivedComparisonAdjunction S X).counit.app K) :=
    isIso_derivedComparisonAdjunction_counit_app S X
  haveI : IsIso (derivedComparisonAdjunction S X).counit := NatIso.isIso_of_isIso_app _
  (derivedComparisonAdjunction S X).fullyFaithfulROfIsIsoCounit

/-- **`Rε_{X,*}` reflects isomorphisms of `D⁺(C_τ/X)`.** A morphism of `D⁺(C_τ/X)` whose image
under `Rε_{X,*}` is invertible is invertible. -/
theorem isIso_of_isIso_derivedComparisonPushforward_map (S : CohomologyComparison C) (X : C)
    {K L : DerivedCategory.Plus (AbelianSheaves S.fineCoverage.toGrothendieck X)} (α : K ⟶ L)
    (hα : IsIso ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).rightDerivedFunctorPlus.map α)) :
    IsIso α :=
  (derivedComparisonPushforwardFullyFaithful S X).isIso_of_isIso_map α

/-- For `ℱ` in `𝒜'_X`, the sheaf `ε_X^{-1} ℱ` on the finer localized site lies in `𝒜_X`. -/
theorem fineWeakSerre_abelianComparisonPullback_obj (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}) (hF : S.weakSerre X F) :
    S.fineWeakSerre X ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj F) :=
  ⟨F, hF, ⟨Iso.refl _⟩⟩

/-- **The higher change-of-topology direct images of `ε_X^{-1} ℱ` vanish.** For `ℱ` in `𝒜'_X`
and `i > 0`, `R^i ε_{X,*}(ε_X^{-1} ℱ) = 0`. This is `(V_n)` for every `n` (Stacks 0EZF) at the
sheaf `ε_X^{-1} ℱ` of `𝒜_X`. -/
theorem isZero_rightDerived_abelianComparisonPullback (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}) (hF : S.weakSerre X F)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).rightDerived i).obj
        ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj F)) :=
  S.vanishingCondition_all i X _ (fineWeakSerre_abelianComparisonPullback_obj S X F hF) i hi le_rfl

/-- **The derived square of topoi on bounded below derived categories.** For a morphism
`f : X ⟶ Y` of `C`,

`Rf_{τ,*} ⋙ Rε_{Y,*} ≅ Rε_{X,*} ⋙ Rf_{τ',*}`

as functors `D⁺(C_τ/X) ⥤ D⁺(C_{τ'}/Y)`. The two underived composites are one and the same functor,
`Stacks.ComparingTopologies.abelianComparisonPushforward_square`. In each composite the first
factor preserves injective objects, being a right adjoint of an exact functor, so each derived
composite is the right derived functor of that common composite (Stacks 015M). -/
def derivedPlusComparisonSquareIso (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) :
    (overPushforward S.fineCoverage.toGrothendieck f).rightDerivedFunctorPlus ⋙
        (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine Y).rightDerivedFunctorPlus ≅
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).rightDerivedFunctorPlus ⋙
        (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlus :=
  let εX := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let εY := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine Y
  let fc := overPushforward S.coarseCoverage.toGrothendieck f
  let ff := overPushforward S.fineCoverage.toGrothendieck f
  letI : εX.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
  let e₁ : (ff ⋙ εY).rightDerivedFunctorPlus ≅
      ff.rightDerivedFunctorPlus ⋙ εY.rightDerivedFunctorPlus :=
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic ff εY fun I hI ↦
      Functor.rightAcyclic_obj_of_preservesInjectiveObjects ff εY I hI
  let e₂ : (εX ⋙ fc).rightDerivedFunctorPlus ≅
      εX.rightDerivedFunctorPlus ⋙ fc.rightDerivedFunctorPlus :=
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic εX fc fun I hI ↦
      Functor.rightAcyclic_obj_of_preservesInjectiveObjects εX fc I hI
  let e₀ : (ff ⋙ εY).rightDerivedFunctorPlus ≅ (εX ⋙ fc).rightDerivedFunctorPlus :=
    Iso.refl _
  e₁.symm ≪≫ e₀ ≪≫ e₂

end CohomologyComparison

end Stacks.ComparingTopologies
