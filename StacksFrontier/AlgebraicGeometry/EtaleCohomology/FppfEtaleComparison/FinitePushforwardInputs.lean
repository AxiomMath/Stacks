module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FiniteDirectImage

/-!
# The finite-morphism inputs of the fppf–étale comparison situation

Let `B` be a big fppf site and `(Sch/S)_étale` the étale site on the same category. Situation 0EZ3
for the fppf and étale topologies (Stacks 0F0H),
`AlgebraicGeometry.fppfEtaleCohomologyComparisonOfFinite`, is built from two facts about the
direct image `f_{big,*}` of abelian sheaves on the big étale sites along a finite morphism `f`:

* `f_{big,*}` is exact;
* `f_{big,*}π_X⁻¹F` is of the form `π_Y⁻¹G`, namely `π_Y⁻¹f_{small,*}F`.

These are the two inputs of the source's proof of Stacks 0DDJ (4). Both are proved, for the slice
topologies `AlgebraicGeometry.BigEtaleOver.topology`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FiniteDirectImage`. This file
moves them to the localized topologies of the situation through
`AlgebraicGeometry.fppfEtaleBigPushforwardTransportIso`. It then obtains the situation without
inputs, and from it the vanishing `R^iε_{X,*}(a_X⁻¹F) = 0` for `i > 0`, the second half of
Stacks 0DDS (1).

## Main results

* `fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite`: exactness of `f_{big,*}` for
  `f` finite.
* `fppfEtaleWeakSerre_overMapPushforward_of_finite`: `f_{big,*}π_X⁻¹F ∈ 𝒜'_Y` for `f` finite.
* `fppfEtaleCohomologyComparison`: Situation 0EZ3 for the fppf and étale topologies.
* `isZero_fppfBigEtaleAbelianPushforward_rightDerived_fppfSmallEtaleAbelianPullback`: the second
  half of Stacks 0DDS (1).

## References

* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0F0H](https://stacks.math.columbia.edu/tag/0F0H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}}

/-- `f_{big,*}` in the localized spelling of Situation 0EZ3 is the slice-topology `f_{big,*}`
conjugated by the identifications of `CategoryTheory.sheafEquivOfTopologyEq`. -/
def fppfEtaleOverMapPushforwardConjugateIso {X Y : B.Schemes} (f : X ⟶ Y) :
    (Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y) ≅
      (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
          AddCommGrpCat.{u + 1}).inverse ⋙
        ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (BigEtaleOver.topology (associatedBigEtaleSite B) Y.1 Y.2)
          (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2) ⋙
        (sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) Y.1 Y.2)
          AddCommGrpCat.{u + 1}).functor) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquivOfTopologyEq
      (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2)
        AddCommGrpCat.{u + 1}).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (fppfEtaleBigPushforwardTransportIso B f)

/-- **`f_{big,*}` is exact for `f` finite**, on abelian sheaves on the big étale sites with the
localized topologies of Situation 0EZ3: the slice-topology statement
`AlgebraicGeometry.bigEtaleAbelianPushforward_preservesFiniteColimits_of_isFinite` (Stacks 03QP
and 075A, as in the proof of Stacks 0DDJ (4)), transported along equivalences. -/
theorem fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite ⦃X Y : B.Schemes⦄
    (f : X ⟶ Y) (hf : fppfEtaleFinite B f) :
    PreservesFiniteColimits ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X)
      ((associatedBigEtaleSite B).topology.over Y)) := by
  have : IsFinite ((associatedBigEtaleSite B).inclusion.map f) := hf
  have := bigEtaleAbelianPushforward_preservesFiniteColimits_of_isFinite
    (associatedBigEtaleSite B) f
  exact preservesFiniteColimits_of_natIso (fppfEtaleOverMapPushforwardConjugateIso f).symm

/-- **`f_{big,*}π_X⁻¹F` lies in `𝒜'_Y` for `f` finite**: it is `π_Y⁻¹f_{small,*}F`, by the
base change isomorphism `π_Y⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_X⁻¹` of Stacks 0DDJ (1) for a finite
morphism, `AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_abelian_of_isFinite`. -/
theorem fppfEtaleWeakSerre_overMapPushforward_of_finite ⦃X Y : B.Schemes⦄ (f : X ⟶ Y)
    (hf : fppfEtaleFinite B f)
    (A : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    fppfEtaleWeakSerre B Y
      (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        ((associatedBigEtaleSite B).topology.over X)
        ((associatedBigEtaleSite B).topology.over Y)).obj
          ((fppfEtaleProjectionPullback B X).obj A)) := by
  have : IsFinite ((associatedBigEtaleSite B).inclusion.map f) := hf
  have := isIso_bigSmallEtaleBaseChange_abelian_of_isFinite (associatedBigEtaleSite B) f
  exact ⟨((associatedBigEtaleSite B).smallPushforward f AddCommGrpCat.{u + 1}).obj A,
    ⟨(sheafEquivOfTopologyEq (bigEtaleOver_topology_eq (associatedBigEtaleSite B) Y.1 Y.2)
        AddCommGrpCat.{u + 1}).functor.mapIso
        (asIso ((bigSmallEtaleBaseChange (associatedBigEtaleSite B) AddCommGrpCat.{u + 1} f
          (bigEtaleAbelianProjectionAdjunction (associatedBigEtaleSite B) X)
          (bigEtaleAbelianProjectionAdjunction (associatedBigEtaleSite B) Y)).app A)) ≪≫
      ((fppfEtaleBigPushforwardTransportIso B f).app _).symm⟩⟩

variable (B) in
/-- **Situation 0EZ3 for the fppf and étale topologies** (Stacks 0F0H), with the class of
finite morphisms and the classes `𝒜'_X` of sheaves `π_X⁻¹F`, its property (0EZ7) supplied by
`AlgebraicGeometry.fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite` and
`AlgebraicGeometry.fppfEtaleWeakSerre_overMapPushforward_of_finite`. -/
abbrev fppfEtaleCohomologyComparison :=
  fppfEtaleCohomologyComparisonOfFinite B
    fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite
    fppfEtaleWeakSerre_overMapPushforward_of_finite

variable (B) in
/-- **The higher direct images `R^iε_{X,*}(a_X⁻¹F)` vanish for `i > 0`**, the second half of
Stacks 0DDS (1), for every abelian sheaf `F` on `X_étale`. -/
theorem isZero_fppfBigEtaleAbelianPushforward_rightDerived_fppfSmallEtaleAbelianPullback
    (X : B.Schemes)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})
    (i : ℕ) (hi : 0 < i) :
    IsZero (((fppfBigEtaleAbelianPushforward B X).rightDerived i).obj
      ((fppfSmallEtaleAbelianPullback B X).obj F)) :=
  isZero_fppfBigEtaleAbelianPushforward_rightDerived_of_finite X
    fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite
    fppfEtaleWeakSerre_overMapPushforward_of_finite F i hi

end AlgebraicGeometry
