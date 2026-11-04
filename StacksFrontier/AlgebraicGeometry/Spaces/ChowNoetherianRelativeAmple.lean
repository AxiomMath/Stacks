module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# The morphism `Z ⟶ ℙⁿ_Y ⟶ Y` of Chow's lemma is proper

In Lemmas 088R and 088S (Chow's lemma for algebraic spaces) the space `Z` comes with a closed
immersion `Z ⟶ ℙⁿ_Y`. This file records that the composite `Z ⟶ ℙⁿ_Y ⟶ Y` is proper: the
projection `ℙⁿ_Y ⟶ Y` is the base change of the proper `ℙⁿ_S ⟶ S`, and a closed immersion is
proper. It is one factor of Stacks Remark 088T,
`Space.exists_isRelativelyAmple_of_isAdmissibleBlowup_of_projectiveSpaceImmersion`.

## Main results

* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.isProper_hom`: `Z ⟶ ℙⁿ_Y ⟶ Y` is proper.

## References

* [Stacks Project, Tag 088T](https://stacks.math.columbia.edu/tag/088T)
* [Stacks Project, Tag 088R](https://stacks.math.columbia.edu/tag/088R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ProjectiveSpaceImmersion

variable {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)} {X Y : AlgebraicSpaces B S hS}

/-- The morphism `X ⟶ ℙⁿ_Y ⟶ Y` of a closed immersion into projective space is proper. -/
theorem isProper_hom (D : ProjectiveSpaceImmersion B S hS n hP X Y) :
    IsProper B S hS D.hom.hom := by
  have hproj : IsProper B S hS D.proj.hom :=
    isProper_of_isPullback B S hS D.projSpace.2
      (schemeSpace (projectiveSpaceSiteObj B S hS n hP)).2 Y.2
      (schemeSpace (baseSiteObj B S hS)).2 D.isPullback.flip
      (isProper_yoneda_map B S hS (projectiveSpaceSiteObjToBase B S hS n hP)
        (isProper_projectiveSpaceOver n S))
  exact isProper_comp B S hS X.2 D.projSpace.2 Y.2 D.imm.hom D.proj.hom
    (isProper_of_isClosedImmersion B S hS X.2 D.projSpace.2 D.imm.hom D.imm_isClosedImmersion)
    hproj

end ProjectiveSpaceImmersion

end AlgebraicGeometry.Space

end
