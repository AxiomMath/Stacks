module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.CohomologicalDescent

/-!
# The derived unit of the projection from the big to the small étale site

Let `S` be a scheme in a big étale site and `π_S` the projection from the big étale topos over
`S` to the small étale topos of `S`. Its inverse image `π_S⁻¹` and its direct image
`π_{S,*} = i_S⁻¹` on abelian sheaves are exact
(`AlgebraicGeometry.projectionInverseImage_exact`, `AlgebraicGeometry.projectionRestriction_exact`),
so on unbounded derived categories they are computed termwise; for `π_{S,*}` the termwise functor
is the right derived functor `Rπ_{S,*}`. This file proves Stacks 0DDI: for every `K` in the
unbounded derived category `D(S_étale)` the map `K ⟶ Rπ_{S,*}π_S⁻¹K` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.projectionDerivedDirectImage` and
  `AlgebraicGeometry.projectionDerivedInverseImage` — `Rπ_{S,*}` and `π_S⁻¹` on unbounded derived
  categories.
* `AlgebraicGeometry.projectionDerivedAdjunctionUnit` — the map `K ⟶ Rπ_{S,*}π_S⁻¹K`.

## Main results

* `AlgebraicGeometry.projectionDerivedDirectImage_isRightDerivedFunctor` — the termwise functor is
  the right derived functor of `π_{S,*}`.
* `AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_Q` — on a complex, the map is the image of
  the termwise unit of `π_S⁻¹ ⊣ π_{S,*}`.
* `AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_isIso` — Stacks 0DDI.

## Implementation notes

The map is `AlgebraicGeometry.projectionDerivedUnit` (the termwise unit, localized, with target
the functor induced by the composite `π_{S,*} ∘ π_S⁻¹`), followed by the identification
`Stacks.DerivedFunctor.mapDerivedCategoryCompIso` of `Rπ_{S,*} ∘ π_S⁻¹` with that functor. It is
invertible because `AlgebraicGeometry.projectionDerivedUnit` is
(`AlgebraicGeometry.projectionDerivedUnit_isIso`): the unit on abelian sheaves is an isomorphism,
the small-site inclusion being fully faithful and cocontinuous.

## References

* [Stacks Project, Lemma 59.99.4 (Tag 0DDI)](https://stacks.math.columbia.edu/tag/0DDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] instHasSheafifySmallEtaleTopologyAddCommGrpCat
  instHasSheafifyBigEtaleOverTopologyAddCommGrpCat instAbelianSmallSheaves instAbelianBigSheaves
  instIsRightAdjointSmallSheavesBigSheavesProjectionRestriction
  instPreservesFiniteLimitsSmallSheavesBigSheavesProjectionPullback
  instPreservesFiniteColimitsSmallSheavesBigSheavesProjectionPullback
  instPreservesFiniteLimitsBigSheavesSmallSheavesProjectionRestriction
  instPreservesFiniteColimitsBigSheavesSmallSheavesProjectionRestriction
  instAdditiveSmallSheavesBigSheavesProjectionPullback
  instAdditiveBigSheavesSmallSheavesProjectionRestriction

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `Rπ_{S,*}` on the unbounded derived category: the functor
`D((Sch/S)_étale) ⥤ D(S_étale)` induced by the direct image `π_{S,*}` (restriction to the small
étale site). Since `π_{S,*}` is exact (`AlgebraicGeometry.projectionRestriction_exact`), it is
computed termwise on unbounded complexes, and it is the right derived functor of `π_{S,*}`:
`AlgebraicGeometry.projectionDerivedDirectImage_isRightDerivedFunctor`. -/
abbrev projectionDerivedDirectImage :
    DerivedCategory (bigSheaves.{u, v} B S hS) ⥤ DerivedCategory (smallSheaves.{u, v} B S hS) :=
  (projectionRestriction.{u, v} B S hS).mapDerivedCategory

/-- `π_S⁻¹` on the unbounded derived category: the functor `D(S_étale) ⥤ D((Sch/S)_étale)`
induced by the exact inverse image (`AlgebraicGeometry.projectionInverseImage_exact`), applied
termwise to complexes; it is also its left derived functor,
`AlgebraicGeometry.projectionDerivedInverseImage_isLeftDerivedFunctor`. -/
abbrev projectionDerivedInverseImage :
    DerivedCategory (smallSheaves.{u, v} B S hS) ⥤ DerivedCategory (bigSheaves.{u, v} B S hS) :=
  (projectionInverseImage.{u, v} B S hS).mapDerivedCategory

/-- The termwise functor `AlgebraicGeometry.projectionDerivedDirectImage` is the right derived
functor `Rπ_{S,*}` of `π_{S,*}` on unbounded complexes, with respect to quasi-isomorphisms: as
`π_{S,*}` is exact, it sends quasi-isomorphisms to quasi-isomorphisms, so the localization of
the termwise functor is a (pointwise) left Kan extension. -/
theorem projectionDerivedDirectImage_isRightDerivedFunctor :
    (projectionDerivedDirectImage.{u, v} B S hS).IsRightDerivedFunctor
      (projectionRestriction.{u, v} B S hS).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso (bigSheaves.{u, v} B S hS) (.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (projectionRestriction.{u, v} B S hS).mapDerivedCategoryFactors

/-- The termwise functor `AlgebraicGeometry.projectionDerivedInverseImage` is the left derived
functor of `π_S⁻¹` on unbounded complexes, with respect to quasi-isomorphisms, `π_S⁻¹` being
exact. -/
theorem projectionDerivedInverseImage_isLeftDerivedFunctor :
    (projectionDerivedInverseImage.{u, v} B S hS).IsLeftDerivedFunctor
      (projectionInverseImage.{u, v} B S hS).mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (smallSheaves.{u, v} B S hS) (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (projectionInverseImage.{u, v} B S hS).mapDerivedCategoryFactors

/-- The map `K ⟶ Rπ_{S,*}π_S⁻¹K` on the unbounded derived category `D(S_étale)`: the unit of
`π_S⁻¹ ⊣ π_{S,*}` applied termwise and localized (`AlgebraicGeometry.projectionDerivedUnit`),
followed by the identification of `Rπ_{S,*} ∘ π_S⁻¹` with the functor induced by the composite.
On a complex it is the image of the termwise unit:
`AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_Q`. -/
def projectionDerivedAdjunctionUnit :
    𝟭 (DerivedCategory (smallSheaves.{u, v} B S hS)) ⟶
      projectionDerivedInverseImage.{u, v} B S hS ⋙ projectionDerivedDirectImage.{u, v} B S hS :=
  projectionInverseImageDerivedUnit.{u, v} B S hS ≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIso
      (projectionInverseImage.{u, v} B S hS) (projectionRestriction.{u, v} B S hS)).inv

/-- On the image of a complex `K`, the map `K ⟶ Rπ_{S,*}π_S⁻¹K`, read through the termwise
descriptions of `π_S⁻¹` and `Rπ_{S,*}`, is the image in the derived category of the unit
`K ⟶ π_{S,*}π_S⁻¹K` of `π_S⁻¹ ⊣ π_{S,*}` applied termwise. -/
theorem projectionDerivedAdjunctionUnit_app_Q
    (K : CochainComplex (smallSheaves.{u, v} B S hS) ℤ) :
    (projectionDerivedAdjunctionUnit.{u, v} B S hS).app (DerivedCategory.Q.obj K) ≫
      (projectionRestriction.{u, v} B S hS).mapDerivedCategory.map
        ((projectionInverseImage.{u, v} B S hS).mapDerivedCategoryFactors.hom.app K) ≫
      (projectionRestriction.{u, v} B S hS).mapDerivedCategoryFactors.hom.app
        (((projectionInverseImage.{u, v} B S hS).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        ((Dualizing.Coreflection.complexUnit
          (projectionInverseImage.{u, v} B S hS ⋙ projectionRestriction.{u, v} B S hS)
          ((SmallEtale.inclusion B S hS).sheafAdjunctionContinuous
            AddCommGrpCat.{max (u + 1) v} _ _).unit).app K) := by
  have h := Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Q
    (projectionInverseImage.{u, v} B S hS) (projectionRestriction.{u, v} B S hS) K
  have h' : (projectionRestriction.{u, v} B S hS).mapDerivedCategory.map
        ((projectionInverseImage.{u, v} B S hS).mapDerivedCategoryFactors.hom.app K) ≫
      (projectionRestriction.{u, v} B S hS).mapDerivedCategoryFactors.hom.app
        (((projectionInverseImage.{u, v} B S hS).mapHomologicalComplex (.up ℤ)).obj K) =
      (Stacks.DerivedFunctor.mapDerivedCategoryCompIso (projectionInverseImage.{u, v} B S hS)
          (projectionRestriction.{u, v} B S hS)).hom.app (DerivedCategory.Q.obj K) ≫
        (projectionInverseImage.{u, v} B S hS ⋙
          projectionRestriction.{u, v} B S hS).mapDerivedCategoryFactors.hom.app K := by
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    refine congrArg (_ ≫ ·) ?_
    exact (Category.comp_id _).symm
  rw [h']
  simp only [projectionDerivedAdjunctionUnit, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [projectionInverseImageDerivedUnit, projectionDerivedUnit,
    Dualizing.Coreflection.derivedUnit_app_Q]
  simp

/-- **Stacks 0DDI.** Let `S` be a scheme. For every `K` in the unbounded derived category
`D(S_étale)` of abelian sheaves on the small étale site, the map `K ⟶ Rπ_{S,*}π_S⁻¹K` is an
isomorphism, where `π_S` is the projection from the big étale topos over `S` to the small
étale topos of `S`. Here `π_S⁻¹` and `Rπ_{S,*}` are the functors induced on unbounded derived
categories by the exact functors `π_S⁻¹` and `π_{S,*} = i_S⁻¹`; `Rπ_{S,*}` is the right derived
functor of `π_{S,*}` (`AlgebraicGeometry.projectionDerivedDirectImage_isRightDerivedFunctor`),
and the map is the image of the termwise unit of `π_S⁻¹ ⊣ π_{S,*}`
(`AlgebraicGeometry.projectionDerivedAdjunctionUnit_app_Q`). The proof is Stacks': both functors
are exact and the unit `id ⟶ π_{S,*} ∘ π_S⁻¹` on abelian sheaves is an isomorphism. -/
@[stacks 0DDI "the derived unit `K ⟶ Rπ_{S,*}π_S⁻¹K` is an isomorphism for every `K` in the \
unbounded `D(S_étale)`; `π_S⁻¹`, `Rπ_{S,*}` are the functors induced by the exact functors, \
`Rπ_{S,*}` being the right derived functor of `π_{S,*}`"]
theorem projectionDerivedAdjunctionUnit_app_isIso
    (K : DerivedCategory (smallSheaves.{u, v} B S hS)) :
    IsIso ((projectionDerivedAdjunctionUnit.{u, v} B S hS).app K) := by
  have := projectionInverseImageDerivedUnit_isIso.{u, v} B S hS
  rw [projectionDerivedAdjunctionUnit, NatTrans.comp_app]
  infer_instance

end AlgebraicGeometry
