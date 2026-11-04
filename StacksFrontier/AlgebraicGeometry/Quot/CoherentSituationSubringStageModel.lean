module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAffineApproximation
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.TerminalSite
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemSiteConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Absolute Noetherian approximation of a separated morphism of finite presentation to an affine

Over the base `Spec ℤ` (the terminal scheme), let `T` be an affine object of the big fppf site
and write `Γ(T) = colim ℤ[i]` as the filtered colimit of its finitely generated subrings
`ℤ[i] ⊆ Γ(T)`, indexed by the finite subsets `i ⊆ Γ(T)`.  Then `T = lim Spec ℤ[i]`, each stage
`Spec ℤ[i]` is an affine Noetherian scheme of finite type over `ℤ`, and the system of the stages
satisfies the standing convention of Section 70.2 (Stacks 07SD) of the chapter on limits of
algebraic spaces.  Consequently, for a separated morphism of finite presentation `f : X ⟶ T` of
algebraic spaces there is a stage `j` and a separated morphism of finite presentation
`f_j : X_j ⟶ Spec ℤ[j]` of which `f` is the base change along `T ⟶ Spec ℤ[j]`: the morphism
descends by Stacks 07SK, and the descended morphism may be taken separated by Stacks 0851.

This is the step of absolute Noetherian approximation in the proofs of Stacks 09DS and 0DNE.

## Main definitions

The stages `AlgebraicGeometry.Space.finsetStage`, their cone and the system
`AlgebraicGeometry.Space.stageSystem` come from
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackAffineApproximation.lean`; this file adds:

* `AlgebraicGeometry.Space.subringStageSituation`: the stages with their limit `T`, as
  Situation 09RH.

## Main results

* `AlgebraicGeometry.Space.isNoetherian_subringStage`: every stage is Noetherian.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0851](https://stacks.math.columbia.edu/tag/0851)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### The inverse system of finitely generated subrings -/

section Stages

variable (R : Type u) [CommRing R]

/-- Every stage `Spec ℤ[i]` is a Noetherian scheme. -/
instance isNoetherian_subringStage (i : (Finset R)ᵒᵖ) :
    _root_.AlgebraicGeometry.IsNoetherian
      ((BigAffineFppf.toScheme B (⊤_ Scheme.{u}) hZ).obj (finsetStage hZ R i)) :=
  isNoetherian_specAdjoinFinsetDiagram_obj R i

end Stages

/-! ### An affine object of the site as the limit of the stages -/

section Cone

variable (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)

end Cone

/-! ### The stages as algebraic spaces -/

section Model

variable (T : BigAffineFppf B (⊤_ Scheme.{u}) hZ)

/-- The cone of represented presheaves with vertex `T` over the stages is a limit cone. -/
def isLimit_yoneda_subringStageCone :
    IsLimit (yoneda.mapCone ((BigAffineFppf.inclusion B (⊤_ Scheme.{u}) hZ).mapCone
      (finsetStageCone hZ T))) :=
  BigFppfOver.isLimitYonedaMapConeOfIsLimitToScheme (isLimit_finsetStageCone hZ T)

/-- **The stages `Spec ℤ[i]` of `Γ(T)` as Situation 09RH**, with limit `T` and chosen index
`j₀`. -/
def subringStageSituation (j₀ : Finset (affineRing hZ T)) :
    DescentSituation B (⊤_ Scheme.{u}) hZ hZ (Finset (affineRing hZ T)) where
  system := stageSystem hZ T
  algebraicSpace i := stageSystem_isAlgebraicSpace hZ T (op i)
  transition_affine m := stageSystem_isAffineHom hZ T m
  quasiCompact i := stageSystem_isQuasiCompactSpace hZ T (op i)
  quasiSeparated i := stageSystem_isAbsolutelyQuasiSeparated hZ T (op i)
  limitCone := yoneda.mapCone ((BigAffineFppf.inclusion B (⊤_ Scheme.{u}) hZ).mapCone
    (finsetStageCone hZ T))
  isLimit := isLimit_yoneda_subringStageCone hZ T
  limitAlgebraicSpace := isAlgebraicSpace_yoneda B _ hZ _
  base := j₀

/-- The inverse system of `subringStageSituation hZ T j₀` is `stageSystem hZ T`. -/
@[simp]
theorem subringStageSituation_system (j₀ : Finset (affineRing hZ T)) :
    (subringStageSituation hZ T j₀).system = stageSystem hZ T :=
  rfl

/-- The chosen index of `subringStageSituation hZ T j₀` is `j₀`. -/
@[simp]
theorem subringStageSituation_base (j₀ : Finset (affineRing hZ T)) :
    (subringStageSituation hZ T j₀).base = j₀ :=
  rfl

end Model

end AlgebraicGeometry.Space

end
