module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleProper
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# The projective bundle of a good algebraic space

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module. The
projective bundle `π : P = 𝐏(ℰ) ⟶ X` of Section 0ERT (`AlgebraicGeometry.Space.projectiveBundle`)
is again good over the base.

## Main results

* `AlgebraicGeometry.Space.isGood_projectiveBundleProj_comp`: the projective bundle of a good
  algebraic space is good, with the projection followed by the structure morphism of `X` as
  structure morphism.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
  {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)
  (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
  [E.IsQuasicoherentOnSite] (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The projective bundle of a finite locally free module on a good algebraic space is good over
the base, with the projection followed by the structure morphism of `X` as structure morphism. -/
theorem isGood_projectiveBundleProj_comp :
    D.IsGood ((projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree).hom ≫ sX) := by
  have hprop := isProper_projectiveBundleProj (X := ⟨X, hX.1⟩) E hfree
  exact ⟨(projectiveBundle (X := ⟨X, hX.1⟩) E hfree).2,
    isQuasiSeparated_comp D.site D.base D.base_mem
      (projectiveBundle (X := ⟨X, hX.1⟩) E hfree).2 hX.1 _ sX
      (isQuasiSeparated_of_isSeparated D.site D.base D.base_mem hprop.1) hX.2.1,
    isLocallyOfFiniteType_comp D.site D.base D.base_mem
      (projectiveBundle (X := ⟨X, hX.1⟩) E hfree).2 hX.1 D.isAlgebraicSpace _ sX
      hprop.2.1.1 hX.2.2⟩

end AlgebraicGeometry.Space

end
