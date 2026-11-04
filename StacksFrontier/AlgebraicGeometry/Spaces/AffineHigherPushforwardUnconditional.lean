module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBaseChangePresieve
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# Higher direct images along an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝓕` be a quasi-coherent `𝒪_X`-module. Then `R^n f_* 𝓕 = 0` for `n > 0`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite`:
  `R^n f_* 𝓕 = 0` for an affine `f`, a quasi-coherent `𝓕` and `n > 0`.

## References

* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open Stacks.Cohomology.ModuleDirectImageOnACover in
/-- For an affine morphism `f : X ⟶ Y` of algebraic spaces over `S`, a quasi-coherent
`𝒪_X`-module `𝓕` and `n > 0`, the higher direct image vanishes: `R^n f_* 𝓕 = 0`. -/
@[stacks 073H]
theorem isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS f).rightDerived n).obj G) := by
  have hres := hasInjectiveResolutions_modules B S hS X.1 X.2
  have hf := relativelyRepresentable_of_isAffineHom B S hS f haff
  have := isContinuous_smallBaseChange B S hS f hf
  have : EnoughInjectives (SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2)) :=
    enoughInjectives_modules B S hS X.1 X.2
  have hadd : (SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f hf)).Additive :=
    inferInstance
  refine IsZero.of_iso (isZero_rightDerived_pushforward_of_presieve.{u, u + 1, u, u + 1, u, u}
    (smallBaseChange B S hS f hf) (smallEtaleRingSheaf B S hS X.1 X.2)
    (smallEtaleRingSheaf B S hS Y.1 Y.2) (smallBaseChangeSharp B S hS f hf) n G (fun V ↦ ?_))
    ((@Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso _ _ _ _ _ _ _ _ _
      (modulePushforward_additive B S hS f) hadd (modulePushforwardChartIso B S hS f hf) n).app G)
  obtain ⟨R, hR, hmem⟩ := exists_presieve_isAffine_smallBaseChange B S hS f hf haff V
  exact ⟨R, hR, fun W g hg ↦ isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS X.1
    X.2 ((smallBaseChange B S hS f hf).obj W) (hmem g hg).2 G hG n hn⟩

end AlgebraicGeometry.Space

end
