module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact

/-!
# The higher direct images of a quasi-coherent module along an affine morphism vanish

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝓕` be a quasi-coherent `𝒪_X`-module.  Stacks 073H asserts that
`R^i f_*𝓕 = 0` for every `i > 0`.  This file proves it with no hypothesis.

The route is the source's, read on the small étale sites.  An affine morphism is representable,
so the direct image of modules along `f` is restriction along base change of étale charts,
`AlgebraicGeometry.Space.modulePushforwardChartIso`, which is the direct image along the
continuous functor `AlgebraicGeometry.Space.smallBaseChange` of the small étale sites.  For such
a direct image Stacks 072W says that `R^i f_*𝓕` is the sheaf associated to the presheaf
`V ↦ H^i(V ×_Y X, 𝓕)`, so it vanishes as soon as `H^i(V ×_Y X, 𝓕) = 0` for the members `V` of a
covering family of each chart; that is
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`.  The
family is that of the affine charts, which cover every chart by Stacks 04JS.  Over an affine
chart `V` the base change `V ×_Y X` is again an affine chart, because `f` is affine
(`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`), and the cohomology of a quasi-coherent
module over an affine chart vanishes in positive degree
(`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isAffineChart`).

## Main results

* `AlgebraicGeometry.Space.generate_isAffineChart_mem_topology_of_isAlgebraicSpace`: the affine
  charts mapping to an étale chart of an algebraic space generate a covering sieve of it.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent`
  (**Stacks 073H**).

## Implementation notes

The degree is a natural number `n` with `0 < n`, in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`; in degree zero the derived functor is the direct image
itself, which does not vanish.  The module universe is the universe `u` of the structure rings,
because `AlgebraicGeometry.Space.modulePushforward` exists only there.  The local priority raise
of `SheafOfModules.instAbelian` is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishing.lean`; enough injectives at
the module universe `u` is supplied by name, `AlgebraicGeometry.Space.enoughInjectives_modules`,
since instance search otherwise commits to a candidate at the module universe `max (u + 1) w`.

## References

* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The affine charts mapping to an étale chart of an algebraic space generate a covering sieve
of it.**  This is the cover-density half of Stacks 04JS,
`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`: every member of the sieve
covered by the images of affine charts factors through an affine chart. -/
theorem generate_isAffineChart_mem_topology_of_isAlgebraicSpace
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtale B S hS F) :
    Sieve.generate (fun (W : SmallEtale B S hS F) (_ : W ⟶ V) ↦ IsAffineChart B S hS F W) ∈
      SmallEtale.topology B S hS F V := by
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    ((AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2.isCoverDense'.is_cover V)
  rintro T g ⟨⟨A, lift, map, fac⟩⟩
  exact ⟨_, lift, map, A.property, fac⟩

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 073H.** Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and let
`𝓕` be a quasi-coherent `𝒪_X`-module.  Then `R^n f_*𝓕 = 0` for every `n > 0`.

The direct image along the representable `f` is the direct image along base change of étale
charts (`AlgebraicGeometry.Space.modulePushforwardChartIso`); by Stacks 072W its higher direct
images vanish once the cohomology of `𝓕` vanishes over the base changes of a covering family of
each chart of `Y`; the affine charts form such a family, their base changes are affine charts of
`X` because `f` is affine, and over an affine chart a quasi-coherent module has no higher
cohomology. -/
@[stacks 073H]
theorem isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS f).rightDerived n).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have : EnoughInjectives (SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2)) :=
    enoughInjectives_modules B S hS X.1 X.2
  have hrep := relativelyRepresentable_of_isAffineHom B S hS f hf
  have hadd : (smallBaseChangeModulePushforward.{u, u} B S hS f hrep).Additive :=
    Stacks.SheafOfModules.pushforward_additive _
  refine IsZero.of_iso ?_
    ((@Functor.rightDerivedIsoOfNatIso (Modules.{u, u} B S hS X.1 X.2) _ _
      (hasInjectiveResolutions_modules B S hS X.1 X.2) (Modules.{u, u} B S hS Y.1 Y.2) _ _ _ _
      (modulePushforward_additive B S hS f) hadd (modulePushforwardChartIso B S hS f hrep)
      n).app F)
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve.{
      u, u + 1, u, u + 1, u, u}
    (smallBaseChange B S hS f hrep) _ _ (smallBaseChangeSharp B S hS f hrep) n F
    (fun V ↦ ⟨_, generate_isAffineChart_mem_topology_of_isAlgebraicSpace B S hS Y.1 Y.2 V,
      fun W _ hW ↦ ?_⟩)
  exact isZero_rightDerived_evaluation_of_isAffineChart B S hS X.1 X.2 F hF _
    (isAffine_smallBaseChange_obj B S hS f hrep hf W hW) n hn

end AlgebraicGeometry.Space

end
