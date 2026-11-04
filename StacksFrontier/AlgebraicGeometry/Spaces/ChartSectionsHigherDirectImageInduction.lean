module

public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplexLowerDegrees
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBasePushforwardInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Sections of a higher direct image over an affine chart, from the lower degrees

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `F` be an `𝒪_X`-module, and let `V` be an affine étale chart of `Y`.  The
degree-`n` derived sections over `V` of the direct image are the sections over `V` of the
degree-`n` higher direct image,

`R^n (Γ(V, f_*−)) (F) ≅ Γ(V, R^n f_*F)`,

as soon as the higher direct images `R^q f_*F` are quasi-coherent in the degrees `q < n`.

This is the degeneration of the Leray spectral sequence of `f` read over a single affine chart:
`f_*` of an injective resolution of `F` is a complex of modules acyclic for the sections over `V`
(Stacks 072Z at the chart), whose cohomology objects `R^q f_*F` are acyclic for the sections in
the degrees `q < n` by their quasi-coherence.

In degree zero the identification holds with no hypothesis.  Under quasi-coherence of the
`R^q f_*F` (Stacks 0720) in every degree it is Stacks 08EX,
`AlgebraicGeometry.Space.cohomologyChartIsoSectionsHigherDirectImage`.

## Main results

* `AlgebraicGeometry.Space.acyclic_evaluation_of_isQuasicoherentOnSite`: over an affine chart, a
  quasi-coherent module is acyclic for the sections over that chart.
* `AlgebraicGeometry.Space.chartEvaluationRightDerivedIso`: **the identification above**, in
  degree `n`, granted quasi-coherence of the higher direct images in the degrees `q < n` only.

## Implementation notes

The local priority raise of `SheafOfModules.instAbelian` is needed because instance search for
`CategoryTheory.Abelian` on the modules at module universe `u` otherwise commits to the
module-universe-`max u v r w` instances in the import closure and then fails on the universe
constraint.

## References

* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Over an affine chart, a quasi-coherent module is acyclic for the sections over that
chart.** -/
theorem acyclic_evaluation_of_isQuasicoherentOnSite (V : SmallEtale B S hS Y.1)
    (hV : IsAffineChart B S hS Y.1 V) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : M.IsQuasicoherentOnSite) :
    have := enoughInjectives_modules B S hS Y.1 Y.2
    Stacks.RightDerivedComp.acyclic (SheafOfModules.evaluation
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)) M :=
  have := enoughInjectives_modules B S hS Y.1 Y.2
  fun p hp => isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS Y.1 Y.2 V hV M hM p hp

/-- **The sections over an affine chart of the degree-`n` higher direct image are the degree-`n`
derived sections of the direct image**, granted quasi-coherence of the higher direct images in
the degrees strictly below `n`:

`R^n (Γ(V, f_*−)) (F) ≅ Γ(V, R^n f_*F)`.

At `n = 0` the hypothesis is vacuous. -/
def chartEvaluationRightDerivedIso (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V) (n : ℕ)
    (hqc : ∀ q < n,
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      (((modulePushforward B S hS f).rightDerived q).obj F).IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS f ⋙ SheafOfModules.evaluation
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
          (op V)).rightDerived n).obj F ≅
      (SheafOfModules.evaluation
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)).obj
        (((modulePushforward B S hS f).rightDerived n).obj F) :=
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  (injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f ⋙
      SheafOfModules.evaluation
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)) n ≪≫
    Stacks.Cohomology.RightDerivedCoEdge.homologyIsoMapHomologyOfAcyclicLt
      (SheafOfModules.evaluation
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V))
      (Stacks.RightDerivedComp.mapCocomplex (modulePushforward B S hS f)
        (injectiveResolution F))
      (fun q => isZero_rightDerived_evaluation_modulePushforward_of_injective B S hS f _
        ((injectiveResolution F).injective q) V)
      n
      (fun q hq => Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso _
        ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) q)
        (acyclic_evaluation_of_isQuasicoherentOnSite B S hS V hV _ (hqc q hq))) ≪≫
    (SheafOfModules.evaluation
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)).mapIso
      ((injectiveResolution F).isoRightDerivedObj (modulePushforward B S hS f) n).symm

end AlgebraicGeometry.Space

end

end
