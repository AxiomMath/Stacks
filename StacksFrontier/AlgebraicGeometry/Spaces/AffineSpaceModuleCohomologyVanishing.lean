module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleCohomologyVanishing
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsTerminalObject
import StacksCore.Tactic.StacksAttribute

/-!
# The higher cohomology of a quasi-coherent module on an affine algebraic space vanishes

Let `Y` be an **affine** algebraic space over a scheme `S` and let `𝓖` be a quasi-coherent
`𝒪_Y`-module on the small étale site of `Y`.  Then `H^p(Y, 𝓖) = 0` for every `p > 0`.

This is the small étale half of **Stacks 03DW** in the shape the rest of this development
consumes: the vanishing of the right derived functors of
`Stacks.Cohomology.SiteModules.globalSectionsFunctor` at module universe `u`.  It is the
hypothesis the Leray degeneration of **Stacks 08EX** calls `hcoh` once the higher direct images
are known to be quasi-coherent, and the `h03DW` the collapse of **Stacks 0D2U** asks for over an
affine base.

Two things go into it, and neither is new mathematics.

* The vanishing of the derived *sections over an affine chart*,
  `AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`, which is
  unconditional and is the keystone of the unconditional **Stacks 073H** of
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardUnconditional`.
* The identification of global sections with sections over a *terminal* chart,
  `Stacks.Cohomology.SiteModules.globalSectionsIsoEvaluation`, together with the fact that an
  affine algebraic space has a terminal chart whose scheme is affine,
  `AlgebraicGeometry.Space.exists_isTerminal_isAffine_chart`.

So the affine vanishing on the small étale site of an algebraic space is *not* missing from this
development, contrary to what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishing.lean` and
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/EtaleAcyclicity.lean` say: what was
missing was the passage from a chart to the whole site, and for an affine space that passage is
terminality of one chart.

## Main definitions

* `AlgebraicGeometry.Space.rightDerivedGlobalSectionsIsoEvaluationChart`: the derived global
  sections of `𝒪_Y`-modules are the derived sections over a terminal chart, read over the ring of
  global functions and lifted.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_of_isTerminalChart`: the derived
  global sections vanish wherever the derived sections over a terminal chart do.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSections_of_isAffineSpace`: **the higher
  cohomology of a quasi-coherent module on an affine algebraic space vanishes.**

## Implementation notes

The module universe is `u`, the universe of the structure rings, because that is where
`AlgebraicGeometry.Space.Modules` and the affine chart vanishing live; the cohomology modules
themselves lie in `Type (u + 1)`, a compatible family being indexed by the objects of the site,
and that is where the universe lift in the statement comes from.

Restriction of scalars along `Stacks.Cohomology.SiteModules.globalSectionEval` and the universe
lift are both exact and additive, so `CategoryTheory.Functor.rightDerivedCompIso` pulls them out
of the derived functor and they take a zero object to a zero object.  The additivity of
`SheafOfModules.evaluation` and of the global-sections functor at this seating is found by
instance search once `SheafOfModules.instAbelian` is raised, exactly as in the rest of the
algebraic-spaces cohomology files.

No `@[stacks 03DW]` attribute is attached.  The tag's covering set in this repository is
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` for the comparison clause and
`AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv` for degree zero of clause (1);
the statement below is about an algebraic space rather than a scheme, and is a consequence of the
chart vanishing rather than a new reading of the tag.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived global sections of `𝒪_X`-modules are the derived sections over a terminal
chart**, read over the ring of global regular functions and lifted to the universe of the
compatible families.

This is `Stacks.Cohomology.SiteModules.globalSectionsIsoEvaluation` right-derived:
`CategoryTheory.Functor.rightDerivedIsoOfNatIso` carries the underived identification across, and
`CategoryTheory.Functor.rightDerivedCompIso` pulls the exact restriction of scalars and universe
lift back out. -/
def rightDerivedGlobalSectionsIsoEvaluationChart (X : AlgebraicSpaces B S hS)
    {V : SmallEtale B S hS X.1} (hV : IsTerminal V) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p ≅
      (SheafOfModules.evaluation
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op V)).rightDerived p ⋙
        ModuleCat.restrictScalars (globalSectionEval
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op V)) ⋙
        ModuleCat.uliftFunctor.{u + 1} _) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  Functor.rightDerivedIsoOfNatIso
    (globalSectionsIsoEvaluation
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) hV) p ≪≫
  Functor.rightDerivedCompIso
    (SheafOfModules.evaluation
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op V))
    (ModuleCat.restrictScalars (globalSectionEval
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op V)) ⋙
      ModuleCat.uliftFunctor.{u + 1} _) p

/-- **The derived global sections vanish wherever the derived sections over a terminal chart
vanish.**  Restriction of scalars and the universe lift are additive, so they take a zero object
to a zero object. -/
theorem isZero_rightDerived_globalSections_of_isTerminalChart (X : AlgebraicSpaces B S hS)
    {V : SmallEtale B S hS X.1} (hV : IsTerminal V) (M : Modules.{u, u} B S hS X.1 X.2) (p : ℕ)
    (h : have := hasInjectiveResolutions_modules B S hS X.1 X.2
      IsZero (((SheafOfModules.evaluation
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        (op V)).rightDerived p).obj M)) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p).obj M) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  refine IsZero.of_iso ?_
    ((rightDerivedGlobalSectionsIsoEvaluationChart B S hS X hV p).app M)
  exact (ModuleCat.restrictScalars (globalSectionEval
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (op V)) ⋙
    ModuleCat.uliftFunctor.{u + 1} _).map_isZero h

/-- **The higher cohomology of a quasi-coherent module on an affine algebraic space vanishes.**

An affine algebraic space has a terminal étale chart whose scheme is affine, and over an affine
chart a quasi-coherent module has no positive-degree derived sections; global sections are the
sections over the terminal chart, so the derived global sections vanish too. -/
theorem isZero_rightDerived_globalSections_of_isAffineSpace (X : AlgebraicSpaces B S hS)
    (hX : IsAffineSpace B S hS X.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p).obj M) := by
  obtain ⟨V, ⟨hV⟩, hVaff⟩ := exists_isTerminal_isAffine_chart B S hS X hX
  exact isZero_rightDerived_globalSections_of_isTerminalChart B S hS X hV M p
    (isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS X.1 X.2 V hVaff M hM p hp)

end AlgebraicGeometry.Space

end

end
