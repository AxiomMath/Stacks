module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GradedAlgebraChartRestriction

/-!
# Restricting a submodule of an `𝒪_X`-module to an étale scheme chart

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `M` be an `𝒪_X`-module and let
`V` be an étale chart of `X`.  The module `M` restricts to the Zariski site of the chart's scheme
by `AlgebraicGeometry.Space.restrictToChartScheme`; this file restricts a *submodule* of `M`
along the same chart.

The restriction is needed whenever a statement about submodules on an algebraic space is to be
compared with the case of schemes on a chart.  Its characteristic use is the spreading out of
Stacks 0829: a finite type quasi-coherent submodule found on a chart is to be compared with the
restriction of one defined on the whole space, and that comparison is a containment of two
submodules of one and the same module on the chart.

## Main definitions

* `AlgebraicGeometry.Space.restrictSubmoduleToChart`: the restriction of a submodule `N ⊆ M` to
  an étale scheme chart — the local closure of the sectionwise range of the restricted inclusion
  `N ⟶ M`.

## Main results

* `AlgebraicGeometry.Space.mem_restrictSubmoduleToChart`: a section of the restricted module lies
  in the restricted submodule exactly when it lies locally in the range of the restricted
  inclusion.  This holds by definition and is what makes the restriction usable.
* `AlgebraicGeometry.Space.app_mem_restrictSubmoduleToChart`: the restricted inclusion lands in
  the restricted submodule, so the restriction loses nothing.
* `AlgebraicGeometry.Space.restrictSubmoduleToChart_mono`: the restriction is monotone.  This is
  the property a comparison of two submodules on a chart rests on.

## Implementation notes

**Why the local closure of a range, and not a sectionwise image.**  The chart restriction of a
module is a Zariski sheafification, so a submodule of it cannot be described by its sections: the
sections of the sheafification are not the sections of the presheaf.  What is available at an
arbitrary module universe is `Stacks.SheafOfModules.localClosure`, the local closure of a
submodule of the underlying presheaf, whose membership condition is itself local; applying it to
`Stacks.SheafOfModules.presheafRangeSubmodule` of the restricted inclusion gives the image
factorisation of that inclusion.  This is the same device the tree uses elsewhere to obtain an
honest `SheafOfModules.Submodule` rather than a mere subobject, and it is why
`AlgebraicGeometry.Space.mem_restrictSubmoduleToChart` is phrased with a covering sieve.

**Monotonicity is proved on sieves, not on sections.**  A section of the smaller restriction lies
locally in the range of the restricted inclusion of `N₁`; that inclusion factors through the
inclusion of `N₂`, by the factorisation of `N₁ ⟶ M` through `N₂`, so the same covering sieve
witnesses membership in the larger restriction.  The factorisation is built inline rather than
named, because `submoduleInclusion` is already taken elsewhere in the library.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules

universe u

namespace AlgebraicGeometry.Space

section ChartSubmodule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS}

/-- **The restriction of a submodule to an étale scheme chart.**  The local closure of the
sectionwise range of the restricted inclusion `N ⟶ M`, which is the image factorisation of that
inclusion inside the chart restriction of `M`.

The chart restriction of `M` is a Zariski sheafification, so this cannot be given by its
sections; see the implementation notes. -/
def restrictSubmoduleToChart (M : Modules.{u, u} B S hS X.1 X.2)
    (N : M.Submodule) (V : SmallEtale B S hS X.1) :
    (restrictToChartScheme B S hS X.1 X.2 M V).Submodule :=
  Stacks.SheafOfModules.localClosure _
    (Stacks.SheafOfModules.presheafRangeSubmodule
      ((restrictToChartSchemeFunctor B S hS X.1 X.2 V).map N.ι).val)

/-- A section of the chart restriction of `M` lies in the chart restriction of `N` exactly when
the sieve of morphisms along which it restricts into the range of the restricted inclusion is a
covering sieve.  This holds by definition. -/
theorem mem_restrictSubmoduleToChart (M : Modules.{u, u} B S hS X.1 X.2)
    (N : M.Submodule) (V : SmallEtale B S hS X.1) (Y : ((chartScheme V).Opens)ᵒᵖ)
    (x : (restrictToChartScheme B S hS X.1 X.2 M V).val.obj Y) :
    x ∈ (restrictSubmoduleToChart M N V).obj Y ↔
      (Stacks.SheafOfModules.presheafRangeSubmodule
          ((restrictToChartSchemeFunctor B S hS X.1 X.2 V).map N.ι).val).toSubfunctor.sieveOfSection
            x ∈ Opens.grothendieckTopology (chartScheme V) Y.unop :=
  Iff.rfl

/-- **The restriction loses nothing.**  Every value of the restricted inclusion `N ⟶ M` lies in
the chart restriction of `N`. -/
theorem app_mem_restrictSubmoduleToChart (M : Modules.{u, u} B S hS X.1 X.2)
    (N : M.Submodule) (V : SmallEtale B S hS X.1) (Y : ((chartScheme V).Opens)ᵒᵖ)
    (m : ((restrictToChartSchemeFunctor B S hS X.1 X.2 V).obj N.toSheafOfModules).val.obj Y) :
    ((restrictToChartSchemeFunctor B S hS X.1 X.2 V).map N.ι).val.app Y m ∈
      (restrictSubmoduleToChart M N V).obj Y :=
  Stacks.SheafOfModules.app_mem_localClosure_presheafRangeSubmodule _ Y m

/-- **The chart restriction of submodules is monotone.**  A section lying locally in the range of
the restricted inclusion of the smaller submodule lies locally in the range of the restricted
inclusion of the larger one, because the first inclusion factors through the second.

This is the property that a comparison of a submodule found on a chart with the restriction of
one defined on the whole space rests on. -/
theorem restrictSubmoduleToChart_mono (M : Modules.{u, u} B S hS X.1 X.2)
    {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) (V : SmallEtale B S hS X.1) :
    restrictSubmoduleToChart M N₁ V ≤ restrictSubmoduleToChart M N₂ V := by
  intro Y x hx
  rw [mem_restrictSubmoduleToChart] at hx
  rw [mem_restrictSubmoduleToChart]
  refine GrothendieckTopology.superset_covering _ (fun Z g hg => ?_) hx
  obtain ⟨m, hm⟩ := hg
  have hι : Stacks.SheafOfModules.sheafFactorThruSubmodule N₁.ι N₂ (fun W y => h W y.2) ≫ N₂.ι =
      N₁.ι := Stacks.SheafOfModules.sheafFactorThruSubmodule_ι _ _ _
  have hcomp := (restrictToChartSchemeFunctor B S hS X.1 X.2 V).map_comp
    (Stacks.SheafOfModules.sheafFactorThruSubmodule N₁.ι N₂ (fun W y => h W y.2)) N₂.ι
  rw [hι] at hcomp
  refine ⟨((restrictToChartSchemeFunctor B S hS X.1 X.2 V).map
    (Stacks.SheafOfModules.sheafFactorThruSubmodule N₁.ι N₂
      (fun W y => h W y.2))).val.app _ m, ?_⟩
  rw [← hm]
  exact congrArg (fun φ => PresheafOfModules.Hom.app (SheafOfModules.Hom.val φ) _ m) hcomp.symm

end ChartSubmodule

end AlgebraicGeometry.Space

end
