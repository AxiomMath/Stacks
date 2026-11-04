module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpec
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChartCanonical
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeTransition
public import StacksFrontier.AlgebraicGeometry.ProjPolynomialSections.GradedIso
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# Tag 02NC over a base scheme: the chart comparisons commute with the chart transitions

Tag 02NC's proof glues the comparisons attached to the members of a covering of the base over
which `ℒ` is trivialized. This file proves the **compatibility with the chart transitions** at the
level of morphisms of schemes: for a nested pair `W ≤ V` of affine opens of the base, the square

```
Proj ℬ(W) ──────→ Proj 𝒜(W)
   │                  │
   │                  │
   ↓                  ↓
Proj ℬ(V) ──────→ Proj 𝒜(V)
```

commutes, the horizontal arrows being the chart comparisons and the vertical ones the chart
transitions `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` of a relative homogeneous
spectrum.

This is the morphism-level form of
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.res_comp_psiSectionAt`, which says the same for
the underlying homomorphisms of graded rings of sections, and it is the shape the glueing
consumes: with it and the section-independence
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_unit_smul`, the
comparisons attached to a family of trivializing sections over the members of a basis of the
topology of the base are two solutions of one gluing problem.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projInclusionMap_eq_mapHomOfTop`: the chart
  transition of a relative homogeneous spectrum is the glued morphism of the restriction
  homomorphism.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projInclusionMap_comp_projMap_psiSectionAt`:
  **the commuting square.**

## Why not `AlgebraicGeometry.Proj.map`

The chart comparison is `AlgebraicGeometry.Proj.map`, because Mathlib's hypothesis
`ℬ₊ ≤ 𝒜₊.map ψ` holds for it
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.irrelevant_le_map_psiSectionAt`). **The chart
transitions are not**, and cannot be made so: restriction of homogeneous sections along an
inclusion `W ≤ V` of affine opens is not surjective in positive degrees — `W` is not a basic open
of `V` in general, so a section over `W` need not be a fraction of sections over `V` — and
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.irrelevant_le_map_res` is available for basic
open inclusions only. What *is* available for an arbitrary inclusion of affine opens is
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionDomain_eq_top`, the domain of definition being
everything (Tag 01NO).

So the square is proved in the `Stacks.AlgebraicGeometry.ProjShared.mapHomOfTop` vocabulary, whose
composition law `Stacks.AlgebraicGeometry.ProjAndSpec.mapHomOfTop_comp_of_mapDomain_eq_top`
asks only for the domains of definition, its hypothesis for the composite being
`Stacks.AlgebraicGeometry.ProjAndSpec.mapDomain_comp_eq_top` — and which the chart transition is
*definitionally*, since
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition` is `mapHomOfTop`. The comparison
crosses over by
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.mapHomOfTop_psiSectionAt_eq_projMap`.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open CategoryTheory Filter HomogeneousIdeal Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjAndSpec
open Stacks.AlgebraicGeometry.ProjPolynomialSections
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

/-! ### The square -/

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- **The chart transition of a relative homogeneous spectrum is the glued morphism of the
restriction homomorphism.** `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition` is
`Stacks.AlgebraicGeometry.ProjShared.mapHomOfTop`, so this is a reading, not a computation. -/
theorem projInclusionMap_eq_mapHomOfTop (A : SheafGradedAlgebra S) (W V : S.Opens) (h : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) :
    RelativeProj.projInclusionMap A W V h hW hV =
      mapHomOfTop (A.grading V) (A.grading W) (A.res h)
        (RelativeProj.projInclusionDomain_eq_top A W V h hW hV) := rfl

variable (𝒜 : SheafGradedAlgebra S)

/-- **The chart comparisons of Tag 02NC commute with the chart transitions.**

For a nested pair `W ≤ V` of affine opens of the base, comparing over `V` and then restricting to
the chart over `W` is restricting and then comparing over `W`, with the restricted section. The
underlying statement about homomorphisms of graded rings of sections is
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.res_comp_psiSectionAt`; what this adds is the
passage to morphisms of schemes, which goes through the composition law for glued morphisms rather
than through `AlgebraicGeometry.Proj.map` because the chart transitions do not satisfy Mathlib's
hypothesis — see the module documentation.

Together with
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_unit_smul` this is the
compatibility the glueing of Tag 02NC consumes: the comparisons attached to an arbitrary family of
trivializing sections over the members of a basis of the topology of the base agree on nestings,
with no coherence condition on the family. -/
theorem projInclusionMap_comp_projMap_psiSectionAt {W V : S.Opens} (h : W ≤ V)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) {x : (tp L 1).val.obj (op V)}
    (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d)
    (hxW : ∀ d : ℕ, 0 < d → TrivializesPower L W ((tp L 1).val.map (homOfLE h).op x) d) :
    RelativeProj.projInclusionMap (twist 𝒜 L) W V h hW hV ≫ projMap_psiSectionAt L 𝒜 hx =
      projMap_psiSectionAt L 𝒜 hxW ≫ RelativeProj.projInclusionMap 𝒜 W V h hW hV := by
  have hdV := mapDomain_psiSectionAt_eq_top' L 𝒜 hx
  have hdW := mapDomain_psiSectionAt_eq_top' L 𝒜 hxW
  have hresA := RelativeProj.projInclusionDomain_eq_top 𝒜 W V h hW hV
  have hresB := RelativeProj.projInclusionDomain_eq_top (twist 𝒜 L) W V h hW hV
  have hdc₁ : mapDomain (𝒜.grading V) ((twist 𝒜 L).grading W)
      (((twist 𝒜 L).res h).comp (psiSectionAt L 𝒜 V x)) = ⊤ :=
    mapDomain_comp_eq_top _ _ _ _ _ hdV hresB
  have hdc₂ : mapDomain (𝒜.grading V) ((twist 𝒜 L).grading W)
      ((psiSectionAt L 𝒜 W ((tp L 1).val.map (homOfLE h).op x)).comp (𝒜.res h)) = ⊤ :=
    mapDomain_comp_eq_top _ _ _ _ _ hresA hdW
  rw [← mapHomOfTop_psiSectionAt_eq_projMap L 𝒜 hx hdV,
    ← mapHomOfTop_psiSectionAt_eq_projMap L 𝒜 hxW hdW,
    projInclusionMap_eq_mapHomOfTop 𝒜 W V h hW hV,
    projInclusionMap_eq_mapHomOfTop (twist 𝒜 L) W V h hW hV,
    ← mapHomOfTop_comp_of_mapDomain_eq_top (𝒜.grading V) ((twist 𝒜 L).grading V)
      ((twist 𝒜 L).grading W) (psiSectionAt L 𝒜 V x) ((twist 𝒜 L).res h) hdV hresB hdc₁,
    ← mapHomOfTop_comp_of_mapDomain_eq_top (𝒜.grading V) (𝒜.grading W)
      ((twist 𝒜 L).grading W) (𝒜.res h)
      (psiSectionAt L 𝒜 W ((tp L 1).val.map (homOfLE h).op x)) hresA hdW hdc₂]
  exact mapHomOfTop_congr (𝒜.grading V) ((twist 𝒜 L).grading W)
    (res_comp_psiSectionAt L 𝒜 h x) hdc₁ hdc₂

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
