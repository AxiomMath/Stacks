module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIdealModuleComparison

/-!
# The map of defining ideal sheaves over a represented chart, read on a Zariski sheaf of ideals

Let
```
Z --i--→ h_V
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
whose left-hand ambient space `h_V = yoneda.obj V` is *represented* by an object `V` of the big
fppf category — an étale scheme chart, in the use this file is written for.  The map
`g^*𝓘' ⟶ 𝓘_Z` of defining ideal sheaves of [Stacks Project, Tag 04CP] then lands in a sheaf of
modules which `AlgebraicGeometry.Space.representedDefiningIdealSheafIso` identifies with the
inverse image `ε^*I` along the comparison `ε` of [Stacks Project, Tag 070R] of a single Zariski
sheaf of ideals `I ⊆ 𝒪_V` of the representing scheme.  This file pins down the transported map
`g^*𝓘' ⟶ ε^*I`.

## The route

Both of the two inputs factor a morphism through the inclusion `𝓘_Z ⊆ 𝒪_{h_V}`, which is a
monomorphism:

* `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` says that `g^*𝓘' ⟶ 𝓘_Z`
  followed by that inclusion is the inverse image of the inclusion `𝓘' ⊆ 𝒪_{X'}`, read in
  `𝒪_{h_V}` through `AlgebraicGeometry.Space.structureModulePullbackMap`.
* `AlgebraicGeometry.Space.representedDefiningIdealSheafIso_hom_comp_ι` says that the comparison
  isomorphism followed by that inclusion is
  `AlgebraicGeometry.Space.representedIdealComparison`, the inverse image along `ε` of the
  inclusion of `I` into the structure sheaf of the scheme.

Composing the first with the inverse of the comparison therefore computes the transported map
against `AlgebraicGeometry.Space.representedIdealComparison`, which is itself a monomorphism
(`AlgebraicGeometry.Space.mono_representedIdealComparison`); so that computation *characterises*
the transported map, and no further description of either side is needed to recognise it.

## Main results

* `AlgebraicGeometry.Space.representedDefiningIdealSheafIso_inv_comp_representedIdealComparison`:
  the inverse of the comparison isomorphism, followed by the comparison map `ε^*I ⟶ 𝒪_{h_V}`, is
  the inclusion `𝓘_Z ⊆ 𝒪_{h_V}`.
* `Space.idealSheafMap_comp_representedDefiningIdealSheafIso_inv_comp_comparison`:
  **the square for the ideal sheaves.**  The map of defining ideal sheaves, transported to
  `ε^*I`, composed with the comparison map `ε^*I ⟶ 𝒪_{h_V}`, is the inverse image of
  `𝓘' ⊆ 𝒪_{X'}` read through `AlgebraicGeometry.Space.structureModulePullbackMap`.
* `AlgebraicGeometry.Space.eq_idealSheafMap_comp_representedDefiningIdealSheafIso_inv`: that
  equation determines the transported map, by cancelling the monomorphism
  `ε^*I ⟶ 𝒪_{h_V}`.

## Implementation notes

**No tag is placed.**  Nothing here is a statement of the Stacks Project; the file transports a
map along an isomorphism which an earlier file already pinned to the canonical one, and records
the resulting characterisation.  [Stacks Project, Tag 04CP] is the map being transported and
[Stacks Project, Tag 070R] the comparison of sites behind `ε`, both cited rather than proved
here.

**Why the characterisation, and not just the square.**  For an étale chart `ε` the composite
`conormalPullbackComparison ≫ (modulePullback _).map (idealSheafMap _)` *is*
`AlgebraicGeometry.Space.conormalMap` (`AlgebraicGeometry.Space.conormalMap_eq`) with the first
factor an isomorphism, so identifying the chart inverse image of the conormal map with a
scheme-level map reduces to identifying the chart inverse image of
`AlgebraicGeometry.Space.idealSheafMap`.  The monomorphism `ε^*I ⟶ 𝒪_{h_V}` turns that
identification into the single equation of
`AlgebraicGeometry.Space.idealSheafMap_comp_representedDefiningIdealSheafIso_inv_comp_comparison`
to be checked of a candidate, which is what makes the ideal-sheaf half of the comparison
available without any affine-open description of the scheme-level map.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (V : BigFppfOver B S hS) (hF : IsAlgebraicSpace B S hS (yoneda.obj V))
  (Z : ClosedSubspaces B S hS (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS).1)

/-- **The inverse of the comparison isomorphism, followed by the comparison map into the
structure sheaf, is the inclusion of the defining ideal sheaf.**

This is `AlgebraicGeometry.Space.representedDefiningIdealSheafIso_hom_comp_ι` read in the other
direction: since the comparison isomorphism composed with `𝓘_Z.ι` is the comparison map
`ε^*I ⟶ 𝒪_{h_V}`, its inverse composed with that comparison map is `𝓘_Z.ι`. -/
theorem representedDefiningIdealSheafIso_inv_comp_representedIdealComparison :
    (representedDefiningIdealSheafIso B S hS V hF Z).inv ≫
        representedIdealComparison B S hS V hF (schemeSpaceIdeal B S hS V Z) =
      (definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩ Z).ι :=
  (Iso.inv_comp_eq _).2 (representedDefiningIdealSheafIso_hom_comp_ι B S hS V hF Z).symm

variable {X' : AlgebraicSpaces B S hS} (Z' : ClosedSubspaces B S hS X'.1)
  (g : (⟨yoneda.obj V, hF⟩ : AlgebraicSpaces B S hS) ⟶ X')
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS ⟨yoneda.obj V, hF⟩ Z ≫ g =
    f ≫ subspaceInclusion B S hS X' Z')

/-- **The square for the ideal sheaves.**  The map `g^*𝓘' ⟶ 𝓘_Z` of defining ideal sheaves of
[Stacks Project, Tag 04CP], transported along the comparison isomorphism to a map
`g^*𝓘' ⟶ ε^*I`, composed with the comparison map `ε^*I ⟶ 𝒪_{h_V}`, is the inverse image along
`g` of the inclusion `𝓘' ⊆ 𝒪_{X'}` read in `𝒪_{h_V}` through
`AlgebraicGeometry.Space.structureModulePullbackMap`.

Two rewrites and no computation: the inverse of the comparison isomorphism followed by the
comparison map is `𝓘_Z.ι` above, and `g^*𝓘' ⟶ 𝓘_Z` followed by `𝓘_Z.ι` is the right-hand side
by `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`. -/
theorem idealSheafMap_comp_representedDefiningIdealSheafIso_inv_comp_comparison :
    idealSheafMap B S hS Z Z' g f hsq ≫
        (representedDefiningIdealSheafIso B S hS V hF Z).inv ≫
          representedIdealComparison B S hS V hF (schemeSpaceIdeal B S hS V Z) =
      (modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
        structureModulePullbackMap B S hS g :=
  (congrArg (fun m => idealSheafMap B S hS Z Z' g f hsq ≫ m)
      (representedDefiningIdealSheafIso_inv_comp_representedIdealComparison
        B S hS V hF Z)).trans
    (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq)

/-- **The square determines the transported map.**  A morphism `g^*𝓘' ⟶ ε^*I` whose composite
with the comparison map `ε^*I ⟶ 𝒪_{h_V}` is the inverse image of `𝓘' ⊆ 𝒪_{X'}` read through
`AlgebraicGeometry.Space.structureModulePullbackMap` is the transported map of defining ideal
sheaves.

The comparison map is a monomorphism, by
`AlgebraicGeometry.Space.mono_representedIdealComparison`, and the transported map satisfies that
same equation by
`AlgebraicGeometry.Space.idealSheafMap_comp_representedDefiningIdealSheafIso_inv_comp_comparison`,
so the two agree.  This is the form in which the ideal-sheaf comparison is consumed: a candidate
scheme-level map needs only to be checked against the inclusion into the structure sheaf. -/
theorem eq_idealSheafMap_comp_representedDefiningIdealSheafIso_inv
    (u : (modulePullback B S hS g).obj (definingIdealSheaf B S hS X' Z').toSheafOfModules ⟶
      (representedAssociatedModule B S hS V hF).obj
        (schemeSpaceIdeal B S hS V Z).unitSubmodule.toSheafOfModules)
    (hu : u ≫ representedIdealComparison B S hS V hF (schemeSpaceIdeal B S hS V Z) =
      (modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
        structureModulePullbackMap B S hS g) :
    u = idealSheafMap B S hS Z Z' g f hsq ≫
      (representedDefiningIdealSheafIso B S hS V hF Z).inv :=
  (mono_representedIdealComparison B S hS V hF
      (schemeSpaceIdeal B S hS V Z)).right_cancellation _ _
    (hu.trans ((Category.assoc _ _ _).trans
      (idealSheafMap_comp_representedDefiningIdealSheafIso_inv_comp_comparison
        B S hS V hF Z Z' g f hsq)).symm)

end AlgebraicGeometry.Space

end
