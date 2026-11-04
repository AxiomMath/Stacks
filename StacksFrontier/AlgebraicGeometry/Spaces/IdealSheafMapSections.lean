module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators

/-!
# The map of defining ideal sheaves of a commutative square, on sections

Let `g : X ⟶ X'` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `Z ⊆ X` and `Z' ⊆ X'` be closed subspaces, and let the square of inclusions
commute.  `AlgebraicGeometry.Space.idealSheafMap` is the resulting morphism
`g^*𝓘_{Z'} ⟶ 𝓘_Z` of `𝒪_X`-modules, built by transposing twice; the only statement about it
is `AlgebraicGeometry.Space.idealSheafMap_transpose`, which describes it after both transposes.

This file reads it on sections.  Over a commutative diagram `d` of étale scheme charts, the
unit section of a regular function `s` in the defining ideal of `Z'` is carried by
`idealSheafMap` to the pullback of `s` along the vertical morphism of `d`.  So the pullbacks of
regular functions in the defining ideal of `Z'` are values of `idealSheafMap`, and a criterion
for it to be an epimorphism is that they span the defining ideal of `Z` locally.

## Main results

* `AlgebraicGeometry.Space.modulePullbackHomFMap_idealSheafMap`: the chartwise transpose of
  `AlgebraicGeometry.Space.idealSheafMap` is `AlgebraicGeometry.Space.idealSheafFMap`.
* `AlgebraicGeometry.Space.idealSheafMap_unitSection_coe`: the value of `idealSheafMap` on the
  unit section of `s` is the pullback of `s` along the vertical morphism of the chart diagram.
* `AlgebraicGeometry.Space.epi_idealSheafMap_of_spanSieve_mem`: `idealSheafMap` is an
  epimorphism as soon as every local section of `𝓘_Z` restricts, along a covering sieve of the
  small étale site of `X`, into the `𝒪_X`-span of such pullbacks.

## Implementation notes

The chartwise transpose of `AlgebraicGeometry.Space.idealSheafMap` is
`AlgebraicGeometry.Space.idealSheafFMap` by construction, so
`AlgebraicGeometry.Space.modulePullbackHomFMap_idealSheafMap` is
`AlgebraicGeometry.Space.idealSheafMap_transpose` with the transposes packaged;
`AlgebraicGeometry.Space.modulePullbackHomFMap_app` is what turns that into the statement about
sections, and `AlgebraicGeometry.Space.idealSheafFMap_app_coe` evaluates the result.

The spanning family of the epimorphism criterion is
`AlgebraicGeometry.Space.moduleFMapSpanningSet` at
`AlgebraicGeometry.Space.idealSheafFMap`, whose members are, by
`AlgebraicGeometry.Space.idealSheafFMap_app_coe`, exactly the restrictions of the pullbacks of
regular functions in the defining ideal of `Z'`.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')

/-- **The chartwise transpose of the map of defining ideal sheaves is the chartwise map.**  This
is `AlgebraicGeometry.Space.idealSheafMap_transpose` with the two transposes packaged as
`AlgebraicGeometry.Space.modulePullbackHomFMap`. -/
theorem modulePullbackHomFMap_idealSheafMap :
    modulePullbackHomFMap B S hS g (definingIdealSheaf B S hS X' Z').toSheafOfModules
        (definingIdealSheaf B S hS X Z).toSheafOfModules
        (idealSheafMap B S hS Z Z' g f hsq) =
      idealSheafFMap B S hS Z Z' g f hsq :=
  idealSheafMap_transpose B S hS Z Z' g f hsq

/-- **The map of defining ideal sheaves carries a unit section to a pullback of regular
functions.**  On a commutative diagram `d` of étale scheme charts, the value of
`AlgebraicGeometry.Space.idealSheafMap` on the unit section of a regular function `s` in the
defining ideal of `Z'` is the pullback of `s` along the vertical morphism of `d`. -/
theorem idealSheafMap_unitSection_coe (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (definingIdealSheaf B S hS X' Z').toSheafOfModules.val.obj (op d.V)) :
    (((idealSheafMap B S hS Z Z' g f hsq).val.app (op d.U)
        (modulePullbackUnitSection B S hS g
          (definingIdealSheaf B S hS X' Z').toSheafOfModules d s)) : ToType _).1 =
      chartDiagramPullback B S hS g d s.1 := by
  rw [← modulePullbackHomFMap_app B S hS g (definingIdealSheaf B S hS X' Z').toSheafOfModules
      (definingIdealSheaf B S hS X Z).toSheafOfModules (idealSheafMap B S hS Z Z' g f hsq) d s,
    modulePullbackHomFMap_idealSheafMap B S hS Z Z' g f hsq]
  exact idealSheafFMap_app_coe B S hS Z Z' g f hsq d s

/-- **The map of defining ideal sheaves is an epimorphism as soon as the pullbacks of regular
functions in the defining ideal of `Z'` locally span the defining ideal of `Z`.**  The spanning
family is the one of `AlgebraicGeometry.Space.moduleFMapSpanningSet` at
`AlgebraicGeometry.Space.idealSheafFMap`. -/
theorem epi_idealSheafMap_of_spanSieve_mem
    (h : ∀ (W : SmallEtale B S hS X.1)
      (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj (op W)),
      Stacks.SheafOfModules.spanSieve (definingIdealSheaf B S hS X Z).toSheafOfModules
          (moduleFMapSpanningSet B S hS g (definingIdealSheaf B S hS X' Z').toSheafOfModules
            (definingIdealSheaf B S hS X Z).toSheafOfModules
            (idealSheafFMap B S hS Z Z' g f hsq)) x ∈
        SmallEtale.topology B S hS X.1 W) :
    Epi (idealSheafMap B S hS Z Z' g f hsq) := by
  refine epi_of_spanSieve_moduleFMapSpanningSet_mem B S hS g
    (definingIdealSheaf B S hS X' Z').toSheafOfModules
    (definingIdealSheaf B S hS X Z).toSheafOfModules
    (idealSheafMap B S hS Z Z' g f hsq) ?_
  rw [modulePullbackHomFMap_idealSheafMap B S hS Z Z' g f hsq]
  exact h

end AlgebraicGeometry.Space

end
