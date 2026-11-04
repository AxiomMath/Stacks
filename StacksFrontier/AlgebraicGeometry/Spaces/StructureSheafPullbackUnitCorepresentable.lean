module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The inverse image of the structure sheaf of an algebraic space, identified

`AlgebraicGeometry.Space.modulePullbackUnitIso` — the identification `f^*𝒪_X ≅ 𝒪_{X'}` of
Stacks 03LU — is built by corepresentability: it is
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, which is
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso` of the two corepresentations of
`coyoneda.obj (op 𝒪_{X'})`.

This file reads the one characterisation corepresentability gives — for two corepresentations
`e`, `e'` of one functor, the comparison morphism is the one whose composites are the two
bijections of one another,

`(e.uniqueUpToIso e').hom ≫ q = e.homEquiv.symm (e'.homEquiv q)`,

which is `CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso_hom_comp` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit` — at the two
corepresentations of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp`: **the inverse image of the structure
  sheaf, identified.**  Composing `𝒪_{X'} ⟶ f^*𝒪_X` with a morphism out of `f^*𝒪_X` is the
  corepresentability bijection of
  `Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitCorepresentableBy` applied to it.

## Implementation notes

The statement is `CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso_hom_comp` at the two
corepresentations
`CategoryTheory.Functor.CorepresentableBy.coyoneda` and
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitCorepresentableBy`, whose comparison
morphism is `.hom` of `pullbackModulesObjUnitIso` and so `.inv` of
`AlgebraicGeometry.Space.modulePullbackUnitIso`, that being its inverse.  The bijection of the
first of the two is the identity (`CategoryTheory.Functor.CorepresentableBy.coyoneda_homEquiv`),
so it contributes nothing.

### What this does not give

It does **not** give the components of `AlgebraicGeometry.Space.modulePullbackUnitIso` at an
étale chart, which is what a computation with the inverse image of a global section needs.
Unwinding the bijection of
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitCorepresentableBy` reaches
`CategoryTheory.MorphismOfTopoi.pushforwardTerminalHomEquiv`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposTerminalSections.lean`), for which the
library has naturality in the sheaf but no description of a value on sections; so the chain stops
one step short of
`AlgebraicGeometry.Space.modulePushforwardCounitApp`, the chartwise universal property of the
direct image, which is what the components would have to be expressed through.

**That is a statement about this one isomorphism and about nothing else.**  It is the
identification `f^*𝒪_X ≅ 𝒪_{X'}` of the *structure sheaf* whose chart components are missing.  In
particular this is **not** an obstruction to the identity and composition laws of
`AlgebraicGeometry.Space.modulePullbackChartSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackChartSectionCoherence.lean`): neither law
mentions `modulePullbackUnitIso`, which does not occur in that file at all.  The identity law is
computed from `AlgebraicGeometry.Space.smallEtaleDirectImageRanIdIso_hom_app_apply` and the
composition law from the chart correspondence of Stacks 03G4.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.Space

/-- **The inverse image of the structure sheaf, identified by its universal property.**  For a
morphism `h : X' ⟶ X` of algebraic spaces, the morphism `𝒪_{X'} ⟶ h^*𝒪_X` inverse to the
identification `AlgebraicGeometry.Space.modulePullbackUnitIso` of Stacks 03LU is characterised by
its composites: composing it with a morphism `q : h^*𝒪_X ⟶ N` of `𝒪_{X'}`-modules gives the
corepresentability bijection of
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitCorepresentableBy` at `q`, that is the
transpose of `q` along the Stacks 03D7 adjunction read as a global section of `N`.

This is `CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso_hom_comp` at the two
corepresentations `pullbackModulesObjUnitIso` compares; the bijection of the first of them is the
identity, so only the second appears. -/
theorem modulePullbackUnitIso_inv_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X X' : AlgebraicSpaces B S hS} (h : X' ⟶ X)
    (N : Modules.{u, u} B S hS X'.1 X'.2)
    (q : (modulePullback B S hS h).obj
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ⟶
        N) :
    (modulePullbackUnitIso B S hS h).inv ≫ q
      = (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitCorepresentableBy
          (smallEtaleRingedToposModulesHom B S hS h)).homEquiv q :=
  Functor.CorepresentableBy.uniqueUpToIso_hom_comp _ _ q

end AlgebraicGeometry.Space

end
