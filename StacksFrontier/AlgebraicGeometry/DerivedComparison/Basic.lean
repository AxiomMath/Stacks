module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ordinary and derived direct image agree along an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module.
Write `R f_* : D⁺(𝒪_X-Mod) ⥤ D⁺(𝒪_S-Mod)` for the right derived functor of the direct image and
`α` for its unit, so that `α` at a bounded below complex `K` is the canonical comparison
`f_*(K) ⟶ R f_*(K)` in the derived category. Then `α` is invertible at `F[0]`, the complex with
`F` placed in degree zero: along an affine morphism the ordinary direct image already computes
the total derived direct image. This is the third assertion of [Stacks, Tag 01XC]'s consequence
recorded under [Stacks, Tag 02KG].

The mathematics is entirely proved elsewhere; this file composes two facts:

* `Stacks.AffineHigherDirectImage.rightAcyclic_pushforward` is [Stacks, Tag 01XC] in the shape
  "a quasi-coherent module is right acyclic for the pushforward along an affine morphism",
  obtained there from the vanishing `R ⁱ f_* F = 0` for `i > 0` together with left exactness of
  `f_*`, via part (2) of [Stacks, Tag 015C].
* `CategoryTheory.Functor.rightAcyclic`, as its defining file records, is *definitionally*
  invertibility of the unit of the right derived functor at the degree-zero complex, once
  `EnoughInjectives` supplies the `HasRightDerivedFunctor` instance that makes
  `Functor.rightDerivedFunctorPlus` and `Functor.rightDerivedFunctorPlusUnit` the right derived
  functor and its unit.

So the proof is the acyclicity statement itself, accepted at the unit spelling.

## Main results

* `Stacks.Tag02KGDerivedComparison.isIso_rightDerivedFunctorPlusUnit_app_of_isAffineHom`:
  **[Stacks, Tag 02KG]**, the comparison with the derived direct image.

## Implementation notes

The hypotheses are exactly those of the source assertion: `f` affine and `F` quasi-coherent.
Everything else in scope is an instance that is derivable here rather than assumed --
`HasDerivedCategory.standard` fixes a choice of derived category, and the two `local instance`
declarations below are `inferInstance` and `IsGrothendieckAbelian.enoughInjectives` respectively.
They are re-declared in the spelling that unfolds `AlgebraicGeometry.Scheme.Modules`, exactly as
in `StacksDraft.AlgebraicGeometry.F3.AffineHigherDirectImage.Vanishing`, because
`Scheme.Modules` is a `def` and instances stated at it are not found as instance arguments.

`HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso` is given a raised priority for
the same reason it is raised in the file supplying the acyclicity: at default priority the search
for the pointwise right derived functor of the pushforward is expensive.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.Tag02KGDerivedComparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Seated from `CohomologyAffineReduction`, not restated: one declaration of each fact,
-- given the instance attribute where the statements below need it.
attribute [local instance]
  _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.SchemeCohomology.sheafOfModules_enoughInjectives

/-- **[Stacks, Tag 02KG], comparison with the derived direct image.** For an affine morphism
`f : X ⟶ S` of schemes and a quasi-coherent `𝒪_X`-module `F`, the canonical map from the ordinary
direct image `f_* F`, placed in degree zero, to the total derived direct image `R f_*(F[0])` is an
isomorphism. Equivalently: a quasi-coherent module has no higher direct images along an affine
morphism, so the unit of `R f_*` is already invertible on degree-zero complexes.

This is `Stacks.AffineHigherDirectImage.rightAcyclic_pushforward`, [Stacks, Tag 01XC], read at the
unfolding of `CategoryTheory.Functor.rightAcyclic`. -/
@[stacks 02KG "comparison with the derived direct image", ega "III 1.3.2"]
theorem isIso_rightDerivedFunctorPlusUnit_app_of_isAffineHom
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [IsAffineHom f] [F.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor X.Modules 0).obj F)) :=
  Stacks.AffineHigherDirectImage.rightAcyclic_pushforward f F

end Stacks.Tag02KGDerivedComparison

end
