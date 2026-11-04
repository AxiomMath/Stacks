module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction

/-!
# Restriction of modules to a chart base change preserves injectives

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let `V` be an étale scheme chart of `Y`.  The structure morphism
`ι : U = V ×_Y X ⟶ X` is étale, being a base change of the étale structure morphism of `V`, so
part (1) of Stacks 03F3 for an étale morphism of algebraic spaces applies to it: restriction of
`𝒪_X`-modules along `ι` carries injective modules to injective modules.

## Main results

* `AlgebraicGeometry.Space.preservesInjectiveObjects_chartBaseChangeModulePullback`: restriction
  of `𝒪_X`-modules to `V ×_Y X` preserves injective objects.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over `S` and an étale scheme chart `V` of
`Y`, restriction of `𝒪_X`-modules to the algebraic space `U = V ×_Y X` carries injective modules
to injective modules. -/
theorem preservesInjectiveObjects_chartBaseChangeModulePullback (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) :
    (chartBaseChangeModulePullback B S hS f V).PreservesInjectiveObjects :=
  preservesInjectiveObjects_etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f V)
    (isEtale_chartBaseChangeInclusion B S hS f V)

end AlgebraicGeometry.Space

end
