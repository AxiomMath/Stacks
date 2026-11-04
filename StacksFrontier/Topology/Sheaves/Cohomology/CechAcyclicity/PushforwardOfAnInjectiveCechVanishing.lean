module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.PushforwardOfAnInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing

/-!
# Čech acyclicity of the pushforward of an injective module

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `I` be an injective `O_X`-module.
Then the positive-degree Čech cohomology of `f_* I` vanishes for every family of opens of
`Y`, and hence for every open covering of `Y`.

## Main definitions

No new definitions are introduced.

## Main results

* `pushforward_injective_cechCohomology_isZero` is part (1) of Stacks Tag 01EX, stated
  unconditionally.

## Implementation notes

The conditional form `pushforward_injective_cechCohomology_isZero_of_flasqueCechVanishing`
carries the Čech acyclicity of flasque abelian sheaves — Stacks Tag 09SZ — as an explicit
hypothesis. That input is now available as
`Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque`, so the hypothesis
is discharged here and the unconditional statement of part (1) is recorded.

Tag 09SZ is stated for a family of opens together with an open it covers; the covering
hypothesis is unused there, so the family is regarded as a covering of its own union.

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.Cohomology.PushforwardAcyclic

/-- **Stacks 01EX, part (1).** The positive-degree Čech cohomology of the pushforward of an
injective module vanishes for every family of opens, and hence for every open covering. -/
@[stacks 01EX "part (1)"]
public theorem pushforward_injective_cechCohomology_isZero
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I]
    {J : Type u} (U : J → Opens Y.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor U).obj
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj I).val.presheaf).homology p) :=
  pushforward_injective_cechCohomology_isZero_of_flasqueCechVanishing f
    (fun G hG {_K} W q hq =>
      have := hG
      Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque G (⨆ i, W i) W
        rfl q hq)
    I U p hp

end Stacks.Cohomology.PushforwardAcyclic

end

end
