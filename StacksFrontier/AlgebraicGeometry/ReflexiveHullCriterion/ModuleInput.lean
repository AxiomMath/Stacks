module

public import StacksFrontier.Algebra.Module.Reflexive

/-!
# The module-level content of the missing geometric input

`ReflexiveHullCriterion.reflexiveHullAdjunction_of_dualSheaf` reduces
[Stacks, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH) to one statement about the dual
of a coherent module on an integral locally Noetherian scheme: that it is coherent and
reflexive.  Over a Noetherian domain the module-level counterpart of the reflexivity half is
already proved in this library, so what the sheaf-level statement still needs is not algebra
but the bridge between a dual sheaf and the dual of its modules of sections.

`Algebra/Module/Reflexive.lean` contains that counterpart twice over: once as
`isReflexive_linearMap` (Stacks Tag 0AV3), which is public, and once as `isReflexive_dual`,
which is `private` and therefore unusable from outside that file, under the weaker hypotheses
that `R` be a domain and the dual be finite.  The statement below is the instance of the
public one that the geometric input would consume.

## Main results

* `isReflexive_dual_of_finite`: over a Noetherian domain, the dual of a finite module is
  reflexive.

## References

* [Stacks Project, Tag 0AV3](https://stacks.math.columbia.edu/tag/0AV3)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
-/

@[expose] public section

universe u v

namespace Stacks.ReflexiveDual

/-- **Over a Noetherian domain, the dual of a finite module is reflexive.**  This is
`isReflexive_linearMap`, Stacks Tag 0AV3, with the target the base ring. -/
theorem isReflexive_dual_of_finite {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsReflexive R (Module.Dual R M) :=
  isReflexive_linearMap (inferInstance : Module.IsReflexive R R)

end Stacks.ReflexiveDual
