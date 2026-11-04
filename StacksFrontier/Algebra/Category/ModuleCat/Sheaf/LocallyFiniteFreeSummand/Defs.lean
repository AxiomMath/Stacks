module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Modules that are locally a direct summand of a finite free module

Let `(X, O_X)` be a ringed space. Stacks 0FNV takes as its hypothesis, and Stacks 0FNW (1)
produces as its conclusion, the condition that a sheaf of `O_X`-modules be *locally a direct
summand of a finite free `O_X`-module*: every point has an open neighbourhood `U` on which
the restriction of the module is a retract of `O_U^{⊕n}` for some natural number `n`. This
file is that predicate and nothing else, so that both halves of Stacks 0FNW — the one
concluding it and the one using it to identify the dual — can import it without importing
each other.

## Main definitions

* `Stacks.SheafOfModules.IsLocallyFiniteFreeSummand`: the predicate.

## Implementation notes

This is deliberately a *local* condition, and is therefore a different notion from the two
global predicates already in the library, with which it should not be confused:

* `StrictlyPerfect.IsDirectSummandOfFiniteFree` (Tag 08C5) asks that a module on a ringed
  space be a direct summand of a finite free module outright, with no covering;
* `AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree` is the same global condition for
  a ringed site.

Neither implies the condition here is satisfied only globally, and neither follows from it:
the point of Stacks 0FNW (1) is precisely that a module with a dual need only be a summand
of a finite free module *locally*, and the rank may vary from one member of the covering to
another. A module satisfying either global predicate does satisfy this one, taking the
covering by `X` itself; the converse fails.

The retract is taken against `SheafOfModules.free (ULift (Fin n))` rather than against an
arbitrary finite index type, so that the rank is a natural number, as in the source's
`O_U^{⊕n}`. The site-level statement from which this is deduced,
`Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing`, produces an
arbitrary finite index type instead; re-indexing it by `Fin n` is done where that theorem is
applied.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FNW](https://stacks.math.columbia.edu/tag/0FNW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace Stacks.SheafOfModules

universe u

/-- A sheaf of `O_X`-modules on a ringed space is **locally a direct summand of a finite free
module** if every point of `X` has an open neighbourhood `U` on which the module restricts to
a retract of `O_U^{⊕n}`, for some natural number `n` depending on `U`.

This is the hypothesis of Stacks 0FNV and the conclusion of Stacks 0FNW (1). -/
@[sga "6 II 2.0" "special case"]
def IsLocallyFiniteFreeSummand (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F : SheafOfModules.{u} (structureSheafRing X)) :
      Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ n : ℕ,
    Nonempty (Retract (F.over U)
      (SheafOfModules.free (R := (structureSheafRing
        X).over U)
        (ULift.{u} (Fin n))))

end Stacks.SheafOfModules
