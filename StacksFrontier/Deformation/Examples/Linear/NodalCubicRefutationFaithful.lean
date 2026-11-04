module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationUniverse

/-!
# Stacks 0DZ2 is false at the source's hypotheses, with `Module.Flat A P` restored

`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation` refutes
`Deformation.FlatModuleLiftBaseChangeStatement`, which carries four of the five flatness
hypotheses of Stacks 0DZ2's "flat horizontal arrows". The horizontal arrows of the diagram are
`A' → P'`, `P' → Q'`, `A → P` and `P → Q`, so the source also asks for `Module.Flat A P`, and
that statement does not say so. This file closes that gap and settles what it was worth:

**`Module.Flat A P` is redundant.** `Deformation.flat_of_surjective_of_ker_eq_map` derives it
from `Module.Flat A' P'` together with the left-hand cartesian square, by the isomorphism
`A ⊗_{A'} P' ≅ P` that square *is*. So omitting it did not strengthen
`Deformation.FlatModuleLiftBaseChangeStatement`: that statement and
`Deformation.FlatModuleLiftBaseChangeStatementFaithful` are equivalent, by
`Deformation.flatModuleLiftBaseChangeStatement_of_faithful` and
`Deformation.flatModuleLiftBaseChangeStatementFaithful_of_statement`. The refutation therefore
transports with no new mathematics, and what it refutes is the source.

For the counterexample the redundancy is visible by hand as well: `P = P'/t·P'` with
`P' = A'[x]/(x² − t·x − t²·Y)` free of rank two over `A' = NC[t]/t³`, so `P` is free of rank two
over `A = NC` on `{1, x}` — it is `NC[x]/(x²)`. `Deformation.Examples.ArtinSchreier.flat_PRed_NC`
proves `Module.Flat NC PRed` through the general lemma rather than through that basis, which is
shorter and says the same thing.

## What this file certifies, and what it does not

It certifies that the counterexample satisfies **every** hypothesis of Stacks 0DZ2, Lemma
93.12.2, with the single deviation that `M` is assumed finite over `P` — which the source's own
proof uses at Stacks 0A6A and its statement omits, so assuming it makes the statement here
*weaker* than the source's and a refutation of it refutes the source a fortiori. The hypothesis
table, with the declaration discharging each row, is in the module documentation of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation`; the one row added here is
`Module.Flat A P`, discharged by `flat_PRed_NC`.

It does **not** show that the square-zero case of 0DZ2 is false: that case is proved, as
`Deformation.FlatModuleLiftLocalization`. What fails is the source's reduction of the nilpotent
case to it — "by induction on the integer `n > 1` such that `Iⁿ = 0` we reduce to the case where
`I` is an ideal of square zero; details omitted". The counterexample has `I³ = 0` and `I² ≠ 0`,
one step past square zero, and the step that breaks is visible in it: `M = P/(x)` does lift to
`P'' = P'/t²P'` over `A'' = A'/(t²)`, as `P''/(x)`, but *that* lift is not locally liftable one
stage further — over `(P')_g` a lift of `(P''/(x))_g` would need `c = t²d` with
`c² = t·c + t²·Y`, i.e. `t²·Y = 0`, and `Y` is a unit there. The lift that is locally liftable
is `P''/(x − t·β)` with `β` an Artin–Schreier root of `Y`, which exists on each `D(g)` and not
globally. So the inductive hypothesis has to be applied to a *chosen* lift at the previous
stage, and the choice that the square-zero case hands back need not be the one the next stage
can use. `StacksFrontier.Deformation.ObstructionVariationQuadratic` is the structural form of the
same obstruction: the variation of the obstruction class along the torsor of lifts is quadratic
at the first filtration step, so the unobstructed classes are not a coset of a submodule and
cannot be reached by adjusting the choice.

The failure is an `H¹`, not an `Ext²`. `NC` is the nodal cubic over `𝔽₂`, which carries a
nontrivial Artin–Schreier `ℤ/2`-torsor; `Q'` is built from exactly that torsor, so the class
dies over `Q'` and on every `D(g)`, `g ∈ J' = (Y)`, while surviving globally. 0DZ2's proof sees
only the `Ext²` obstruction of a single square-zero step, which is why the torsor class is
invisible to it.

## Main results

* `Deformation.Examples.ArtinSchreier.flat_PRed_NC`: **`Module.Flat A P`** for the
  counterexample, the hypothesis of Stacks 0DZ2 that
  `Deformation.FlatModuleLiftBaseChangeStatement` leaves out.
* `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful`:
  **`¬ Deformation.FlatModuleLiftBaseChangeStatementFaithful.{0}`.**
* `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful_ulift`:
  **`¬ Deformation.FlatModuleLiftBaseChangeStatementFaithful.{u}`**, at an arbitrary universe.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Deformation
open scoped TensorProduct

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### `Module.Flat A P` for the counterexample -/

/-- **`Module.Flat A P` of Stacks 0DZ2 for the counterexample**, i.e. `Module.Flat NC PRed`:
the nodal cubic's `P = P'/t·P'` is flat over `A = NC`.

It is `Deformation.flat_of_surjective_of_ker_eq_map` applied to the left-hand square, whose
three inputs are already proved: `redA_surjective`, `surjective_PBase_PRed` with
`ker_PBase_PRed_eq_map`, and `flat_PBase`. Concretely `PRed` is `NC[x]/(x²)`, free of rank two
over `NC` on `{1, x}` — `PBase` is free of rank two over `ABase` on `{1, x}` by
`free_PBase`, and `ABase = NC[t]/t³` is free of rank three over `NC` on `{1, t, t²}`, so
`PBase` is free of rank six over `NC` and `t·PBase` is the span of `{t, t², t·x, t²·x}` — but
the general lemma is shorter and is the statement that matters, since it is also what makes the
hypothesis redundant in the source.

The `Algebra ABase NC` needed to speak of the square at all is `redA`, introduced here as a local
instance exactly as `not_flatModuleLiftBaseChangeStatement` introduces it; the conclusion
`Module.Flat NC PRed` does not mention it, being about the global `Algebra NC PRed`. -/
theorem flat_PRed_NC : Module.Flat NC PRed := by
  let : Algebra ABase NC := redA.toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := ABase) (S := NC) (A := PRed)
    (fun a => algebraMap_ABase_PRed_eq a)
  refine flat_of_surjective_of_ker_eq_map ABase NC PBase PRed
    redA_surjective surjective_PBase_PRed ?_ flat_PBase
  rw [ker_PBase_PRed_eq_map]
  rfl

/-! ### The refutation at the faithful statement -/

/-- **Stacks 0DZ2 with every hypothesis of the source written out, restricted to a finite
module, is false.**

The counterexample is the one of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation`, and the hypothesis this
statement adds over the one refuted there, `Module.Flat A P`, holds for it: `flat_PRed_NC`.
The proof does not need to supply it, because
`Deformation.flatModuleLiftBaseChangeStatement_of_faithful` derives it from the cartesian square
in general — but `flat_PRed_NC` is what a reader checking the hypothesis table against the
counterexample wants to see, and it is proved above. -/
theorem not_flatModuleLiftBaseChangeStatementFaithful :
    ¬ Deformation.FlatModuleLiftBaseChangeStatementFaithful.{0} := fun h =>
  not_flatModuleLiftBaseChangeStatement (flatModuleLiftBaseChangeStatement_of_faithful h)

/-- **The same at an arbitrary universe.** This is the form that makes the registrations
carrying Stacks 0DZ2 as a hypothesis vacuous at their own universe parameter. -/
theorem not_flatModuleLiftBaseChangeStatementFaithful_ulift :
    ¬ Deformation.FlatModuleLiftBaseChangeStatementFaithful.{u} := fun h =>
  not_flatModuleLiftBaseChangeStatement_ulift (flatModuleLiftBaseChangeStatement_of_faithful h)

end Deformation.Examples.ArtinSchreier

end
