module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicDiagram

/-!
# The module of the Stacks 0DZ2 counterexample

Fifth layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`. The module
the counterexample is about is

`M = P/(x) = NC`,

the quotient of `P = NC[x]/(x²)` by the thickening coordinate. Two presentations of it are
possible and the cheap one matters:

* as the literal quotient `P ⧸ (x̄)`. Then `Module.Finite P M` is immediate, but `Module.Flat A M`
  needs `P` exhibited as free over `A = NC` on `{1, x̄}` — a further `AdjoinRoot`-and-quotient
  argument;
* as `NC` itself, carrying the `P`-module structure through the ring map `P → NC` that kills `x`.
  Then **`Module.Flat A M` is `Module.Flat NC NC`, which is self-flatness**, and
  `Module.Finite P M` follows from surjectivity of that map. Nothing has to be said about bases.

The second is what is built here. The map is `pRedToNC`, obtained from `pBaseToNC` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicQColumn` — which sends `x ↦ 0` and `t ↦ 0`,
and exists because the constant term of `x² − t·x − t²·Y` is divisible by `t²` — by factoring
through `P = P'/t·P'`, which is possible because that map already kills `t`.

Note that `M` is **finite and cyclic**: that is what makes the counterexample survive the
finiteness restriction in `Deformation.FlatModuleLiftBaseChangeStatement`, which is 0DZ2 with
`Module.Finite P M` added. A counterexample with a non-finite `M` would prove nothing about that
statement, and would anyway only re-refute the source's own proof step, which
`StacksFrontier.Deformation.FlatModuleLiftLocalization` already records as false without finiteness.

## Main definitions

* `Deformation.Examples.ArtinSchreier.pRedToNC`: the map `P → NC` killing `x`, and the
  `Algebra P NC` instance it induces, which is the `P`-module structure on `M`.

## Main results

* `Deformation.Examples.ArtinSchreier.surjective_pRedToNC`: `P → NC` is surjective.
* `Deformation.Examples.ArtinSchreier.finite_NC`: **`Module.Finite P M`**, from that surjectivity.
* `Deformation.Examples.ArtinSchreier.flat_NC_NC`: **`Module.Flat A M`**, which is self-flatness.
* `Deformation.Examples.ArtinSchreier.isScalarTower_NC_PRed_NC`: **`IsScalarTower A P M`** — the
  `NC`-action on `M` through `P` is the native one, because `P → NC` splits the structure map.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### The map `P → NC` -/

/-- `pBaseToNC` restricted along `A' → P'` is the reduction `A' → NC`. -/
theorem pBaseToNC_algebraMap (a : ABase) :
    pBaseToNC (algebraMap ABase PBase a) = redA a :=
  AdjoinRoot.lift_of _

/-- `pBaseToNC` kills `t`. -/
theorem pBaseToNC_tauP : pBaseToNC tauP = 0 := by
  change pBaseToNC (algebraMap ABase PBase (tau NC)) = 0
  rw [pBaseToNC_algebraMap, redA_tau]

/-- **The map `P → NC`**, killing `x`. It exists because `pBaseToNC` already kills `t`. -/
def pRedToNC : PRed →+* NC :=
  Ideal.Quotient.lift _ pBaseToNC (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, pBaseToNC_tauP, zero_mul])

/-- The `P`-module structure on `M = NC`. -/
instance : Algebra PRed NC := pRedToNC.toAlgebra

/-- The composite `P' → P → NC` is `pBaseToNC`. -/
theorem algebraMap_pRed_NC (a : PBase) :
    algebraMap PRed NC (algebraMap PBase PRed a) = pBaseToNC a := rfl

/-- The composite `NC → P' → NC` is the identity. -/
theorem pBaseToNC_algebraMap_NC (a : NC) :
    pBaseToNC (algebraMap NC PBase a) = a := by
  rw [IsScalarTower.algebraMap_apply NC ABase PBase a, pBaseToNC_algebraMap]
  change redA (cst NC a) = a
  exact redA_cst a

/-- **`P → NC` is surjective**: it splits the structure map `NC → P`. -/
theorem surjective_pRedToNC : Function.Surjective (algebraMap PRed NC) := by
  intro a
  refine ⟨algebraMap NC PRed a, ?_⟩
  rw [IsScalarTower.algebraMap_apply NC PBase PRed a, algebraMap_pRed_NC,
    pBaseToNC_algebraMap_NC]

/-- **`Module.Finite P M`** for `M = NC`: the structure map is surjective, so `M` is cyclic. This
is the finiteness that `Deformation.FlatModuleLiftBaseChangeStatement` adds to Stacks 0DZ2, and
the counterexample satisfies it. -/
theorem finite_NC : Module.Finite PRed NC :=
  Module.Finite.of_surjective (Algebra.linearMap PRed NC) surjective_pRedToNC

/-- **`Module.Flat A M`** for `A = NC` and `M = NC`: self-flatness. Presenting `M` as `NC` rather
than as `P ⧸ (x̄)` is what reduces this hypothesis of Stacks 0DZ2 to nothing. -/
theorem flat_NC_NC : Module.Flat NC NC := Module.Flat.self

/-- **`IsScalarTower A P M`**, one of the seven towers of Stacks 0DZ2: the `NC`-action on
`M = NC` through `P` is the native one, because `P → NC` splits `NC → P`. -/
instance isScalarTower_NC_PRed_NC : IsScalarTower NC PRed NC :=
  IsScalarTower.of_algebraMap_eq fun a => by
    have h : algebraMap PRed NC (algebraMap NC PRed a) = a := by
      rw [IsScalarTower.algebraMap_apply NC PBase PRed a, algebraMap_pRed_NC,
        pBaseToNC_algebraMap_NC]
    rw [h]
    rfl

end Deformation.Examples.ArtinSchreier

end
