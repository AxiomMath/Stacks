module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Topological modules

Stacks 0B25: for a topological ring `R`, (1) a topological `R`-module is an `R`-module `M` carrying
a topology for which addition `M × M → M` and scalar multiplication `R × M → M` are continuous, and
(2) a homomorphism of topological modules is a continuous `R`-linear map.

Both are in Mathlib.

* (1) is the structure `TopModuleCat R`, whose objects are exactly the topological `R`-modules;
  `TopModuleCat.of` produces one from an unbundled module with `[ContinuousAdd M]` and
  `[ContinuousSMul R M]`, which are precisely the source's two conditions.
* (2) is `ContinuousLinearMap`, i.e. `M →L[R] N`: an `R`-linear map bundled with a proof that its
  underlying function is continuous, which is literally the source's definition. The category
  structure wraps it in the one-field `TopModuleCat.Hom`, which carries no mathematics of its own
  beyond `ContinuousLinearMap`, so the tag goes on the latter.

## Faithfulness: `IsTopologicalAddGroup` is not an extra hypothesis

`TopModuleCat` lists `IsTopologicalAddGroup carrier` next to `ContinuousSMul R carrier`, so it
appears to demand continuity of negation, which 0B25 does not ask for. Over a *ring* the two
conditions coincide, because `-x = (-1 : R) • x`, so continuity of negation already follows from
continuity of scalar multiplication:

```
example (R M : Type*) [Ring R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M] :
    IsTopologicalAddGroup M := by
  refine { continuous_neg := ?_ }
  have : (fun x : M => -x) = fun x : M => (-1 : R) • x := by funext x; simp
  rw [this]; exact continuous_const.smul continuous_id
```

This is the argument Mathlib itself runs inside `TopModuleCat.of`, which is why `of` asks only for
the source's two continuity hypotheses. So `TopModuleCat R` is no stronger than 0B25(1), and the
apparent gap does not need reopening.
-/

@[expose] public section

-- The two former `@[stacks 0B25]` defs here were `ContinuousAdd M ∧ ContinuousSMul R M` and
-- `Continuous f` for an `f : M →ₗ[R] N`, with an unfolding lemma each; all four are subsumed by
-- the Mathlib declarations below.

add_to_stacks 0B25 "(1), topological modules: the objects of this category are exactly the modules
  over a topological ring equipped with a topology making addition and scalar multiplication
  continuous. The `IsTopologicalAddGroup` field is no strengthening of the source: over a ring
  `-x = (-1) • x`, so continuity of negation follows from `ContinuousSMul`." TopModuleCat

add_to_stacks 0B25 "(1), a topological module built from exactly the source's two conditions: `of`
  takes only `[ContinuousAdd M]` and `[ContinuousSMul R M]`, deriving `ContinuousNeg M` from
  `-x = (-1 : R) • x`." TopModuleCat.of

add_to_stacks 0B25 "(2), homomorphisms of topological modules: an `R`-linear map bundled with a
  proof that its underlying function is continuous." ContinuousLinearMap
