module

public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# A bundled dimension function is a dimension function for catenarity

`DimensionFunction X` bundles a function `X → ℤ` with the two conditions a dimension function
satisfies, and `IsDimensionFunctionForCatenary` is the unbundled predicate the catenarity results
are stated against. The two live in modules that do not import one another, so the lemma relating
them has no home in either; this module is that home.

## Main results

* `TopologicalSpace.DimensionFunction.isDimensionFunctionForCatenary`: the function underlying a
  bundled dimension function satisfies the unbundled predicate.
-/

@[expose] public section

namespace TopologicalSpace

/-- A bundled dimension function satisfies the two conditions `IsDimensionFunctionForCatenary`
asks for. -/
public lemma DimensionFunction.isDimensionFunctionForCatenary
    {X : Type*} [TopologicalSpace X] (δ : DimensionFunction X) :
    IsDimensionFunctionForCatenary δ := by
  constructor
  · intro x y hxy hne
    exact δ.strictAnti_specializes hxy hne
  · intro x y hxy
    exact δ.step_immediate hxy

end TopologicalSpace

end
