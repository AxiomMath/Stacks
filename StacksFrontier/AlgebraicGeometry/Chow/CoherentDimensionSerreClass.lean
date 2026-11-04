module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherent
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentReflexive
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic
import all StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherent

/-!
# The delta-dimension bound on a coherent sheaf, read pointwise

Let `(S, δ)` be the base situation of chapter 42 and let `X` be a scheme locally of finite type
over `S`. For `k : ℤ` the subcategory `Coh_{≤k}(X)` collects the coherent sheaves `F` with
`dim_δ(Supp F) ≤ k`. That bound is equivalent to the pointwise bound
`relativeDimension δ f x ≤ k` at every `x` in the support of `F`, and this module records that
equivalence.

The property `Stacks.Chow.coherentModulesDimLE` itself, the full subcategory it cuts out, and
the Serre property of [Stacks, Tag 02S8] are
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension`, which this module
imports.

## Main results

* `Stacks.Chow.coherentModulesDimLE_iff_forall_relativeDimension_le` — the bound read pointwise
  on the support.

## Implementation notes

The support dimension is measured on `Stacks.Chow.reducedSupport`, the canonical reduced closed
subscheme on the support, exactly as in the definition of the cycle associated to a coherent
sheaf, so the two dimension bounds are literally the same condition.

The library carries two field-identical realizations of the coherence predicate of Tag 01BV. The
ambient category here is `Stacks.SheafOfModules.CoherentModules`, the one over which the abelian
structure and the exactness of the inclusion are stated; `Stacks.Chow.reducedSupport` takes the
other one as an instance, and `Stacks.SheafOfModules.IsCoherent.sheafOfModules` converts.

The two directions of the pointwise reading of the bound are
`Stacks.Chow.relativeDimension_le_of_mem_supp` and
`Stacks.Chow.schemeDeltaDimension_reducedSupport_le`, stated for the support of a coherent
module in general.

## References

* [Stacks Project, Tag 02S8](https://stacks.math.columbia.edu/tag/02S8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ZeroObject

universe u

namespace Stacks.Chow

/-- The delta-dimension bound defining `Coh_{≤k}(X)` read off pointwise: it says exactly that
every point of the support has relative dimension at most `k`. -/
theorem coherentModulesDimLE_iff_forall_relativeDimension_le (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    coherentModulesDimLE C f k F ↔
      ∀ x ∈ SheafOfModules.supp F.obj, relativeDimension C.dimensionFunction f x ≤ k :=
  have : _root_.SheafOfModules.IsCoherent F.obj := F.property.sheafOfModules
  schemeDeltaDimension_reducedSupport_le_iff C f F.obj k


end Stacks.Chow

end
