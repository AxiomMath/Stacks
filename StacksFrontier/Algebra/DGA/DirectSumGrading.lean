module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.LinearMap.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical grading of a direct sum

A direct sum of modules is graded by its own coordinates: the degree-`n` part is
the image of the `n`-th inclusion, and these submodules decompose the direct sum.

## Main definitions

* `DirectSum.lofRange` is the degree-`n` coordinate submodule of a direct sum.
* `DirectSum.lofRangeDecomposition` is the decomposition of a direct sum into
  these submodules.

## References

* [Stacks Project, Tag 09MN](https://stacks.math.columbia.edu/tag/09MN)
-/

@[expose] public section

namespace DirectSum

variable {R : Type*} [CommRing R]

/-- The degree-`n` summand inside a direct sum. -/
abbrev lofRange {ι : Type*} (V : ι → Type*) [DecidableEq ι]
    [∀ i : ι, AddCommGroup (V i)] [∀ i : ι, Module R (V i)] (n : ι) :
    Submodule R (DirectSum ι V) :=
  LinearMap.range (DirectSum.lof R ι V n)

/-- The canonical decomposition of a direct sum into its coordinate submodules. -/
@[instance_reducible]
def lofRangeDecomposition {ι : Type*} (V : ι → Type*) [DecidableEq ι]
    [∀ i : ι, AddCommGroup (V i)] [∀ i : ι, Module R (V i)] :
    DirectSum.Decomposition (lofRange (R := R) V) :=
  DirectSum.Decomposition.ofLinearMap _
    (DirectSum.toModule R ι _ fun i ↦
      (DirectSum.lof R ι (fun i ↦ lofRange (R := R) V i) i).comp
        (DirectSum.lof R ι V i).rangeRestrict)
    (by ext i x : 2; simp)
    (by
      ext i ⟨x, y, rfl⟩ : 2
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
        DirectSum.toModule_lof, LinearMap.id_apply]
      rfl)

end DirectSum

end
