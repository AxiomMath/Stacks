module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Triangulated
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealPowStalk
/-!
# Biproducts of finite locally free modules on a scheme

A biproduct of two finite locally free sheaves of modules on a scheme is finite locally free:
intersect the two trivialising coverings pairwise, and over each intersection take the disjoint
union of the two free bases.

The biproduct result is proved in `Stacks.Perfect.BoundedLocallyFreeComplexes` with the spelling
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, a reducible abbreviation of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` — the class
`AlgebraicGeometry.HasResolutionProperty` is stated with — so it applies here directly. The
hypotheses are passed by assumption rather than instance search: that lemma's sheaf of rings is
the one of `X.toRingedSpace`, which agrees with `X.ringCatSheaf` only at default transparency.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_biprod`: a biproduct of two finite
  locally free sheaves of modules on a scheme is finite locally free.

## Implementation notes

The biproduct is taken in `SheafOfModules X.ringCatSheaf` rather than in
`AlgebraicGeometry.Scheme.Modules X`, which is a `def` for it whose category instance is a
structure copy. Both spellings have binary biproducts and the two biproducts of a pair of
modules over a scheme agree definitionally, so `isFiniteLocallyFree_biprod` applies to
`(M ⊞ N : X.Modules)`; what fails is instance search for `HasBinaryBiproduct M N` when the
ambient category is given as `SheafOfModules X.ringCatSheaf` while `M` and `N` are typed as
modules over the scheme, so a consumer at that spelling has to ascribe the biproduct to
`AlgebraicGeometry.Scheme.Modules X`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : Scheme.{u}}

/-- **A biproduct of two finite locally free sheaves of modules on a scheme is finite locally
free.** -/
theorem isFiniteLocallyFree_biprod (M N : SheafOfModules.{u} X.ringCatSheaf)
    [IsFiniteLocallyFree (R := X.ringCatSheaf) M]
    [IsFiniteLocallyFree (R := X.ringCatSheaf) N] :
    IsFiniteLocallyFree (R := X.ringCatSheaf) (M ⊞ N) :=
  @Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_biprod
    X.toRingedSpace M N _ _ _ _ ‹_› ‹_›

end AlgebraicGeometry.SheafOfModules

end
