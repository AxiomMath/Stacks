module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01PG, the directedness assertion

[Stacks, Tag 01PG] says that on a quasi-compact and quasi-separated scheme a quasi-coherent
module is the directed colimit of its quasi-coherent submodules of finite type. Its two
assertions are separately statable: that the category of those submodules is **filtered**, with
no hypothesis on the scheme, and that the canonical cocone out of it is **colimiting**, which
needs quasi-compactness and quasi-separatedness.

The first of the two is already proved, unconditionally on the scheme, as
`AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`
(`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/FiniteTypeSubobjects.lean`): the upper
bound of two finite type quasi-coherent subobjects is the image of the map to the ambient module
out of their direct sum, which is quasi-coherent by [Stacks, Tag 01BF] and of finite type by
[Stacks, Tag 01B7]. It already carries `@[stacks 01PG]` where it is declared.

## Main results

Nothing is proved or registered here: the declaration that proves the directedness assertion,
`AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`, is already registered against
[Stacks, Tag 01PG] by the attribute on its declaration, so a second registration from this
module would be a duplicate, which the `stacks` extension skips.

## Implementation notes

This module once registered the declaration a second time with
`add_to_stacks 01PG "directedness"`. That registration was a duplicate of the `@[stacks 01PG]`
attribute on the declaration, and the `stacks` extension skipped it with a warning, so it was
removed; the module now only collects the imports above.

## References

* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
* [Stacks Project, Tag 01B7](https://stacks.math.columbia.edu/tag/01B7)
-/

@[expose] public section

end
