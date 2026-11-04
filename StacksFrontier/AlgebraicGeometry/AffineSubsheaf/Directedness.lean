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
[Stacks, Tag 01B7]. No attribute was attached to it. This module attaches one.

## Main results

Nothing is proved here. The module registers
`AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered` against
[Stacks, Tag 01PG] under the label `directedness`.

## Implementation notes

The registration uses the `add_to_stacks` command rather than an `@[stacks]` attribute, because
the declaration it names lives in a module that several other files already import; the command
writes the same environment extension.

The covering set of the label is complete and consists of that one declaration: the statement
registered is `IsFiltered (FiniteTypeQuasicoherentSubobject F)` for a quasi-coherent `F` on an
arbitrary scheme, with no hypothesis the tag does not grant — indeed with two fewer, since the
tag's scheme is quasi-compact and quasi-separated and the registered statement needs neither. The
label `colimit` of the same tag is **not** registered and may not be: the colimit assertion is
not proved anywhere in this repository, and its missing input is the extension step
[Stacks, Tag 01PF].

## References

* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
* [Stacks Project, Tag 01B7](https://stacks.math.columbia.edu/tag/01B7)
-/

@[expose] public section

namespace AlgebraicGeometry

add_to_stacks 01PG "directedness"
  AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered

end AlgebraicGeometry

end
