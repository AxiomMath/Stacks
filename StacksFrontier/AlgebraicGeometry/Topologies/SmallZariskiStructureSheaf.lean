module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf

/-!
# The structure sheaf of the small Zariski site

The presheaf of rings `T ↦ Γ(T, 𝒪_T)` is a sheaf on the small Zariski site of a scheme `S`
inside a chosen big Zariski site, the site whose objects are the schemes open in `S`.  Its
value at an object is the ring of global functions on the whole of that object, so the sheaf
condition for a covering family `{Tᵢ → T}` is the assertion that functions on the pieces of a
Zariski covering of an open `T ⊆ S` which agree on the overlaps glue to a unique function on
`T`; it is a statement about the schemes `T`, not a reformulation of how the presheaf was
built.

`AlgebraicGeometry.SmallZariski.structure_isSheaf` and
`AlgebraicGeometry.SmallZariski.structureSheaf`, the latter being the structure sheaf `𝒪_S` of
Stacks 04HS for the site `S_Zar`, live next to the comparison of that site with the opens of
the underlying space of `S` in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiStructureSheaf`, which this
module re-exports.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
-/

add_to_stacks 03DU "small Zariski structure sheaf" AlgebraicGeometry.SmallZariski.structure_isSheaf
add_to_stacks 03DU "small Zariski structure sheaf construction"
  AlgebraicGeometry.SmallZariski.structureSheaf
add_to_stacks 04HS "small Zariski structure sheaf" AlgebraicGeometry.SmallZariski.structureSheaf
