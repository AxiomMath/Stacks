module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite

/-!
# The associated presheaf of modules on a site of schemes

Let `F` be a quasi-coherent module on a scheme `S`.  The presheaf of Tag 03DS assigns to a
scheme `f : T ⟶ S` the abelian group `Γ(T, f⁺ F)`, and that group is a module over the ring
`Γ(T, 𝒪_T)` of global functions on `T`.  Restricting both along a functor from a site of
`S`-schemes therefore gives a presheaf of modules over the presheaf of rings
`Stacks.Sites.structurePresheaf`, and this is the presheaf underlying the module `F^a` of
Tag 03DU.

Nothing here uses a sheaf condition, on the site or on `S`: the content is the compatibility of
the scalar action with the restriction maps, which is a statement about one morphism of schemes
over `S` at a time.

The presheaf is `Stacks.Sites.associatedModulePresheaf`, assembled from the abelian presheaf
`Stacks.Sites.associatedPresheaf` and the action `Stacks.Sites.associatedPresheafModule`; the
semilinearity statements are `AlgebraicGeometry.pullbackSectionsMap_smul` on one morphism of
schemes over `S` and `Stacks.Sites.associatedPresheaf_map_smul` on the site.  All of them are
declared in `StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite`, which this module
re-exports.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/
