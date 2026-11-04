module

public import StacksFrontier.AlgebraicGeometry.Descent.BigSiteEquivalence.AssociatedPresheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor

/-!
# Functoriality of the associated presheaf of modules

A morphism `φ : F ⟶ G` of quasi-coherent modules on a scheme `S` pulls back to every scheme
over `S`, and taking global sections of the pullbacks gives a morphism of the presheaves of
Tag 03DS.  Assembling that assignment gives the functor `F ↦ F^a` of Tag 03DX on any site of
`S`-schemes, at the level of presheaves of modules, so no sheaf condition is needed.

The construction is `Stacks.Sites.associatedModuleFunctor`, built from the induced morphisms
`Stacks.Sites.associatedPresheafMap` of associated presheaves and
`Stacks.Sites.associatedModuleMap` of associated presheaves of modules, with the functor laws
`Stacks.Sites.associatedModuleMap_id` and `Stacks.Sites.associatedModuleMap_comp` and the
naturality `AlgebraicGeometry.pullbackSectionsMap_naturality` of the maps on pullback sections
in the module.  All of them are proved in
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor`, together with the sheaf-level
packaging `Stacks.Sites.associatedSheafFunctor`, and are re-exported here, so that consumers of
this module resolve every one of those names unchanged.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/
