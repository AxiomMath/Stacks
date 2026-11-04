module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Big and small sites for the standard topologies on schemes

For a scheme `S`, the big `τ`-site is a chosen category of schemes over `S`, equipped with the
fppf, syntomic, smooth, étale, or Zariski coverings. The small étale and Zariski sites are the
full subcategories on schemes étale and open over `S` respectively, with coverings inherited
from the big sites.

## Main definitions

The big categories, their covering families, and their generated topologies are
`AlgebraicGeometry.BigFppfOver`, `AlgebraicGeometry.BigSyntomicOver`,
`AlgebraicGeometry.BigSmoothOver`, `AlgebraicGeometry.BigEtaleOver` and
`AlgebraicGeometry.BigZariskiOver`. The two small sites are `AlgebraicGeometry.SmallEtale` and
`AlgebraicGeometry.SmallZariski`.

## Implementation notes

Each site is registered through its existing category, covering predicate and Grothendieck
topology. The big-site registrations give part (1) of the source definition. The small-site
registrations give part (2): the small categories are full subcategories cut out by the
structure morphism, and their covering predicates pull back the corresponding big-site
predicate along the canonical full inclusion. Thus no second copy of any site is made.

## References

* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
-/

@[expose] public section

add_to_stacks 03XB "big fppf category" AlgebraicGeometry.BigFppfOver
add_to_stacks 03XB "big fppf coverings" AlgebraicGeometry.BigFppfOver.IsCovering
add_to_stacks 03XB "big fppf topology" AlgebraicGeometry.BigFppfOver.topology

add_to_stacks 03XB "big syntomic category" AlgebraicGeometry.BigSyntomicOver
add_to_stacks 03XB "big syntomic coverings" AlgebraicGeometry.BigSyntomicOver.IsCovering
add_to_stacks 03XB "big syntomic topology" AlgebraicGeometry.BigSyntomicOver.topology

add_to_stacks 03XB "big smooth category" AlgebraicGeometry.BigSmoothOver
add_to_stacks 03XB "big smooth coverings" AlgebraicGeometry.BigSmoothOver.IsCovering
add_to_stacks 03XB "big smooth topology" AlgebraicGeometry.BigSmoothOver.topology

add_to_stacks 03XB "big étale category" AlgebraicGeometry.BigEtaleOver
add_to_stacks 03XB "big étale coverings" AlgebraicGeometry.BigEtaleOver.IsCovering
add_to_stacks 03XB "big étale topology" AlgebraicGeometry.BigEtaleOver.topology

add_to_stacks 03XB "big Zariski category" AlgebraicGeometry.BigZariskiOver
add_to_stacks 03XB "big Zariski coverings" AlgebraicGeometry.BigZariskiOver.IsCovering
add_to_stacks 03XB "big Zariski topology" AlgebraicGeometry.BigZariskiOver.topology

add_to_stacks 03XB "small étale category" AlgebraicGeometry.SmallEtale
add_to_stacks 03XB "small étale coverings" AlgebraicGeometry.SmallEtale.IsCovering
add_to_stacks 03XB "small étale topology" AlgebraicGeometry.SmallEtale.topology

add_to_stacks 03XB "small Zariski category" AlgebraicGeometry.SmallZariski
add_to_stacks 03XB "small Zariski coverings" AlgebraicGeometry.SmallZariski.IsCovering
add_to_stacks 03XB "small Zariski topology" AlgebraicGeometry.SmallZariski.topology

/-!
## The four sites named in the étale cohomology chapter

For a scheme `S`, the big étale site `(Sch/S)_étale`, the small étale site `S_étale`, and the
big and small Zariski sites `(Sch/S)_Zar` and `S_Zar` are, by definition, the étale and
Zariski instances of the sites above. Each is registered by its category, its covering
families and the topology they generate.

### References

* [Stacks Project, Tag 03PI](https://stacks.math.columbia.edu/tag/03PI)
-/

add_to_stacks 03PI "big étale site (Sch/S)_étale, category" AlgebraicGeometry.BigEtaleOver
add_to_stacks 03PI "big étale site (Sch/S)_étale, coverings"
  AlgebraicGeometry.BigEtaleOver.IsCovering
add_to_stacks 03PI "big étale site (Sch/S)_étale, topology"
  AlgebraicGeometry.BigEtaleOver.topology

add_to_stacks 03PI "small étale site S_étale, category" AlgebraicGeometry.SmallEtale
add_to_stacks 03PI "small étale site S_étale, coverings" AlgebraicGeometry.SmallEtale.IsCovering
add_to_stacks 03PI "small étale site S_étale, topology" AlgebraicGeometry.SmallEtale.topology

add_to_stacks 03PI "big Zariski site (Sch/S)_Zar, category" AlgebraicGeometry.BigZariskiOver
add_to_stacks 03PI "big Zariski site (Sch/S)_Zar, coverings"
  AlgebraicGeometry.BigZariskiOver.IsCovering
add_to_stacks 03PI "big Zariski site (Sch/S)_Zar, topology"
  AlgebraicGeometry.BigZariskiOver.topology

add_to_stacks 03PI "small Zariski site S_Zar, category" AlgebraicGeometry.SmallZariski
add_to_stacks 03PI "small Zariski site S_Zar, coverings"
  AlgebraicGeometry.SmallZariski.IsCovering
add_to_stacks 03PI "small Zariski site S_Zar, topology" AlgebraicGeometry.SmallZariski.topology
