module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.StrictCokernel
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.InjectiveEmbedding
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.TowerComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveResolutionDegreeZero.FilteredResolution

/-!
# Filtered injective resolutions of a filtered object

Over an abelian category with enough injectives, a filtered complex concentrated in degree `0`
with finite filtration admits a filtered quasi-isomorphism into a complex of filtered injective
objects vanishing in negative degrees ([Stacks, Tag 05TT]). The development is split into:

* `InjectiveResolutionDegreeZero.StrictCokernel`: cokernels of strict morphisms of filtered
  objects, their filtrations and graded pieces;
* `InjectiveResolutionDegreeZero.InjectiveEmbedding`: a strict monomorphism of a finitely filtered
  object into a filtered injective object;
* `InjectiveResolutionDegreeZero.TowerComplex`: the filtered complex of a tower of filtered
  objects and the comparison map out of a complex concentrated in degree `0`;
* `InjectiveResolutionDegreeZero.FilteredResolution`: [Stacks, Tag 05TS], filtered injective
  resolutions and [Stacks, Tag 05TT].
-/
