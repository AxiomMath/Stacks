module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage

/-!
# Exactness of the inverse image of étale sheaves of modules, as instances

The inverse image `etaleModuleInverseImage Λ f` of sheaves of `Λ`-modules on small étale sites
preserves finite limits and finite colimits
(`Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits`,
`Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits`). This file makes both
of them instances.
-/

@[expose] public section

namespace Stacks.EtaleCohomology

attribute [instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

end Stacks.EtaleCohomology

end
