module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Exactness of the inverse image of étale sheaves of modules, as global instances

The inverse image `etaleModuleInverseImage Λ f` of sheaves of `Λ`-modules on small étale sites
preserves finite colimits and finite limits
(`Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits`,
`Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits`). This file makes both of
them instances.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

attribute [instance] Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteColimits
attribute [instance] Stacks.EtaleCohomology.etaleModuleInverseImage_preservesFiniteLimits

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [local instance] preservesFiniteLimits_lan_op_smallEtaleBaseChange_module

end Stacks.EtaleCohomology

end
