module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.DerivedTensor

/-!
# The instances of the tensor bifunctor of étale sheaves of `Λ`-modules, named

`CochainComplex.KFlatBifunctor.derivedBifunctor (etaleModuleTensor Λ X)`, and hence
`Stacks.EtaleCohomology.etaleModuleDerivedTensor Λ X`, takes three instance arguments: additivity
of the bifunctor, additivity in the second variable, and existence of the total complexes of the
tensor bicomplexes. This module states them under names, with the statements in the spelling the
derived tensor product records, so that a module working with `derivedBifunctor (etaleModuleTensor
Λ X)` can make them its preferred instances and every such term is syntactically the unfolding of
`etaleModuleDerivedTensor Λ X`, up to proofs of the same propositions.

## Main results

* `Stacks.EtaleCohomology.etaleModuleTensor_additive`
* `Stacks.EtaleCohomology.etaleModuleTensor_obj_additive`
* `Stacks.EtaleCohomology.etaleModuleTensor_hasTotal_mapBifunctor`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u r

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- The tensor product of étale sheaves of `Λ`-modules is additive in its first variable. -/
theorem etaleModuleTensor_additive : (curriedTensor (EtaleModules.{u, r} Λ X)).Additive :=
  inferInstance

/-- The tensor product of étale sheaves of `Λ`-modules is additive in its second variable. -/
theorem etaleModuleTensor_obj_additive (M : EtaleModules.{u, r} Λ X) :
    ((tensoringLeft (EtaleModules.{u, r} Λ X)).obj M).Additive :=
  inferInstance

/-- The tensor bicomplex of two complexes of étale sheaves of `Λ`-modules has a total complex. -/
theorem etaleModuleTensor_hasTotal_mapBifunctor
    (K₁ K₂ : HomologicalComplex (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) :
    ((((etaleModuleTensor.{u, r} Λ X).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj K₁).obj K₂).HasTotal (ComplexShape.up ℤ) :=
  inferInstance

end Stacks.EtaleCohomology

end
