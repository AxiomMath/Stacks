module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomSheafDescent

/-!
# Morphisms in the derived category of a disjoint union

This file proves `AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct`, the fact used without
comment in step (S) of the proof of Stacks 0DLC, part (3): for an algebraic space `V` over a
disjoint union `W₀ = ∐ W_k` of schemes of the site, with pieces `V_k = V ×_{W₀} W_k`, the map
`Hom_{D(𝒪_V)}(K, E) ⟶ ∏_k Hom_{D(𝒪_{V_k})}(Lj_k^*K, Lj_k^*E)` is bijective for all `K`, `E`.

The content is in `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedDisjointUnion.lean`:
restriction to the pieces identifies `𝒪_V`-modules with families of `𝒪_{V_k}`-modules, hence
`D(𝒪_V)` with `∏_k D(𝒪_{V_k})`, which is
`AlgebraicGeometry.Space.bijective_mapDerivedCategory_etaleModulePullback_map_of_isPullback_cofan`
on morphisms.
What is added here is the identification of the derived pullback `Lj_k^*` along the étale
morphism `j_k` with the functor that the exact restriction induces on derived categories,
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale`. Nothing is registered.

## Main results

* `AlgebraicGeometry.Space.derivedHomDisjointUnionProduct`: the proposition
  `AlgebraicGeometry.Space.DerivedHomDisjointUnionProduct` holds.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

attribute [local instance] AlgebraicGeometry.Space.etaleModulePullback_additive
  AlgebraicGeometry.Space.preservesFiniteLimits_etaleModulePullback
  AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- **Morphisms in the derived category of a disjoint union**: for an algebraic space `V` over a
disjoint union `W₀ = ∐ W_k` of schemes of the site, with pieces `V_k = V ×_{W₀} W_k` and
projections `j_k : V_k ⟶ V`, and for all `K`, `E` in `D(𝒪_V)`, the map
`Hom(K, E) ⟶ ∏_k Hom(Lj_k^*K, Lj_k^*E)`, `φ ↦ (Lj_k^*φ)_k`, is bijective.

Restriction to the pieces identifies `D(𝒪_V)` with `∏_k D(𝒪_{V_k})`, and each `Lj_k^*` is that
restriction, `j_k` being étale. -/
theorem derivedHomDisjointUnionProduct : DerivedHomDisjointUnionProduct B S hS := by
  intro ι W W₀ w hW V p V' j p' hsq K E
  have hj := isEtale_hom_of_isPullback_cofan hW hsq
  have := fun k => hasDerivedModulePullbacks B S hS (j k)
  exact Functor.bijective_pi_map_of_iso
    (fun k => smallEtaleDerivedModulePullbackIsoEtale B S hS (j k) (hj k))
    (bijective_mapDerivedCategory_etaleModulePullback_map_of_isPullback_cofan hW hsq hj K E)

end AlgebraicGeometry.Space

end
