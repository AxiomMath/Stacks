module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageSystem

/-!
# The transition maps of the tower rings are compatible with the limit

The maps `C_k^∧ ⟶ C^∧` of the descended system of a stage witness
(`AlgebraicGeometry.Artin.LimitStages.towerToLimit`) are compatible with the transition maps
`C_k^∧ ⟶ C_{k'}^∧`.

## Main results

* `towerSystem_map_comp_towerToLimit`: For `k' ⟶ k` in `Over k₀`, the transition map
  `C_k^∧ ⟶ C_{k'}^∧` followed by `C_{k'}^∧ ⟶ C^∧` is the map `C_k^∧ ⟶ C^∧`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat} {k₀ : I} (W : StageWitness c κ ξ w k₀)
  [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]
  [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  {I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)}

/-- For a morphism `f : k' ⟶ k` in `Over k₀`, the transition map `C_k^∧ ⟶ C_{k'}^∧` of
`towerSystem W I₀` followed by `towerToLimit W I₀ k'` equals `towerToLimit W I₀ k`. -/
theorem towerSystem_map_comp_towerToLimit {k k' : Over k₀} (f : k' ⟶ k) :
    (towerSystem W I₀).map f.op ≫ towerToLimit W I₀ k' = towerToLimit W I₀ k := by
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  exact congrArg (fun φ => φ x) (towerRingMap_stageHom_comp_toLimit (I₀ := I₀) W f)

end AlgebraicGeometry.Artin.LimitStages

end
