module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.DepthThreeCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.DepthThreeImprovementInputs
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoSystem

/-!
# The canonical depth-three improvement of a coherent formal module on `U`

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and let `δ^Y_Z` be the distance of a point of `Y` from
`Z`. Assume `A` has a dualizing complex and let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`.

Following the proof of [Stacks, Tag 0EJG], the depth-two improvement of [Stacks, Tag 0EJF] is
taken on `U`, along the closed subscheme `U ∩ Y`, with `T = {y ∈ U ∩ Y : δ^Y_Z(y) ≤ 2}` and
`T' = {y ∈ U ∩ Y : δ^Y_Z(y) ≤ 1}`. This gives the canonical map `(ℱₙ) ⟶ (ℱ''ₙ)` of inverse
systems of coherent `𝒪_U`-modules, and here are proved conclusion (1) of the source,
`depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` on `U ∩ Y`, and conclusion (4), finiteness of
`H⁰(U, ℱ''ₙ)` and `H¹(U, ℱ''ₙ)`.

## Main definitions

* `Stacks.Algebraization.depthThreeImprovedSystem`: the system `(ℱ''ₙ)`.
* `Stacks.Algebraization.toDepthThreeImprovedSystem`: the canonical map `(ℱₙ) ⟶ (ℱ''ₙ)`.

## Main results

* `Stacks.Algebraization.three_le_depth_add_distanceToZ_depthThreeImprovedSystem`:
  conclusion (1).
* `Stacks.Algebraization.depth_depthThreeImprovedSystem_eq_top_of_notMem`: off `U ∩ Y` the
  stalks of the terms of `(ℱ''ₙ)` have infinite depth.
* `Stacks.Algebraization.finite_complementSheafCohomology_depthThreeImprovedSystem` and
  `Stacks.Algebraization.finite_complementGlobalSections_depthThreeImprovedSystem`:
  conclusion (4).

## Implementation notes

The hypotheses of the construction hold here: `U` locally has a dualizing complex, the two loci
lie in `U ∩ Y` and are stable under specialization, and condition (e) of [Stacks, Tag 0EJF] holds
because `δ^Y_Z` grows by at most one along an immediate specialization of the catenary `Y`.

Finiteness of the cohomology is
`Stacks.Algebraization.finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ`,
which needs conclusion (1) and that the stalks of `ℱ''ₙ` vanish off `U ∩ Y`: off `T'` the
extension `ℱ'ₙ ⟶ ℱ''ₙ` is an isomorphism on stalks, and `ℱ'ₙ` is a quotient of `ℱₙ`, which
vanishes off the support of `I𝒪_U`.

## References

* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace IsLocalRing
open Stacks.LocalCohomology

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The inverse system `(ℱ''ₙ)` of [Stacks, Tag 0EJG]: the depth-two improvement of
[Stacks, Tag 0EJF] on `U` along `T = {δ^Y_Z ≤ 2}` and `T' = {δ^Y_Z ≤ 1}`. -/
public abbrev depthThreeImprovedSystem : ℕᵒᵖ ⥤ S.U.toScheme.Modules :=
  canonicalImprovedSystem (S.hasDualizingComplexOnAffineCover_U hdual) F
    (S.stableUnderSpecialization_distanceToZSublevel 2)
    (S.stableUnderSpecialization_distanceToZSublevel 1)
    (S.distanceToZSublevel_subset_support 2)
    (S.forall_mem_distanceToZSublevel_two_of_isImmediateSpecialization hdual)

/-- The canonical map `(ℱₙ) ⟶ (ℱ''ₙ)` of inverse systems of coherent `𝒪_U`-modules. -/
public abbrev toDepthThreeImprovedSystem : F.obj ⟶ depthThreeImprovedSystem S hdual F :=
  toCanonicalImprovedSystem (S.hasDualizingComplexOnAffineCover_U hdual) F
    (S.stableUnderSpecialization_distanceToZSublevel 2)
    (S.stableUnderSpecialization_distanceToZSublevel 1)
    (S.distanceToZSublevel_subset_support 2)
    (S.forall_mem_distanceToZSublevel_two_of_isImmediateSpecialization hdual)

/-- The terms of `(ℱ''ₙ)` are coherent. -/
public instance isCoherent_depthThreeImprovedSystem_obj (n : ℕᵒᵖ) :
    ((depthThreeImprovedSystem S hdual F).obj n).IsCoherent :=
  isCoherent_canonicalImprovedSystem_obj _ F _ _ _ _ n

/-- **Conclusion (1) of [Stacks, Tag 0EJG].** `depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` at every point
`y` of `U ∩ Y`. -/
public theorem three_le_depth_add_distanceToZ_depthThreeImprovedSystem (n : ℕᵒᵖ)
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z) :
    (3 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk y)
        (maximalIdeal (S.U.toScheme.presheaf.stalk y))
        (((depthThreeImprovedSystem S hdual F).obj n).presheaf.stalk y) +
      S.distanceToZ z := by
  obtain ⟨hA, hB⟩ := depth_stalk_canonicalImprovedSystem _ F _ _ _ _ n y
  exact S.three_le_add_distanceToZ y z hyz _ hA hB

/-- Off `U ∩ Y` the terms of `(ℱ''ₙ)` have stalks of infinite depth. -/
public theorem depth_depthThreeImprovedSystem_eq_top_of_notMem (n : ℕᵒᵖ) (y : S.U.toScheme)
    (hy : ∀ z : S.Y, S.U.ι.base y ≠ S.Yι.base z) :
    Module.depth (S.U.toScheme.presheaf.stalk y)
        (maximalIdeal (S.U.toScheme.presheaf.stalk y))
        (((depthThreeImprovedSystem S hdual F).obj n).presheaf.stalk y) = ⊤ := by
  have hsupp : y ∉ (idealOnOpen S).support := fun h => by
    obtain ⟨z, hz⟩ := (S.mem_support_idealOnOpen_iff y).mp h
    exact hy z hz
  let D := canonicalDepthTwoImprovement (S.hasDualizingComplexOnAffineCover_U hdual) F
    (S.stableUnderSpecialization_distanceToZSublevel 2)
    (S.stableUnderSpecialization_distanceToZSublevel 1)
    (S.distanceToZSublevel_subset_support 2)
    (S.forall_mem_distanceToZSublevel_two_of_isImmediateSpecialization hdual)
  have hyT' : y ∉ S.distanceToZSublevel 1 := fun h =>
    hsupp (S.distanceToZSublevel_subset_support 1 h)
  have hiso := (D.extend_isDepthTwoExtension n).2.1 y hyT'
  let : Module (S.U.toScheme.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((improvedSystem (S.distanceToZSublevel 2)
          (S.stableUnderSpecialization_distanceToZSublevel 2) F.obj).obj n).val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.U.toScheme.presheaf) _ y
  let : Module (S.U.toScheme.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (D.term n).val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.U.toScheme.presheaf) _ y
  have hbij : Function.Bijective
      (stalkMapLinear (R := S.U.toScheme.presheaf) _ _ (D.extend n).val y) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hiso
  have htop : Module.depth (S.U.toScheme.presheaf.stalk y)
      (maximalIdeal (S.U.toScheme.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((improvedSystem (S.distanceToZSublevel 2)
          (S.stableUnderSpecialization_distanceToZSublevel 2) F.obj).obj n).val.presheaf y) = ⊤ :=
    depth_improvedSystem_stalk_eq_top_of_notMem_support F
      (S.distanceToZSublevel 2) (S.stableUnderSpecialization_distanceToZSublevel 2)
      (S.distanceToZSublevel_subset_support 2) n y hsupp
  have heq := @Module.depth_eq_depth_of_linearEquiv _ _
    (maximalIdeal (S.U.toScheme.presheaf.stalk y)) _ _ _
    (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.U.toScheme.presheaf) _ y) _
    (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.U.toScheme.presheaf) _ y)
    (LinearEquiv.ofBijective _ hbij)
  exact heq.symm.trans htop

/-- **Conclusion (4) of [Stacks, Tag 0EJG], in degrees `0` and `1`.** `H^p(U, ℱ''ₙ)` is a
finite `A`-module for `p ≤ 1`. -/
public theorem finite_complementSheafCohomology_depthThreeImprovedSystem (n : ℕᵒᵖ) (p : ℕ)
    (hp : p ≤ 1) :
    Module.Finite S.A
      ((complementSheafCohomology S.A S.a p).obj ((depthThreeImprovedSystem S hdual F).obj n)) :=
  finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ S hdual _
    (depth_depthThreeImprovedSystem_eq_top_of_notMem S hdual F n)
    (three_le_depth_add_distanceToZ_depthThreeImprovedSystem S hdual F n) p hp

/-- **Conclusion (4) of [Stacks, Tag 0EJG], degree `0` as sections.** `Γ(U, ℱ''ₙ)` is a finite
`A`-module. -/
public theorem finite_complementGlobalSections_depthThreeImprovedSystem (n : ℕᵒᵖ) :
    Module.Finite S.A (complementGlobalSections S.A S.a
      (show (complementZeroLocus S.A S.a : Scheme).Modules from
        (depthThreeImprovedSystem S hdual F).obj n)) :=
  finite_complementGlobalSections_of_three_le_depth_add_distanceToZ S hdual _
    (depth_depthThreeImprovedSystem_eq_top_of_notMem S hdual F n)
    (three_le_depth_add_distanceToZ_depthThreeImprovedSystem S hdual F n)

end Stacks.Algebraization

end
