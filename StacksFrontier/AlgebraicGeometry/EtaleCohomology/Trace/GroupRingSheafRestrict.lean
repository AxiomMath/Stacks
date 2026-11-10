module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingSheafClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange

/-!
# Restriction of the continuous module of a group-ring module

For a continuous homomorphism `φ : G' → G` and a finite `ℤ[G]`-module `T` killed by `n` with open
stabilizers, restricting the continuous module of `T`
(`Stacks.EtaleCohomology.groupRingContinuousModule`) along `φ` is the continuous module of the
restriction `Stacks.EtaleCohomology.GroupRingRestrict φ T`
(`Stacks.EtaleCohomology.groupRingContinuousModuleResIso`). With Tag 0DV6 for lisse sheaves this
identifies the inverse images of the sheaves `Qⱼ` of the model of Laumon's Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) with the sheaves of the restricted simple
subquotients.

## Main results

* `Stacks.EtaleCohomology.groupRingIsContinuous_groupRingRestrict`.
* `Stacks.EtaleCohomology.groupRingContinuousModuleResIso`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidAlgebra Stacks.GroupCohomology

universe v w

namespace Stacks.EtaleCohomology

variable {G G' : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
  [TopologicalSpace G'] [IsTopologicalGroup G'] (n : ℕ) [NeZero n] (φ : G' →ₜ* G)
  {T : Type w} [AddCommGroup T] [Module (MonoidAlgebra ℤ G) T] [Module (ZMod n) T] [Finite T]

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [Finite T] in
/-- The restriction of a module with open stabilizers has open stabilizers. -/
theorem groupRingIsContinuous_groupRingRestrict (hT : GroupRingIsContinuous G T) :
    GroupRingIsContinuous G' (GroupRingRestrict φ.toMonoidHom T) := fun m => by
  have : {g : G' | of ℤ G' g • m = m} =
      φ ⁻¹' {g : G | of ℤ G g • (toGroupRingRestrict φ.toMonoidHom).symm m =
        (toGroupRingRestrict φ.toMonoidHom).symm m} := by
    ext g
    rw [Set.mem_ofPred_eq, groupRingRestrict_of_smul]
    rfl
  rw [this]
  exact (hT _).preimage φ.continuous

/-- **Restricting the continuous module of `T` along `φ` is the continuous module of the
restriction of `T`.** -/
def groupRingContinuousModuleResIso (hT : GroupRingIsContinuous G T) :
    (finiteTypeContinuousModuleRes (ZMod n) φ).obj (groupRingContinuousModule n T hT) ≅
      groupRingContinuousModule n (GroupRingRestrict φ.toMonoidHom T)
        (groupRingIsContinuous_groupRingRestrict φ hT) where
  hom := ObjectProperty.homMk ((homEquiv (ZMod n) G' _ _).symm
    ⟨(toGroupRingRestrict φ.toMonoidHom).toAddMonoidHom.toZModLinearMap n, fun g x =>
      (groupRingRestrict_of_smul (M := T) φ.toMonoidHom g
        (toGroupRingRestrict (M := T) φ.toMonoidHom x)).symm⟩)
  inv := ObjectProperty.homMk ((homEquiv (ZMod n) G' _ _).symm
    ⟨(toGroupRingRestrict φ.toMonoidHom).symm.toAddMonoidHom.toZModLinearMap n, fun g x =>
      congrArg (toGroupRingRestrict (M := T) φ.toMonoidHom).symm
        (groupRingRestrict_of_smul (M := T) φ.toMonoidHom g x)⟩)
  hom_inv_id := continuousModule_hom_ext n fun _ => rfl
  inv_hom_id := continuousModule_hom_ext n fun _ => rfl

end Stacks.EtaleCohomology

end
