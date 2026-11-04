module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated

/-!
# The projective bundle formula for an isomorphism

Proper pushforward along the identity is the identity, and for an isomorphism `π : P → X`, flat of
relative dimension `0`, both halves of the projective bundle formula hold with `n = 0`, whatever
the invertible module: `π_*π^* = id` and `π^*` is surjective. This is the rank one case of
Stacks 0ERV, a projective bundle of an invertible module being an isomorphism onto the base.

## Main results

* `AlgebraicGeometry.Space.properCyclePushforward_id_coe`
* `AlgebraicGeometry.Space.bundleTopPowerIdentity_of_isIso`
* `AlgebraicGeometry.Space.bundleFormulaSurjective_of_isIso`

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

section Identity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- **Proper pushforward along the identity is the identity**, on coefficient families. -/
theorem properCyclePushforward_id_coe (hB : 𝟙 X ≫ sX = sX)
    (hq : IsQuasiCompact D.site D.base D.base_mem (𝟙 X)) (k : ℤ) (α : CycleGroup D sX k) :
    (properCyclePushforward D sX hX sX hX hB hq k α).1 = α.1 := by
  classical
  funext Z'
  have hc := IntegralClosedSubspace.closureImage_id D hX.1 (D.isDecentSpace_of_isGood sX hX)
  rw [properPushforward_apply, finsum_eq_single _ Z' fun Z hZ => ?_]
  · rw [properCycleMult, if_pos (hc Z'), properCycleDegree, if_pos (by rw [hc Z'])]
    have hone : functionFieldDegree D sX hX sX hX (𝟙 X) Z' = 1 :=
      IntegralClosedSubspace.degreeOverClosureImage_eq_one_of_isClosedImmersion D.site D.base
        D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sX hX)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 X)) Z'
    rw [hone, Nat.cast_one, mul_one]
  · rw [properCycleMult, if_neg (by rw [hc Z]; exact hZ), mul_zero]

end Identity

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sP : P ⟶ D.space) (hP : D.IsGood sP)
    (π : P ⟶ X) [IsIso π] (hπB : π ≫ sX = sP)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hrel : HasRelativeDimension 0 D.site D.base D.base_mem π)
    (hp : IsProper D.site D.base D.base_mem π)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- **The top power for an isomorphism**: `π_*π^*α = α`. -/
theorem bundleTopPowerIdentity_of_isIso :
    BundleTopPowerIdentity D sX hX sP hP π hπB 0 hflat hrel hp L hL := by
  intro k α
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso D sX hX sX hX (𝟙 X)
  have hidp : IsProper D.site D.base D.base_mem (𝟙 X) :=
    isProper_of_isClosedImmersion D.site D.base D.base_mem hX.1 hX.1 _
      (isClosedImmersion_of_isIso D.site D.base D.base_mem (𝟙 X))
  congr 1
  refine Subtype.ext ?_
  have h := properCyclePushforward_flatPullbackMap_of_isIso_over D sX hX sX hX sP hP (𝟙 X)
    (Category.id_comp sX) π hπB hidp hp π hπB (Category.comp_id π) k
    (cycleGroupCast D sX (by simp) α)
  have h' := congrArg Subtype.val h
  rw [properCyclePushforward_id_coe] at h'
  refine Eq.trans ?_ h'
  refine coe_properCyclePushforward_congr D sX hX sP hP π hπB hp.2.1.2 rfl _ _ ?_
  simp only [firstChernCapPowCycleMap, cycleGroupCast_coe]
  exact coe_flatPullbackMap_congr D sX hX sP hP π hπB 0 hflat hrel rfl (by simp) _ _ _ _ rfl

/-- **The surjectivity for an isomorphism**: `π^*` is surjective. -/
theorem bundleFormulaSurjective_of_isIso :
    BundleFormulaSurjective D sX hX sP hP π hπB 0 hflat hrel L hL := by
  intro N d hd b
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective b
  have hd0 : d 0 = N := by have := hd 0; simpa using this
  have hψB : inv π ≫ sP = sX := by rw [← hπB, IsIso.inv_hom_id_assoc]
  have hψ := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sX hX (inv π)
  have hid := isFlat_and_hasRelativeDimension_zero_of_isIso D sP hP sP hP (𝟙 P)
  refine ⟨fun i => chowClassCanonical.{u + 1} D sX hX (d i)
    (cycleGroupCast D sX (by rw [Fin.fin_one_eq_zero i, hd0])
      (flatPullbackMap D sX hX sP hP (inv π) hψB 0 hψ.1 hψ.2 N N (by simp) β)), ?_⟩
  simp only [bundleFormulaMap, ProjectiveBundleRelation.bundleSum_apply]
  show chowClassCanonical.{u + 1} D sP hP N _ = chowClassCanonical.{u + 1} D sP hP N β
  congr 1
  refine Subtype.ext ?_
  have h1 := congrArg (fun ψ => (ψ β).1)
    (flatPullbackMap_comp D sP hP sX hX sP hP π (inv π) hπB hψB 0 0 hflat hrel hψ.1 hψ.2 N N
      (by simp))
  refine (Eq.trans ?_ h1.symm).trans ((flatPullbackMap_coe_congr D sP hP sP hP
    (IsIso.hom_inv_id π) _ (Category.id_comp sP) rfl _ hid.1 _ hid.2 N N N N _ (by simp) _ _
    rfl).trans (flatPullbackMap_id_coe D sP hP (Category.id_comp sP) hid.1 hid.2 N N (by simp) β))
  refine (congrArg Subtype.val (add_zero _)).trans ?_
  simp only [firstChernCapPowCycleMap, cycleGroupCast_coe]
  exact coe_flatPullbackMap_congr D sX hX sP hP π hπB 0 hflat hrel (hd0.trans (by simp)) (by simp)
    (hd 0) (by simp) _ _ ((cycleGroupCast_coe D sX _ _).trans
      (coe_flatPullbackMap_congr D sP hP sX hX (inv π) hψB 0 hψ.1 hψ.2 rfl (by simp) _ _ _ _ rfl))

end Iso

end AlgebraicGeometry.Space

end
