module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCapTransport

/-!
# Flat pullback along the inverse image of an integral closed subspace

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension
`r` and let `W ⊆ Y` be an integral closed subspace.  Write `W' = f^{-1}(W) = W ×_Y X`, a closed
subspace of `X`, with its projection `h : W' ⟶ W`, which is flat of relative dimension `r`
(Stacks 0EPD, second assertion).  This file compares the flat pullback along `f` with the one
along `h`:

* the multiplicity of the image `V' ⊆ X` of an integral closed subspace `V ⊆ W'` in `f^*[W]` is
  the multiplicity of `V` in `h^*[W]`, and an integral closed subspace of `X` which is not such an
  image does not occur in `f^*[W]`;
* the pushforward along `W' ⊆ X` of a locally finite sum of pushforwards from integral closed
  subspaces of `W'` is the corresponding sum of pushforwards from their images in `X`.

## Main results

* `AlgebraicGeometry.Space.integralClosedSubspacePushforward_integralCycle_top`: `[W]` is the
  pushforward of the fundamental cycle of `W` itself.
* `AlgebraicGeometry.Space.flatPullbackMult_preimageComponentImage`: the comparison of
  multiplicities.
* `AlgebraicGeometry.Space.flatPullbackMult_eq_zero_of_forall_ne_preimageComponentImage`: the
  vanishing off the images.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Top

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (W : IntegralClosedSubspace D.site D.base D.base_mem Y)

/-- The image in `Y` of `W`, read as an integral closed subspace of itself, is `W`. -/
theorem IntegralClosedSubspace.pushforward_top_eq :
    IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 W.isClosedSubspace.1
        (D.isDecentSpace_of_isGood sY hY) W.isClosedSubspace.2
        (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
          W.isIntegralSpace) = W := by
  refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
    (IrreducibleCloseds.ext ?_)
  change subspacePointSet D.site D.base D.base_mem Y _ =
    subspacePointSet D.site D.base D.base_mem Y _
  rw [IntegralClosedSubspace.subspacePointSet_pushforward, subspacePointSet,
    IntegralClosedSubspace.range_pointsMap_top, Set.image_univ]

/-- The δ-dimension of `W`, read as an integral closed subspace of itself, is that of `W`. -/
private theorem deltaDimension_top_integralClosedSubspace (hY : D.IsGood sY) :
    deltaDimension D (W.subspace.ι ≫ sY)
      (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
        W.isIntegralSpace) = deltaDimension D sY W :=
  deltaDimension_top D (W.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W)
    W.isIntegralSpace (deltaDimensionClosed_univ_integralClosedSubspace D sY hY W)

/-- **`[W] = i_*[W]`.**  The fundamental cycle of an integral closed subspace `W ⊆ Y` of
δ-dimension `m` is the pushforward along `W ⊆ Y` of the fundamental cycle of `W` itself. -/
theorem integralClosedSubspacePushforward_integralCycle_top {m : ℤ}
    (hW : deltaDimension D sY W = m)
    (htop : deltaDimension D (W.subspace.ι ≫ sY)
      (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
        W.isIntegralSpace) = m) :
    integralClosedSubspacePushforward D sY hY W m
        (integralCycle D (W.subspace.ι ≫ sY) m
          (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
            W.isIntegralSpace) htop) =
      integralCycle D sY m W hW := by
  refine Subtype.ext (funext fun Z => ?_)
  change cycleClosedPushforward D hY.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY)
    W.isClosedSubspace.2 (integralCycleCoeff D _) Z = integralCycleCoeff D W Z
  by_cases hZ : Z = W
  · subst hZ
    have h := cycleClosedPushforward_apply_pushforward D hY.1 Z.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sY hY) Z.isClosedSubspace.2
      (integralCycleCoeff D (IntegralClosedSubspace.top D.site D.base D.base_mem
        Z.isClosedSubspace.1 Z.isIntegralSpace))
      (IntegralClosedSubspace.top D.site D.base D.base_mem Z.isClosedSubspace.1
        Z.isIntegralSpace)
    rw [IntegralClosedSubspace.pushforward_top_eq D sY hY Z, integralCycleCoeff_self] at h
    rw [h, integralCycleCoeff_self]
  · rw [integralCycleCoeff_eq_zero D W hZ]
    by_cases hex : ∃ U, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1
        W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sY hY) W.isClosedSubspace.2 U = Z
    · obtain ⟨U, rfl⟩ := hex
      rw [cycleClosedPushforward_apply_pushforward]
      refine integralCycleCoeff_eq_zero D _ fun hU => hZ ?_
      rw [hU, IntegralClosedSubspace.pushforward_top_eq D sY hY W]
    · exact cycleClosedPushforward_apply_of_forall_ne D hY.1 W.isClosedSubspace.1
        (D.isDecentSpace_of_isGood sY hY) W.isClosedSubspace.2 _ Z fun U hU => hex ⟨U, hU⟩

end Top

section PushforwardSums

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)

/-- **Pushforward along a closed immersion commutes with sums, coefficientwise.**  The
pushforward of a coefficient family which is pointwise a weighted sum `∑ᶠ j, n_j F_j` is
pointwise the weighted sum of the pushforwards.  No finiteness is needed. -/
theorem cycleClosedPushforward_apply_of_eq_finsum {J : Type*} (n : J → ℤ)
    (F : J → IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (G : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (hG : ∀ Z, G Z = ∑ᶠ j, n j * F j Z) (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleClosedPushforward D hX hY hXdec hi G T =
      ∑ᶠ j, n j * cycleClosedPushforward D hX hY hXdec hi (F j) T := by
  by_cases hT :
    ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec hi Z = T
  · obtain ⟨Z, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward, hG]
    exact finsum_congr fun j => by rw [cycleClosedPushforward_apply_pushforward]
  · have h0 := fun G => cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi G T
      fun Z hZ => hT ⟨Z, hZ⟩
    rw [h0]
    exact (finsum_eq_zero_of_forall_eq_zero fun j => by rw [h0, mul_zero]).symm

end PushforwardSums

section Preimage

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)

/-- The flat pullback along the projection `h : f^{-1}(W) ⟶ W` of the fundamental cycle of `W`
itself, as a cycle on `f^{-1}(W)`.  Its coefficient at `V` is the multiplicity of `V` in
`h^{-1}(W) = f^{-1}(W)`. -/
abbrev preimageFlatPullbackMult
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor) : ℤ :=
  flatPullbackMult D ((W.subspace.preimage f).ι ≫ sX)
    (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W)
    (W.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W)
    (W.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase W) r
    (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr W).1
    (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr W).2
    (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
      W.isIntegralSpace) V

/-- **The multiplicity of a component of `f^{-1}(W)` is the same in `X` and in `f^{-1}(W)`.**
The coefficient of the image `V' ⊆ X` of an integral closed subspace `V ⊆ f^{-1}(W)` in `f^*[W]`
is the coefficient of `V` in `h^*[W]` for the projection `h : f^{-1}(W) ⟶ W`. -/
theorem flatPullbackMult_preimageComponentImage
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor) :
    flatPullbackMult D sX hX sY hY f hbase r hflat hr W
        (preimageComponentImage sX hX sY hY f W V) =
      preimageFlatPullbackMult D sX hX sY hY f hbase r hflat hr W V := by
  have htop := deltaDimension_top_integralClosedSubspace D sY W hY
  have h := congrArg (fun c => c.1 (preimageComponentImage sX hX sY hY f W V))
    (flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward D sX hX sY hY f hbase r
      hflat hr W (deltaDimension D sY W) (deltaDimension D sY W + (r : ℤ)) rfl
      (integralCycle D (W.subspace.ι ≫ sY) (deltaDimension D sY W)
        (IntegralClosedSubspace.top D.site D.base D.base_mem W.isClosedSubspace.1
          W.isIntegralSpace) htop))
  rw [integralClosedSubspacePushforward_integralCycle_top D sY hY W rfl htop,
    flatPullbackMap_integralCycle] at h
  rw [h]
  change cycleClosedPushforward D hX.1 _ (D.isDecentSpace_of_isGood sX hX) _ _
    (preimageComponentImage sX hX sY hY f W V) = _
  rw [cycleClosedPushforward_apply_pushforward]
  exact flatPullbackMap_integralCycle D _ _ _ _ _ _ r _ _ _ _ rfl _ htop V

/-- An integral closed subspace of `X` which is not the image of one of `f^{-1}(W)` does not occur
in `f^*[W]`. -/
theorem flatPullbackMult_eq_zero_of_forall_ne_preimageComponentImage
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor,
      preimageComponentImage sX hX sY hY f W V ≠ T) :
    flatPullbackMult D sX hX sY hY f hbase r hflat hr W T = 0 :=
  closedSubspaceCycle_apply_eq_zero_of_forall_ne D sX hX _ _ _ _ T hT

/-- **Carrying a cycle on `V ⊆ f^{-1}(W)` out to `X`.**  Pushing a cycle on an integral closed
subspace `V` of `f^{-1}(W)` forward to `f^{-1}(W)` and then to `X` is transporting it to the image
`V' ⊆ X` and pushing forward from there. -/
theorem integralClosedSubspacePushforward_preimageComponentImage_coe {m : ℤ}
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (d : CycleGroup D (V.subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX) m) :
    (integralClosedSubspacePushforward D sX hX (preimageComponentImage sX hX sY hY f W V) m
        (IntegralClosedSubspace.pushforwardCycleTransport D sX hX
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2 V m d)).1 =
      cycleClosedPushforward D hX.1
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
        (D.isDecentSpace_of_isGood sX hX)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2
        (integralClosedSubspacePushforward D ((W.subspace.preimage f).ι ≫ sX)
          (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V m d).1 := by
  have hP := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W
  have hPdec : IsDecentSpace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor :=
    D.isDecentSpace_of_isGood _ (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W)
  refine Eq.trans (cycleClosedPushforward_comp D hX.1
    (preimageComponentImage sX hX sY hY f W V).isClosedSubspace.1
    V.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX)
    (preimageComponentImage sX hX sY hY f W V).isIntegralSpace.isDecentSpace
    (isClosedImmersion_of_isIso D.site D.base D.base_mem
      (preimageComponentIso sX hX sY hY f W V).hom)
    (preimageComponentImage sX hX sY hY f W V).isClosedSubspace.2 d.1).symm ?_
  refine Eq.trans ?_ (cycleClosedPushforward_comp D hX.1 hP.1 V.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) hPdec V.isClosedSubspace.2 hP.2 d.1)
  exact cycleClosedPushforward_congr D hX.1 V.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) _ _
    (IntegralClosedSubspace.pushforwardIso_hom_comp_ι D.site D.base D.base_mem hX.1 hP.1
      (D.isDecentSpace_of_isGood sX hX) hP.2 V) d.1

/-- An integral closed subspace of `f^{-1}(W)` occurring in `h^*[W]` has δ-dimension `r` more than
`W`. -/
theorem deltaDimension_of_preimageFlatPullbackMult_ne_zero
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : preimageFlatPullbackMult D sX hX sY hY f hbase r hflat hr W V ≠ 0) :
    deltaDimension D ((W.subspace.preimage f).ι ≫ sX) V = deltaDimension D sY W + (r : ℤ) := by
  rw [deltaDimension_eq_of_flatPullbackMult_ne_zero D _ _ _ _ _ _ r _ _ _ V hV,
    deltaDimension_top_integralClosedSubspace D sY W hY]

/-- The δ-dimension of an integral closed subspace of `f^{-1}(W)` occurring in `h^*[W]`, read on
the subspace itself. -/
theorem deltaDimensionClosed_of_preimageFlatPullbackMult_ne_zero {k : ℤ}
    (hW : deltaDimension D sY W = k + 1)
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : preimageFlatPullbackMult D sX hX sY hY f hbase r hflat hr W V ≠ 0) :
    deltaDimensionClosed D (V.subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX)
        (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
          (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V)
        Set.univ isClosed_univ = ((k + (r : ℤ) + 1 : ℤ) : EInt) := by
  rw [deltaDimensionClosed_univ_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
    (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V,
    deltaDimension_of_preimageFlatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W V hV, hW]
  congr 1
  ring

/-- The image in `X` of an integral closed subspace of `f^{-1}(W)` occurring in `h^*[W]` has
δ-dimension `r` more than `W`. -/
theorem deltaDimension_preimageComponentImage_of_ne_zero {k : ℤ}
    (hW : deltaDimension D sY W = k + 1)
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : preimageFlatPullbackMult D sX hX sY hY f hbase r hflat hr W V ≠ 0) :
    deltaDimension D sX (preimageComponentImage sX hX sY hY f W V) = k + (r : ℤ) + 1 := by
  rw [IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1
      (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
      (D.isDecentSpace_of_isGood sX hX)
      (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2 V,
    deltaDimension_of_preimageFlatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W V hV, hW]
  ring

/-- The δ-dimension of an integral closed subspace `V` of `f^{-1}(W)`, read on `V` itself. -/
theorem deltaDimensionClosed_preimageComponent {m : ℤ}
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : deltaDimension D ((W.subspace.preimage f).ι ≫ sX) V = m) :
    deltaDimensionClosed D (V.subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX)
        (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
          (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V)
        Set.univ isClosed_univ = ((m : ℤ) : EInt) := by
  rw [deltaDimensionClosed_univ_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
    (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) V, hV]

/-- The image in `X` of an integral closed subspace of `f^{-1}(W)` has the δ-dimension of that
subspace. -/
theorem deltaDimension_preimageComponentImage
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor) :
    deltaDimension D sX (preimageComponentImage sX hX sY hY f W V) =
      deltaDimension D ((W.subspace.preimage f).ι ≫ sX) V :=
  IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1
    (D.isDecentSpace_of_isGood sX hX)
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).2 V

/-- **The multiplicity of a component of `f^{-1}(W)` in `f^*[W]` is its multiplicity in
`f^{-1}(W)`**, the length of `𝒪_{f^{-1}(W)}` at a geometric point over its generic point
(Stacks 0EE9), for an integral closed subspace of `f^{-1}(W)` of δ-dimension `dim_δ(W) + r`. -/
theorem flatPullbackMult_preimageComponentImage_eq_geometricLength
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : deltaDimension D sX (preimageComponentImage sX hX sY hY f W V) =
      deltaDimension D sY W + (r : ℤ)) :
    flatPullbackMult D sX hX sY hY f hbase r hflat hr W
        (preimageComponentImage sX hX sY hY f W V) =
      ((geometricLength D.site D.base D.base_mem
        ⟨(W.subspace.preimage f).toFunctor,
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W).1⟩
        (canonicalGeometricPoint D.site D.base D.base_mem (W.subspace.preimage f).toFunctor
          (V.ambientGenericPoint D.site D.base D.base_mem))
        (SheafOfModules.unit _)).toNat : ℤ) :=
  (closedSubspaceCycle_apply_closedSubspaceComponentImage D sX hX _
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) _
    (deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY f hbase r hflat hr W)
    V).trans (ite_eq_left hV)

include hbase hflat hr in
/-- **An integral closed subspace of `f^{-1}(W)` of the maximal δ-dimension is an irreducible
component of `f^{-1}(W)`.**  An integral closed subspace `V ⊆ f^{-1}(W)` whose image in `X` has
δ-dimension `dim_δ(W) + r` has for its point set an irreducible component of `|f^{-1}(W)|`. -/
theorem mem_irreducibleComponents_of_deltaDimension_preimageComponentImage
    (V : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : deltaDimension D sX (preimageComponentImage sX hX sY hY f W V) =
      deltaDimension D sY W + (r : ℤ)) :
    subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f).toFunctor V.subspace ∈
      irreducibleComponents
        (points D.site D.base D.base_mem (W.subspace.preimage f).toFunctor) := by
  have hP := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W
  obtain ⟨C, hC⟩ := exists_irreducibleComponents_closedSubspaceComponentImage D sX hX _ hP _
    (deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY f hbase r hflat hr W)
    V hV
  have hemb := (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
    hP.2).isEmbedding
  let e := hemb.toHomeomorph
  have hpre : e ⁻¹' (C : Set _) =
      subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f).toFunctor V.subspace := by
    ext x
    have h1 : (e x : points D.site D.base D.base_mem X) =
        pointsMap D.site D.base D.base_mem _ (W.subspace.preimage f).ι x := rfl
    have h2 : pointsMap D.site D.base D.base_mem _ (W.subspace.preimage f).ι x ∈
          subspacePointSet D.site D.base D.base_mem X
            (closedSubspaceComponentImage D sX hX _ hP V).subspace ↔
        x ∈ subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f).toFunctor
          V.subspace := by
      rw [IntegralClosedSubspace.subspacePointSet_pushforward]
      exact hemb.injective.mem_set_image
    rw [Set.mem_preimage, ← h2, hC, ← h1]
    exact (Subtype.val_injective.mem_set_image).symm
  rw [← hpre]
  refine preimage_mem_irreducibleComponents C.2 e.isOpenEmbedding ?_
  obtain ⟨c, hc⟩ := C.2.1.1
  exact ⟨c, hc, e.surjective c⟩

/-- **The defect at `W` is rationally equivalent to zero inside `f^{-1}(W)`, given the expansion
of `h^*(c₁(ℒ|_W) ∩ [W])` over the components of `f^{-1}(W)`.**  Let `W ⊆ Y` be an integral closed
subspace of δ-dimension `k + 1` and `h : f^{-1}(W) ⟶ W` the projection.  Let `(V_j)_{j ∈ J}` be a
locally finite family of distinct integral closed subspaces of `f^{-1}(W)` of δ-dimension
`k + r + 1`, with integers `n_j`, such that the coefficient of `f^*[W]` at the image of `V_j` in
`X` is `n_j` and every integral closed subspace of `X` occurring in `f^*[W]` is such an image.
Suppose that the flat pullback along `h` of the chosen component cycle `div_{ℒ|_W}(s)` is,
coefficientwise, `∑_j n_j · (V_j → f^{-1}(W))_* div_{g_j^*(ℒ|_W)}(σ_j)`, with `g_j : V_j ⟶ W`
lifting `V_j → X → Y` and `σ_j` regular meromorphic sections — the identity of Stacks 0EQQ for
`h`, with `σ_j = g_j^*s`.  Then for every `a : ℤ` the cycle
`a · (f^*(c₁(ℒ) ∩ [W]) - c₁(f^*ℒ) ∩ f^*[W])` is rationally equivalent to zero, at the canonical
embeddings of Stacks 0ENK, by integral closed subspaces of `X` lying in `f^{-1}(|W|)`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_zsmul_flatChernDefect_of_finsum
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (k : ℤ) (hW : deltaDimension D sY W = k + 1) {J : Type (u + 1)}
    (V : J → IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hVinj : Function.Injective V) (n : J → ℤ)
    (hn : ∀ j, flatPullbackMult D sX hX sY hY f hbase r hflat hr W
      (preimageComponentImage sX hX sY hY f W (V j)) = n j)
    (hcover : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X,
      flatPullbackMult D sX hX sY hY f hbase r hflat hr W T ≠ 0 →
        ∃ j, preimageComponentImage sX hX sY hY f W (V j) = T)
    (hVfin : LocallyFinite fun j =>
      subspacePointSet D.site D.base D.base_mem (W.subspace.preimage f).toFunctor (V j).subspace)
    (hVdim : ∀ j, deltaDimension D ((W.subspace.preimage f).ι ≫ sX) (V j) = k + (r : ℤ) + 1)
    (g : ∀ j, (⟨(V j).subspace.toFunctor, (V j).isClosedSubspace.1⟩ :
          AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩)
    (hg : ∀ j, (g j).hom ≫ W.subspace.ι = (V j).subspace.ι ≫ (W.subspace.preimage f).ι ≫ f)
    (σ : ∀ j, MeromorphicSection.{u, u} D.site D.base D.base_mem (V j).subspace.toFunctor
      (V j).isClosedSubspace.1
      ((modulePullback D.site D.base D.base_mem (g j)).obj
        (integralClosedSubspaceRestrict D sY hY L W)))
    (hσ : ∀ j, IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem
      (V j).subspace.toFunctor (V j).isClosedSubspace.1
      ((modulePullback D.site D.base D.base_mem (g j)).obj
        (integralClosedSubspaceRestrict D sY hY L W)) (σ j))
    (hsum : ∀ Z, (flatPullbackMap D ((W.subspace.preimage f).ι ≫ sX)
        (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W)
        (W.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W)
        (W.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase W) r
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr W).1
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr W).2
        k (k + (r : ℤ)) rfl (canonicalFirstChernRule D sY hY L hL k W hW)).1 Z =
      ∑ᶠ j, n j *
        (integralClosedSubspacePushforward D ((W.subspace.preimage f).ι ≫ sX)
          (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) (V j) (k + (r : ℤ))
          (canonicalDivisorCycleAt D ((V j).subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX)
            (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX)
              (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W) (V j))
            (V j).isIntegralSpace
            ((modulePullback D.site D.base D.base_mem (g j)).obj
              (integralClosedSubspaceRestrict D sY hY L W))
            (modulePullbackInvertible (g j) (integralClosedSubspaceRestrict D sY hY L W)
              (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL W))
            (σ j) (hσ j)
            (deltaDimensionClosed_preimageComponent D sX hX sY hY f W (V j) (hVdim j)))).1 Z)
    (a : ℤ) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX (k + (r : ℤ))
      (a • flatChernDefect D sX hX sY hY f hbase r hflat hr k
        (canonicalFirstChernRule D sY hY L hL k)
        (canonicalFirstChernRule D sX hX
          ((modulePullback D.site D.base D.base_mem
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩)).obj L)
          (modulePullbackInvertible
            (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
              ⟨Y, hY.1⟩) L hL) (k + (r : ℤ))) W hW)
      (pointsMap D.site D.base D.base_mem X f ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y W.subspace) := by
  classical
  have hP := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W
  have hPg := isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f W
  have hdec := D.isDecentSpace_of_isGood sX hX
  let V' : J → IntegralClosedSubspace D.site D.base D.base_mem X := fun j =>
    preimageComponentImage sX hX sY hY f W (V j)
  have hdim : ∀ j, deltaDimension D sX (V' j) = k + (r : ℤ) + 1 := fun j =>
    (deltaDimension_preimageComponentImage D sX hX sY hY f W (V j)).trans (hVdim j)
  let d : ∀ j, CycleGroup D ((V j).subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX) (k + (r : ℤ)) :=
    fun j => canonicalDivisorCycleAt D ((V j).subspace.ι ≫ (W.subspace.preimage f).ι ≫ sX)
      (isGood_integralClosedSubspace D ((W.subspace.preimage f).ι ≫ sX) hPg (V j))
      (V j).isIntegralSpace
      ((modulePullback D.site D.base D.base_mem (g j)).obj
        (integralClosedSubspaceRestrict D sY hY L W))
      (modulePullbackInvertible (g j) (integralClosedSubspaceRestrict D sY hY L W)
        (isInvertibleModule_integralClosedSubspaceRestrict D sY hY L hL W))
      (σ j) (hσ j) (deltaDimensionClosed_preimageComponent D sX hX sY hY f W (V j) (hVdim j))
  let N := (modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩)).obj L
  have hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N :=
    modulePullbackInvertible
      (ObjectProperty.homMk f : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨Y, hY.1⟩) L hL
  let c : ∀ j, CycleGroup D ((V' j).subspace.ι ≫ sX) (k + (r : ℤ)) := fun j =>
    (-(a * n j)) •
      (canonicalFirstChernRule D sX hX N hN (k + (r : ℤ)) (V' j) (hdim j) -
        IntegralClosedSubspace.pushforwardCycleTransport D sX hX hP.1 hP.2 (V j) (k + (r : ℤ))
          (d j))
  have hfin : LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem X (V' j).subspace :=
    locallyFinite_subspacePointSet_pushforward D.site D.base D.base_mem hX.1 hP.1 hdec hP.2 V hVfin
  refine ⟨J, V', hfin, c, fun j => ?_, hdim, fun j => ?_, ?_⟩
  · change subspacePointSet D.site D.base D.base_mem X
      (preimageComponentImage sX hX sY hY f W (V j)).subspace ⊆ _
    rw [IntegralClosedSubspace.subspacePointSet_pushforward, ← subspacePointSet_preimage]
    exact Set.image_subset_range _ _
  · exact isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_preimageComponent sX hX
      sY hY f L W (V j) hL (k + (r : ℤ)) (g j) (hg j) (hdim j) (σ j) (hσ j) _ _
  refine Subtype.ext (funext fun T => ?_)
  have hA : (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
      (firstChernComponentCycle D sY hY k (canonicalFirstChernRule D sY hY L hL k) W)).1 T =
      ∑ᶠ j, n j *
        (integralClosedSubspacePushforward D sX hX (V' j) (k + (r : ℤ))
          (IntegralClosedSubspace.pushforwardCycleTransport D sX hX hP.1 hP.2 (V j) (k + (r : ℤ))
            (d j))).1 T := by
    rw [firstChernComponentCycle_of_deltaDimension_eq D sY hY k _ hW,
      flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward D sX hX sY hY f hbase r
        hflat hr W k (k + (r : ℤ)) rfl]
    change cycleClosedPushforward D hX.1 hP.1 hdec hP.2 _ T = _
    rw [cycleClosedPushforward_apply_of_eq_finsum D hX.1 hP.1 hdec hP.2 n
      (fun j => (integralClosedSubspacePushforward D _ hPg (V j) (k + (r : ℤ)) (d j)).1) _ hsum T]
    exact finsum_congr fun j => by
      rw [integralClosedSubspacePushforward_preimageComponentImage_coe]
  have hB : (firstChernCapCycleMap D sX hX (k + (r : ℤ))
      (canonicalFirstChernRule D sX hX N hN (k + (r : ℤ)))
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k + 1) (k + (r : ℤ) + 1) (by ring)
        (integralCycle D sY (k + 1) W hW))).1 T =
      ∑ᶠ j, n j * (firstChernComponentCycle D sX hX (k + (r : ℤ))
        (canonicalFirstChernRule D sX hX N hN (k + (r : ℤ))) (V' j)).1 T := by
    rw [firstChernCapCycleMap_apply, finsum_congr fun T' => by
      rw [flatPullbackMap_integralCycle D sX hX sY hY f hbase r hflat hr (k + 1)
        (k + (r : ℤ) + 1) (by ring) W hW T']]
    have hinj : Function.Injective V' := fun j j' hjj' => hVinj
      (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 hP.1 hdec hP.2
        hjj')
    rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq' _ (Set.range V') Set.univ ?_,
      finsum_mem_range hinj]
    · exact finsum_congr fun j => by rw [hn j]
    · intro T' hT'
      simp only [Set.mem_univ, iff_true]
      exact hcover T' (left_ne_zero_of_mul hT')
  have hξ : T.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X T.subspace :=
    ⟨T.genericPoint D.site D.base D.base_mem, rfl⟩
  have hfx : (Function.support fun j => n j *
      (integralClosedSubspacePushforward D sX hX (V' j) (k + (r : ℤ))
        (IntegralClosedSubspace.pushforwardCycleTransport D sX hX hP.1 hP.2 (V j) (k + (r : ℤ))
          (d j))).1 T).Finite :=
    (hfin.point_finite (T.ambientGenericPoint D.site D.base D.base_mem)).subset fun j hj =>
      subspacePointSet_subset_of_pushforward_ne_zero D sX hX (V' j) (k + (r : ℤ)) _ T
        (right_ne_zero_of_mul hj) hξ
  have hfy : (Function.support fun j => n j *
      (firstChernComponentCycle D sX hX (k + (r : ℤ))
        (canonicalFirstChernRule D sX hX N hN (k + (r : ℤ))) (V' j)).1 T).Finite :=
    (hfin.point_finite (T.ambientGenericPoint D.site D.base D.base_mem)).subset fun j hj =>
      subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX (k + (r : ℤ)) _ (V' j) T
        (right_ne_zero_of_mul hj) hξ
  have hc : ∀ j, (integralClosedSubspacePushforward D sX hX (V' j) (k + (r : ℤ)) (c j)).1 T =
      -(a * n j) *
        ((firstChernComponentCycle D sX hX (k + (r : ℤ))
            (canonicalFirstChernRule D sX hX N hN (k + (r : ℤ))) (V' j)).1 T -
          (integralClosedSubspacePushforward D sX hX (V' j) (k + (r : ℤ))
            (IntegralClosedSubspace.pushforwardCycleTransport D sX hX hP.1 hP.2 (V j) (k + (r : ℤ))
              (d j))).1 T) := fun j => by
    rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX (k + (r : ℤ)) _ (hdim j)]
    change (integralClosedSubspacePushforward D sX hX (V' j) (k + (r : ℤ))
      ((-(a * n j)) • _)).1 T = _
    rw [map_zsmul, map_sub, AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul,
      AddSubgroup.coe_sub, Pi.sub_apply]
  rw [cycleFamilySum_apply, finsum_congr hc, flatChernDefect, AddSubgroup.coe_zsmul, Pi.smul_apply,
    smul_eq_mul, AddSubgroup.coe_sub, Pi.sub_apply, hA, hB, ← finsum_sub_distrib hfx hfy,
    mul_finsum]
  exact finsum_congr fun j => by ring

end Preimage

end AlgebraicGeometry.Space

end
