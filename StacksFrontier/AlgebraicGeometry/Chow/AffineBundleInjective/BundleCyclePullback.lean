module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.BundleFibre
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange

/-!
# Flat pullback of cycles along an affine-space bundle, pointwise

Let `(S, δ)` be the base situation of chapter 42 and `f : X ⟶ Y` an affine-space bundle of rank
`r` between schemes locally of finite type over `S`. The flat pullback of Stacks 02RB has, at a
point `ξ` of `X`, the coefficient of the cycle at `f ξ` times a multiplicity. For an affine-space
bundle that multiplicity is one at the generic point of a fibre: the scheme-theoretic inverse
image of the closure of a point `y` is again an affine-space bundle over the integral scheme
`closure {y}`, hence integral, and its generic point is the generic point of the fibre over `y`.
So flat pullback of cycles is the pullback `Stacks.Chow.bundleChainPullback` of degree-zero
Milnor K-chains.

## Main results

* `Stacks.Chow.flatPullbackWeight_eq_one_of_isAffineSpaceBundle` — the multiplicity is one at the
  generic point of a fibre.
* `Stacks.Chow.pointwiseCycleEquiv_flatPullback_of_isAffineSpaceBundle` — flat pullback of
  cycles, read pointwise, is the pullback of degree-zero chains.
* `Stacks.Chow.flatPullback_injective_of_isAffineSpaceBundle` — flat pullback of cycles along an
  affine-space bundle is injective.

## References

* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) {r : ℕ}
  (hb : IsAffineSpaceBundle f r)

include hbase hb in
/-- **The flat pullback multiplicity of an affine-space bundle is one at the generic point of a
fibre.** The inverse image of `closure {f ξ}` is an affine-space bundle over that integral
scheme, hence integral, and `ξ` is its generic point; the cycle of an integral scheme has
coefficient one at its generic point. -/
theorem flatPullbackWeight_eq_one_of_isAffineSpaceBundle {ξ : X}
    (hξ : relativeDimension C.dimensionFunction sX ξ =
      relativeDimension C.dimensionFunction sY (f.base ξ) + r) :
    flatPullbackWeight C sX f (relativeDimension C.dimensionFunction sX ξ) ξ = 1 := by
  set W := integralComponentAt (f.base ξ) with hW
  have : IsIntegral W.subscheme := isIntegral_integralComponentAt _
  have : IsIntegral (W.comap f).subscheme :=
    isIntegral_of_isAffineSpaceBundle (comapRestrict W f) r
      (isAffineSpaceBundle_comapRestrict f hb W)
  -- `ξ` lies in the inverse image
  have hmem : ξ ∈ Set.range (W.comap f).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap, Set.mem_preimage,
      hW, coe_support_integralComponentAt]
    exact subset_closure rfl
  obtain ⟨z, hz⟩ := hmem
  -- the image of the generic point of the inverse image is `ξ`
  set g := (W.comap f).subschemeι.base (genericPoint (W.comap f).subscheme) with hg
  have hgξ : g ⤳ ξ := by
    rw [← hz]
    exact (genericPoint_specializes z).map (W.comap f).subschemeι.continuous
  have hfg : f.base g = f.base ξ := by
    have hgmem : g ∈ Set.range (W.comap f).subschemeι.base := ⟨_, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap, Set.mem_preimage,
      hW, coe_support_integralComponentAt] at hgmem
    exact ((hgξ.map f.continuous).antisymm (specializes_iff_mem_closure.mpr hgmem)).eq
  have hξg : ξ ⤳ g :=
    specializes_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sX sY f hbase hb hξ hfg
  have hgeq : g = ξ := (hgξ.antisymm hξg).eq
  have hzgen : z = genericPoint (W.comap f).subscheme :=
    (W.comap f).subschemeι.isEmbedding.injective (hz.trans hgeq.symm)
  have hfz : f.base ((W.comap f).subschemeι.base z) = f.base ξ := by rw [hz]
  have hw := flatPullbackWeight_eq_cycleAssociatedToClosedSubscheme_id C sX f (f.base ξ)
    (relativeDimension C.dimensionFunction sX ξ) z hfz
  rw [hz] at hw
  rw [hw, hzgen]
  have hdim : relativeDimension C.dimensionFunction ((W.comap f).subschemeι ≫ sX)
      ((𝟙 (W.comap f).subscheme : (W.comap f).subscheme ⟶ _).base
        (genericPoint (W.comap f).subscheme)) =
        relativeDimension C.dimensionFunction sX ξ := by
    show relativeDimension C.dimensionFunction ((W.comap f).subschemeι ≫ sX)
      (genericPoint (W.comap f).subscheme) = _
    rw [relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction
        (W.comap f).subschemeι sX _ (bijective_residueFieldMap_of_isClosedImmersion _ _),
      ← hg, hgeq]
  exact cycleAssociatedToClosedSubscheme_isIntegral_apply_genericPoint C
    ((W.comap f).subschemeι ≫ sX) (𝟙 _) _ hdim

include hbase hb in
/-- **Flat pullback of cycles along an affine-space bundle is the pullback of degree-zero Milnor
K-chains.** At a point `ξ` both sides are the coefficient at `f ξ`: when `f ξ` has relative
dimension `k`, the point `ξ` of relative dimension `k + r` is the generic point of its fibre and
the multiplicity there is one; otherwise the coefficient at `f ξ` vanishes. -/
theorem pointwiseCycleEquiv_flatPullback_of_isAffineSpaceBundle [LocallyOfFiniteType f] [Flat f]
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (c : CycleGroup C sY k) :
    pointwiseCycleEquiv C sX (k + r) (flatPullback C sX sY f hbase r hf k c) =
      bundleChainPullback C sX sY f hbase hb k (k + r) rfl 0 (pointwiseCycleEquiv C sY k c) := by
  refine Subtype.ext (funext fun ξ ↦ ?_)
  apply (milnorKTheoryZeroAddEquiv (X.residueField ξ.1)).injective
  rw [pointwiseCycleEquiv_apply, flatPullback_apply]
  by_cases h : f.base ξ.1 ∈ pointsOfDimension C sY k
  · rw [bundleChainPullback_apply_of_mem C sX sY f hbase hb rfl _ ξ h,
      milnorKTheoryZeroAddEquiv_milnorKTransport]
    have hξ : relativeDimension C.dimensionFunction sX ξ.1 =
        relativeDimension C.dimensionFunction sY (f.base ξ.1) + r := by
      rw [(mem_pointsOfDimension C sX).mp ξ.2, (mem_pointsOfDimension C sY).mp h]
    have hw := flatPullbackWeight_eq_one_of_isAffineSpaceBundle C sX sY f hbase hb hξ
    rw [(mem_pointsOfDimension C sX).mp ξ.2] at hw
    rw [hw, mul_one]
    exact (pointwiseCycleEquiv_apply C sY k c ⟨_, h⟩).symm
  · rw [bundleChainPullback_apply_of_notMem C sX sY f hbase hb rfl _ ξ h, map_zero]
    have hc : c.1 (f.base ξ.1) = 0 := by
      by_contra hne
      exact h (mem_pointsOfDimension_of_apply_ne_zero C sY c hne)
    rw [hc, zero_mul]

include hbase hb in
/-- **Flat pullback of cycles along an affine-space bundle is injective.** -/
theorem flatPullback_injective_of_isAffineSpaceBundle [LocallyOfFiniteType f] [Flat f]
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) :
    Function.Injective (flatPullback C sX sY f hbase r hf k) := by
  intro c c' h
  apply (pointwiseCycleEquiv C sY k).injective
  apply bundleChainPullback_zero_injective C sX sY f hbase hb (rfl : k + r = k + r)
  rw [← pointwiseCycleEquiv_flatPullback_of_isAffineSpaceBundle C sX sY f hbase hb hf,
    ← pointwiseCycleEquiv_flatPullback_of_isAffineSpaceBundle C sX sY f hbase hb hf, h]

end Stacks.Chow

end
