module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion

/-!
# Flat pullback along an affine-space fibration is surjective on Chow groups

In Situation 0EDT let `X, Y/B` be good and let `f : X → Y` be a quasi-compact morphism over the
base, flat of relative dimension `r`, with `X_y ≅ 𝐀^r_{κ(y)}` for every `y ∈ |Y|`. Then
`f^* : CH_k(Y) → CH_{k+r}(X)` is surjective (Stacks 0ERG): every `α ∈ Z_{k+r}(X)` is rationally
equivalent to `f^*β` for some `β ∈ Z_k(Y)`, rational equivalence being read at the canonical
embeddings of Stacks 0ENK.

The proof is the source's, carried out in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineBundleSurjectivity` from the compatibility
`f^*(i_*β) = i'_*(f'^*β)` of flat pullback with pushforward along the inclusion `i : Z → Y` of a
closed subspace, `f' : f^{-1}(Z) → Z` being the base change of `f` and `i' : f^{-1}(Z) → X` the
inclusion. That compatibility is the closed-immersion case of the third assertion of
Stacks 0EPD: a closed immersion is proper (Stacks 04XZ), the square formed by `f`, `i`, `f'` and
`i'` is cartesian, and along a closed immersion the proper pushforward of Stacks 0EP1 is the
pushforward of the localization sequence.

## Main results

* `AlgebraicGeometry.Space.flatPullbackMap_cycleGroupClosedPushforward`: `f^*(i_*β) = i'_*(f'^*β)`
  for the inclusion `i` of a closed subspace and a flat `f`.
* `AlgebraicGeometry.Space.flatPullbackClosedPushforwardCompatible`: flat pullback commutes with
  pushforward along closed subspaces, for every flat morphism of good spaces over the base.
* `AlgebraicGeometry.Space.isFlatPullbackSurjective_of_isQuasiCompact_of_hasAffineSpaceFibres`:
  **Stacks 0ERG**.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineBundleSurjectivity`, surjectivity of
`f^* : CH_k(Y) → CH_{k+r}(X)` is read on cycles: every `α ∈ Z_{k+r}(X)` has some
`β ∈ Z_k(Y)` with `f^*β - α` a locally finite sum of canonical principal divisors
`div_W(g)` (Stacks 0ENK, 0EQ6); by Stacks 0EQ8 such a cycle is rationally equivalent to zero.

## References

* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section ClosedPushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Flat pullback commutes with pushforward along a closed subspace.** Let `f : X → Y` be a
morphism of good algebraic spaces over the base, flat of relative dimension `r`, let `Z ⊆ Y` be
a closed subspace with inclusion `i`, and let `f' : f^{-1}(Z) → Z` and `i' : f^{-1}(Z) → X` be
the base change of `f` and the inclusion. Then `f^*(i_*β) = i'_*(f'^*β)` in `Z_{m+r}(X)` for
every `m`-cycle `β` on `Z`.

This is the third assertion of Stacks 0EPD
(`AlgebraicGeometry.Space.flatPullback_properPushforward_unconditional`) for the cartesian square
`CategoryTheory.Subfunctor.isPullback_preimage`, the inclusion `i` being proper by Stacks 04XZ,
read through `AlgebraicGeometry.Space.properCyclePushforward_ι_eq_cycleGroupClosedPushforward` on
both sides. -/
theorem flatPullbackMap_cycleGroupClosedPushforward (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (Z : Subfunctor Y)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (m : ℤ) (β : CycleGroup D (Z.ι ≫ sY) m) :
    flatPullbackMap D sX hX sY hY f hbase r hflat hr m (m + (r : ℤ)) rfl
        (cycleGroupClosedPushforward D hY.1 hZ.1 (D.isDecentSpace_of_isGood sY hY) hZ.2 sY hY.2.2
          (Z.ι ≫ sY) rfl m β) =
      cycleGroupClosedPushforward D hX.1
        (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ).1
        (D.isDecentSpace_of_isGood sX hX)
        (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ).2 sX hX.2.2
        ((Z.preimage f).ι ≫ sX) rfl (m + (r : ℤ))
        (flatPullbackMap D ((Z.preimage f).ι ≫ sX)
          (isGood_ι_of_isClosedSubspace D sX hX _
            (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ))
          (Z.ι ≫ sY) (isGood_ι_of_isClosedSubspace D sY hY Z hZ) (Z.fromPreimage f)
          (fromPreimage_comp_structureMorphism D sX sY f hbase Z) r
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase Z hZ r
            hflat hr).1
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase Z hZ r
            hflat hr).2
          m (m + (r : ℤ)) rfl β) := by
  have hPc := isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ
  have hproper : IsProper D.site D.base D.base_mem Z.ι :=
    isProper_of_isClosedImmersion D.site D.base D.base_mem hZ.1 hY.1 Z.ι hZ.2
  rw [← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sY hY Z hZ m β,
    ← properCyclePushforward_ι_eq_cycleGroupClosedPushforward D sX hX (Z.preimage f) hPc
      (m + (r : ℤ)) _]
  exact flatPullback_properPushforward_unconditional D ((Z.preimage f).ι ≫ sX)
    (isGood_ι_of_isClosedSubspace D sX hX _ hPc) (Z.ι ≫ sY)
    (isGood_ι_of_isClosedSubspace D sY hY Z hZ) sX hX sY hY
    (fromPreimage_comp_structureMorphism D sX sY f hbase Z) rfl rfl hbase r hflat hr
    (Subfunctor.isPullback_preimage f Z) hproper m (m + (r : ℤ)) rfl β

/-- Flat pullback of cycles commutes with pushforward along the inclusion of a closed subspace,
for every flat morphism of good algebraic spaces over the base: the closed-immersion case of the
third assertion of Stacks 0EPD. -/
theorem flatPullbackClosedPushforwardCompatible : FlatPullbackClosedPushforwardCompatible D :=
  fun _ _ sX hX sY hY f hbase r hflat hr Z hZ m β =>
    flatPullbackMap_cycleGroupClosedPushforward D sX hX sY hY f hbase r hflat hr Z hZ m β

end ClosedPushforward

section AffineSpaceFibres

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- **Stacks 0ERG.** In Situation 0EDT let `X, Y/B` be good and let `f : X → Y` be a
quasi-compact morphism over the base, flat of relative dimension `r`, with
`X_y ≅ 𝐀^r_{κ(y)}` for every `y ∈ |Y|`. Then `f^* : CH_k(Y) → CH_{k+r}(X)` is surjective: for
every `k ∈ ℤ` and every `α ∈ Z_{k+r}(X)` there is `β ∈ Z_k(Y)` with `f^*β - α` rationally
equivalent to zero, as a locally finite sum of principal divisors at the canonical embeddings of
Stacks 0ENK. -/
@[stacks 0ERG]
theorem isFlatPullbackSurjective_of_isQuasiCompact_of_hasAffineSpaceFibres
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) (hfib : HasAffineSpaceFibres D sY hY f r)
    (k : ℤ) : IsFlatPullbackSurjective D sX hX sY hY f hbase r hflat hr k :=
  isFlatPullbackSurjective_of_hasAffineSpaceFibres D sX hX sY hY f hbase r hflat hr
    (flatPullbackClosedPushforwardCompatible D) hqc hfib k

end AffineSpaceFibres

end AlgebraicGeometry.Space

end
