module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineSpaceFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSurjectiveAffineFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupMapOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IsomorphismRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RelativeEffectiveCartierFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.Fiber

/-!
# Flat pullback to a line bundle is an isomorphism on Chow groups

In Situation 0EDT let `X/B` be good, let `ℒ` be a finite locally free `𝒪_X`-module of rank one
and let `p : L = \underline{Spec}(Sym^*(ℒ)) → X` be its line bundle. The flat pullback
`p^* : CH_k(X) → CH_{k+1}(L)` on the Chow groups of Stacks 0EQ6 at the canonical embeddings of
Stacks 0ENK is an isomorphism for every `k` (Stacks 0ERH).

The proof is the source's. Surjectivity is Stacks 0ERG: `p` is quasi-compact, flat of relative
dimension one, with fibres `L_x ≅ 𝐀^1_{κ(x)}`; this holds for the vector bundle of a finite
locally free module of any rank `r`, with `p^* : CH_k(X) → CH_{k+r}(E)`. For injectivity, the
zero section `o : X → L` has image an effective Cartier divisor `o(X) ⊆ L`, flat over `X`, and
`o(X)` is the vanishing locus of the canonical section of `𝒪_L(o(X))`. By Stacks 0ERE the Gysin
map `i^*` of this pair satisfies `i^* p^* α = (p|_{o(X)})^* α` in `CH_k(o(X))`, and `i^*`
descends to the Chow groups by Stacks 0ERA. Since `p|_{o(X)} : o(X) → X` is an isomorphism,
flat pullback along it reflects rational equivalence. So `p^* α ∼_rat 0` gives
`(p|_{o(X)})^* α ∼_rat 0` and then `α ∼_rat 0`.

## Main definitions

* `AlgebraicGeometry.Space.flatPullbackChowAddEquivCanonicalLineBundle`: the isomorphism
  `p^* : CH_k(X) ≃+ CH_{k+1}(L)`.

## Main results

* `AlgebraicGeometry.Space.flatPullbackMap_id_coe`: flat pullback along the identity is the
  identity.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_flatPullbackMap_iff_of_isIso`:
  flat pullback along an isomorphism preserves and reflects rational equivalence at the
  canonical embeddings.
* `AlgebraicGeometry.Space.isQuasiCompact_vectorBundleProjection` and
  `AlgebraicGeometry.Space.hasAffineSpaceFibres_vectorBundleProjection`: the projection of the
  vector bundle of a finite locally free module of rank `r` is quasi-compact, with fibres
  `𝐀^r_{κ(x)}`; these are the hypotheses of Stacks 0ERG for it.
* `AlgebraicGeometry.Space.surjective_flatPullbackChowMapCanonical_vectorBundle`: for the vector
  bundle `p : E → X` of a finite locally free module of rank `r`, `p^* : CH_k(X) → CH_{k+r}(E)`
  is surjective.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_of_flatPullbackMap_vectorBundle`:
  for the line bundle `p : L → X`, `p^* α ∼_rat 0` implies `α ∼_rat 0`.
* `AlgebraicGeometry.Space.injective_flatPullbackChowMapCanonical_vectorBundle`: the injectivity
  of `p^* : CH_k(X) → CH_{k+1}(L)`.
* `AlgebraicGeometry.Space.bijective_flatPullbackChowMapCanonical_vectorBundle`: **Stacks 0ERH**.

## Implementation notes

The invertible `𝒪_X`-module `ℒ` of the source is taken as a finite locally free module of rank
one, the hypothesis under which the vector bundle `\underline{Spec}(Sym^*(ℒ))` and its zero
section are constructed; on the locally ringed small étale site the two notions agree
(Stacks 0B8M, 0B8N).

## References

* [Stacks Project, Tag 0ERH](https://stacks.math.columbia.edu/tag/0ERH)
* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 0ERE](https://stacks.math.columbia.edu/tag/0ERE)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Identity

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The closure of the image of an integral closed subspace along the identity is itself. -/
theorem IntegralClosedSubspace.closureImage_id (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec (𝟙 X) W = W := by
  refine IntegralClosedSubspace.eq_of_subspacePointSet_eq D hX ?_
  have h := IntegralClosedSubspace.image_subspacePointSet_eq_inter D.site D.base D.base_mem hX hX
    (isImmersion_of_isOpenImmersion D.site D.base D.base_mem
      (isOpenImmersion_of_isIso D.site D.base D.base_mem (𝟙 X))) W
  rw [pointsMap_id, Set.image_id, Set.range_id, Set.inter_univ] at h
  rw [IntegralClosedSubspace.subspacePointSet_closureImage, pointsMap_id, Set.image_id]
  exact h

/-- **Flat pullback along the identity is the identity**, read on coefficient families: the
identity is an open immersion, along which flat pullback is restriction of cycles, and the
closure of the image of an integral closed subspace along the identity is itself. -/
theorem flatPullbackMap_id_coe (sX : X ⟶ D.space) (hX : D.IsGood sX) (hbase : 𝟙 X ≫ sX = sX)
    (hflat : IsFlat D.site D.base D.base_mem (𝟙 X))
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem (𝟙 X)) (k n : ℤ)
    (hkn : k + ((0 : ℕ) : ℤ) = n) (α : CycleGroup D sX k) :
    (flatPullbackMap D sX hX sX hX (𝟙 X) hbase 0 hflat hr k n hkn α).1 = α.1 := by
  have hj := isOpenImmersion_of_isIso D.site D.base D.base_mem (𝟙 X)
  rw [flatPullbackMap_eq_cycleGroupRestrict D sX hX sX hX hj hbase k n hkn α]
  funext W
  rw [cycleGroupRestrict_apply, IntegralClosedSubspace.closureImage_id]

end Identity

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)

/-- **Flat pullback along an isomorphism preserves and reflects rational equivalence at the
canonical embeddings.** For an isomorphism `j : U → X` of good algebraic spaces over the base,
flat of relative dimension `0`, `j^*α ∼_rat 0` if and only if `α ∼_rat 0`, for every `k`-cycle
`α` on `X`, rational equivalence being read at the canonical embeddings of Stacks 0ENK.

Both directions are Stacks 0EQB: for `j` and for its inverse, with
`(j⁻¹)^* j^* = (j⁻¹ ≫ j)^* = 𝟙^*` the identity by Stacks 0EPA. -/
theorem isRationallyEquivalentToZeroCanonical_flatPullbackMap_iff_of_isIso (j : U ⟶ X) [IsIso j]
    (hjc : j ≫ sX = sU) (hflat : IsFlat D.site D.base D.base_mem j)
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem j) (k n : ℤ)
    (hkn : k + ((0 : ℕ) : ℤ) = n) (α : CycleGroup D sX k) :
    IsRationallyEquivalentToZeroCanonical.{max v (u + 1)} D sU hU n
        (flatPullbackMap D sU hU sX hX j hjc 0 hflat hr k n hkn α) ↔
      IsRationallyEquivalentToZeroCanonical.{max v (u + 1)} D sX hX k α := by
  subst hkn
  refine ⟨fun h => ?_, fun h =>
    isRationallyEquivalentToZeroCanonical_flatPullbackMap.{max v (u + 1)} D sU hU sX hX j hjc 0
      hflat hr k _ rfl h⟩
  have hie : IsEtale D.site D.base D.base_mem (inv j) :=
    isEtale_of_isOpenImmersion D.site D.base D.base_mem
      (isOpenImmersion_of_isIso D.site D.base D.base_mem (inv j))
  have hiflat : IsFlat D.site D.base D.base_mem (inv j) :=
    isFlat_of_isEtale D.site D.base D.base_mem hie
  have hir : HasRelativeDimension 0 D.site D.base D.base_mem (inv j) :=
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem (inv j) hU.1 hie
  have hibase : inv j ≫ sU = sX := by rw [← hjc, IsIso.inv_hom_id_assoc]
  have h' := isRationallyEquivalentToZeroCanonical_flatPullbackMap.{max v (u + 1)} D sX hX sU hU
    (inv j) hibase 0 hiflat hir (k + ((0 : ℕ) : ℤ)) k (by simp) h
  have hcomp := congrArg (fun F => F α)
    (flatPullbackMap_comp D sX hX sU hU sX hX (inv j) j hibase hjc 0 0 hiflat hir hflat hr k k
      (by simp))
  simp only [AddMonoidHom.comp_apply] at hcomp
  have hc := isFlat_and_hasRelativeDimension_comp D sX hX sU hU sX hX (inv j) j hibase hjc 0 0
    hiflat hir hflat hr
  have hid : flatPullbackMap D sX hX sX hX (inv j ≫ j)
      (comp_structureMorphism_eq D sX sU sX (inv j) j hibase hjc) (0 + 0) hc.2.1 hc.2.2 k k
      (by simp) α = α := by
    refine Subtype.ext ?_
    have hidflat : IsFlat D.site D.base D.base_mem (𝟙 X) := IsIso.inv_hom_id j ▸ hc.2.1
    have hidr : HasRelativeDimension 0 D.site D.base D.base_mem (𝟙 X) :=
      IsIso.inv_hom_id j ▸ hc.2.2
    rw [flatPullbackMap_coe_congr D sX hX sX hX (IsIso.inv_hom_id j) _ (Category.id_comp sX)
      (show 0 + 0 = 0 from rfl) _ hidflat _ hidr k k k k (by simp) (by simp) α α rfl]
    exact flatPullbackMap_id_coe D sX hX (Category.id_comp sX) hidflat hidr k k (by simp) α
  rw [hid] at hcomp
  rw [hcomp]
  exact h'

end Iso

section Fibres

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
  (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
  (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- **The projection of a vector bundle is quasi-compact**: it is affine. -/
theorem isQuasiCompact_vectorBundleProjection :
    IsQuasiCompact D.site D.base D.base_mem
      (vectorBundleProjection D.site D.base D.base_mem W F).hom :=
  isQuasiCompact_of_isAffineHom' D.site D.base D.base_mem _
    (vectorBundle D.site D.base D.base_mem W F).obj.left.2 W.2
    (isAffineHom_vectorBundleProjection D.site D.base D.base_mem W F)

/-- **The fibres of a vector bundle are affine spaces.** For the vector bundle `p : E → X` of a
finite locally free `𝒪_X`-module of rank `r` on a good algebraic space `X/B`,
`E_x ≅ 𝐀^r_{κ(x)}` for every `x ∈ |X|`: the fibre hypothesis of Stacks 0ERG for `p`. -/
theorem hasAffineSpaceFibres_vectorBundleProjection (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r] :
    HasAffineSpaceFibres D sW hW (vectorBundleProjection D.site D.base D.base_mem W F).hom r :=
  fun x => BaseSpaceDimensionSituation.exists_isPullback_vectorBundleProjection_residueFieldMorphism
    D W F r (n := ULift.{u} (Fin r)) (by simp) sW hW x

end Fibres

section Surjectivity

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
  (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]
  (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- **Flat pullback to a vector bundle is surjective on Chow groups.** Let `p : E → X` be the
vector bundle of a finite locally free `𝒪_X`-module of rank `r` on a good algebraic space
`X/B`. Then the flat pullback `p^* : CH_k(X) → CH_{k+r}(E)` of Stacks 0EQB, on the Chow groups of
Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK, is surjective for every `k`.

This is Stacks 0ERG for `p`, which is quasi-compact, flat of relative dimension `r`, with fibres
`E_x ≅ 𝐀^r_{κ(x)}`. -/
theorem surjective_flatPullbackChowMapCanonical_vectorBundle (k n : ℤ) (hkn : k + (r : ℤ) = n) :
    Function.Surjective (flatPullbackChowMapCanonical.{u + 1} D _
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl r
      (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F r) k n hkn) := by
  subst hkn
  intro a
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨β, hβ⟩ := isFlatPullbackSurjective_of_isQuasiCompact_of_hasAffineSpaceFibres D _
    (isGood_vectorBundle D W F sW hW) sW hW
    (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl r
    (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
    (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F r)
    (isQuasiCompact_vectorBundleProjection D W F)
    (hasAffineSpaceFibres_vectorBundleProjection D W F sW hW r) k α
  refine ⟨chowClassCanonical.{u + 1} D sW hW k β, ?_⟩
  change chowClassCanonical.{u + 1} D _ (isGood_vectorBundle D W F sW hW) (k + (r : ℤ))
      (flatPullbackMap D _ (isGood_vectorBundle D W F sW hW) sW hW
        (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl r
        (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
        (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F r) k
        (k + (r : ℤ)) rfl β) =
    chowClassCanonical.{u + 1} D _ (isGood_vectorBundle D W F sW hW) (k + (r : ℤ)) α
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  exact IsRationallyEquivalentToZeroCanonical.uliftIndex.{u + 1, u}
    hβ.isRationallyEquivalentToZeroCanonical

end Surjectivity

section LineBundle

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
  (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F 1]
  (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- The restriction to the vanishing locus of the canonical section of `𝒪_L(o(X))` of the
projection `p : L → X` of a line bundle is an isomorphism: that vanishing locus is the zero locus
`o(X)`, on which `p` restricts to the inverse of the zero section. -/
theorem isIso_vanishingLocus_canonicalSection_ι_comp_vectorBundleProjection :
    IsIso ((vanishingLocus D _ (isGood_vectorBundle D W F sW hW)
        (associatedInvertibleSheaf D.site D.base D.base_mem _
          (vectorBundleZeroLocus D.site D.base D.base_mem W F)
          (isEffectiveCartierDivisor_vectorBundleZeroLocus D.site D.base D.base_mem W F))
        (canonicalSection D.site D.base D.base_mem _
          (vectorBundleZeroLocus D.site D.base D.base_mem W F)
          (isEffectiveCartierDivisor_vectorBundleZeroLocus D.site D.base D.base_mem W F))).1.ι ≫
      (vectorBundleProjection D.site D.base D.base_mem W F).hom) := by
  rw [vanishingLocus_canonicalSection_vectorBundleZeroLocus D W F sW hW]
  infer_instance

/-- **Flat pullback to a line bundle reflects rational equivalence**, at the canonical
embeddings of Stacks 0ENK. Let `p : L → X` be the line bundle of a finite locally free
`𝒪_X`-module of rank one on a good algebraic space `X/B`. If the flat pullback `p^* α` of a
`k`-cycle `α` on `X` is rationally equivalent to zero, so is `α`.

This is the injectivity half of Stacks 0ERH, as in the source: with `i : o(X) → L` the zero
locus, the vanishing locus of the canonical section of `𝒪_L(o(X))`, Stacks 0ERE gives
`i^* p^* α = (p|_{o(X)})^* α` in `CH_k(o(X))`, Stacks 0ERA makes `i^*` a homomorphism of Chow
groups, so `(p|_{o(X)})^* α ∼_rat 0`, and `p|_{o(X)}` is an isomorphism. -/
theorem isRationallyEquivalentToZeroCanonical_of_flatPullbackMap_vectorBundle (m n : ℤ)
    (hmn : m + ((1 : ℕ) : ℤ) = n) (α : CycleGroup D sW m)
    (h : IsRationallyEquivalentToZeroCanonical.{u + 1} D _ (isGood_vectorBundle D W F sW hW) n
      (flatPullbackMap D _ (isGood_vectorBundle D W F sW hW) sW hW
        (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl 1
        (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
        (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F 1) m n hmn
        α)) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sW hW m α := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, m = k + 1 := ⟨m - 1, by ring⟩
  obtain rfl : n = k + ((0 : ℕ) : ℤ) + 1 + 1 := by push_cast at hmn ⊢; omega
  set Z := vectorBundleZeroLocus D.site D.base D.base_mem W F
  have hZ := isRelativeEffectiveCartierDivisor_vectorBundleZeroLocus D.site D.base D.base_mem W F
  have hE := isGood_vectorBundle D W F sW hW
  -- the Gysin map of Stacks 0ERA carries `p^* α ∼_rat 0` to `i^* p^* α ∼_rat 0`
  have hgysin := (chowClassCanonical_eq_zero_iff.{u + 1} D _ _ _ _).2
    (gysinCycleMapFactorsThroughRationalEquivalenceCanonical_sectionGysinRule D _ hE
      (associatedInvertibleSheaf D.site D.base D.base_mem _ Z hZ.1)
      (canonicalSection D.site D.base D.base_mem _ Z hZ.1)
      (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem _ Z hZ.1)
      (k + ((0 : ℕ) : ℤ) + 1) _ h)
  -- Stacks 0ERE identifies `i^* p^* α` with `(p|_{o(X)})^* α`
  have h0ERE := chowClassCanonical_gysinCycleMap_canonicalSection_flatPullbackMap.{u + 1} D _ hE
    sW hW (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl 0
    (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
    (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F 1) Z hZ k α
  rw [h0ERE, chowClassCanonical_eq_zero_iff] at hgysin
  have := isIso_vanishingLocus_canonicalSection_ι_comp_vectorBundleProjection D W F sW hW
  exact (isRationallyEquivalentToZeroCanonical_flatPullbackMap_iff_of_isIso.{u + 1} D sW hW _
    (isGood_vanishingLocus D _ hE _ _) _ _ _ _ (k + 1) _ _ α).1 hgysin

/-- **The injectivity half of Stacks 0ERH.** In Situation 0EDT let `X/B` be good, let `ℒ` be a
finite locally free `𝒪_X`-module of rank one and let `p : L = \underline{Spec}(Sym^*(ℒ)) → X`
be its line bundle, flat of relative dimension one. Then the flat pullback
`p^* : CH_k(X) → CH_{k+1}(L)` of Stacks 0EQB, on the Chow groups of Stacks 0EQ6 at the canonical
embeddings of Stacks 0ENK, is injective for every `k`. -/
theorem injective_flatPullbackChowMapCanonical_vectorBundle (k : ℤ) :
    Function.Injective (flatPullbackChowMapCanonical.{u + 1} D _
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl 1
      (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F 1) k (k + 1)
      (by push_cast; rfl)) := by
  intro a b hab
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  change flatPullbackChowMapCanonical.{u + 1} D _ _ sW hW _ rfl 1 _ _ k (k + 1) _
      (chowClassCanonical.{u + 1} D sW hW k α) =
    flatPullbackChowMapCanonical.{u + 1} D _ _ sW hW _ rfl 1 _ _ k (k + 1) _
      (chowClassCanonical.{u + 1} D sW hW k β) at hab
  rw [flatPullbackChowMapCanonical_chowClassCanonical,
    flatPullbackChowMapCanonical_chowClassCanonical,
    chowClassCanonical_eq_iff_rationallyEquivalentCanonical] at hab
  change chowClassCanonical.{u + 1} D sW hW k α = chowClassCanonical.{u + 1} D sW hW k β
  rw [chowClassCanonical_eq_iff_rationallyEquivalentCanonical]
  unfold RationallyEquivalentCanonical at hab ⊢
  rw [← map_sub] at hab
  exact isRationallyEquivalentToZeroCanonical_of_flatPullbackMap_vectorBundle D W F sW hW k (k + 1)
    _ (α - β) hab

/-- **Stacks 0ERH.** In Situation 0EDT let `X/B` be good, let `ℒ` be a finite locally free
`𝒪_X`-module of rank one and let `p : L = \underline{Spec}(Sym^*(ℒ)) → X` be its line bundle,
flat of relative dimension one. Then the flat pullback `p^* : CH_k(X) → CH_{k+1}(L)` of
Stacks 0EQB, on the Chow groups of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK, is an
isomorphism for every `k`. -/
@[stacks 0ERH]
theorem bijective_flatPullbackChowMapCanonical_vectorBundle (k : ℤ) :
    Function.Bijective (flatPullbackChowMapCanonical.{u + 1} D _
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl 1
      (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F 1) k (k + 1)
      (by push_cast; rfl)) :=
  ⟨injective_flatPullbackChowMapCanonical_vectorBundle D W F sW hW k,
    surjective_flatPullbackChowMapCanonical_vectorBundle D W F 1 sW hW k (k + 1) _⟩

/-- The flat pullback `p^* : CH_k(X) ≃+ CH_{k+1}(L)` to the line bundle `L` of a finite locally
free `𝒪_X`-module of rank one, as an isomorphism of Chow groups at the canonical embeddings of
Stacks 0ENK. -/
def flatPullbackChowAddEquivCanonicalLineBundle (k : ℤ) :
    chowGroupCanonical.{u + 1} D sW hW k ≃+
      chowGroupCanonical.{u + 1} D _ (isGood_vectorBundle D W F sW hW) (k + 1) :=
  AddEquiv.ofBijective _ (bijective_flatPullbackChowMapCanonical_vectorBundle D W F sW hW k)

/-- The isomorphism `p^* : CH_k(X) ≃+ CH_{k+1}(L)` sends the class of a cycle to the class of
its flat pullback. -/
theorem flatPullbackChowAddEquivCanonicalLineBundle_chowClassCanonical (k : ℤ)
    (α : CycleGroup D sW k) :
    flatPullbackChowAddEquivCanonicalLineBundle D W F sW hW k
        (chowClassCanonical.{u + 1} D sW hW k α) =
      chowClassCanonical.{u + 1} D _ (isGood_vectorBundle D W F sW hW) (k + 1)
        (flatPullbackMap D _ (isGood_vectorBundle D W F sW hW) sW hW
          (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl 1
          (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
          (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F 1) k (k + 1)
          (by push_cast; rfl) α) :=
  rfl

end LineBundle

end AlgebraicGeometry.Space

end
