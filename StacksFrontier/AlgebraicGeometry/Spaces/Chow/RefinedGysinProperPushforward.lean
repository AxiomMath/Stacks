module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImageDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinModuleIso

/-!
# The refined Gysin map and proper pushforward, up to canonical rational equivalence

In Situation 0EDT let `f : X' ⟶ X` be a proper morphism of good algebraic spaces over `B`, let
`(ℒ, s, i : E → X)` be a triple as in Stacks 0ER1, and form the diagram of Remark 0ER3

```
E' --i'--> X'
|          |
g          f
|          |
v          v
E  --i-->  X
```

with `ℒ' = f^*ℒ`, `s' = f^*s` and `E' = Z(s') = f^{-1}(E)`. Stacks 0ER5 asserts that
`i^* f_* α' = g_* (i')^* α'` in `CH_k(E)` for every `(k+1)`-cycle `α'` on `X'`. The source proves
it on a prime cycle `[W']`, with `W ⊆ X` the closure of the image of `W'`, in two cases:

* `W' ⊄ E'`: then `W ⊄ E`, and `g_*[E' ∩ W']_k = deg(W'/W) [E ∩ W]_k` as cycles, by the first
  assertion of Stacks 0EQS applied to `W' → W`;
* `W' ⊆ E'`: then `W ⊆ E`, and `(f_W)_*(c₁(ℒ'|_{W'}) ∩ [W']) = deg(W'/W) (c₁(ℒ|_W) ∩ [W])` in
  `CH_k(W)`, by the second assertion of Stacks 0EQS;

and concludes for a general cycle by Remark 0EQ8. This file carries out everything but the two
appeals to Stacks 0EQS, at the rational equivalence by canonical principal divisors of
`AlgebraicGeometry.Space.IsCanonicallyRationallyEquivalentToZeroWithin`: the passage from prime
cycles to all cycles, the case matching, the reduction of the contained case to Stacks 0EQT for
the component morphism `f_W : W' → W` (which is how the reduction of Stacks 0EQT in this library
asks for Stacks 0EQS), and the non-contained case when `W` has smaller δ-dimension than `W'`,
where both sides vanish.

## Main results

* `isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_properPushforward_sub_of_component`:
  the reduction of Stacks 0ER5 to prime cycles, for any component rules of Stacks 0ER1.
* `properCyclePushforward_gysinIntersectionCycle_eq_zero_of_deltaDimension_closureImage_ne`:
  `g_*[E' ∩ W']_k = 0` when `W' ⊄ E'` and `dim_δ(W) ≠ dim_δ(W')`.
* `isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_properPushforward_sub_of_le`:
  the contained case, from Stacks 0EQT for `f_W : W' → W`.
* Stacks 0ER5 for the canonical component rules, from the two inputs the source takes from
  Stacks 0EQS, and the same for the refined Gysin homomorphisms of `(ℒ, s)` and `(f^*ℒ, f^*s)`.
* `subspacePointSet_vanishingLocus_pullbackGlobalSection`: `|Z(f^*s)| = |f|⁻¹|Z(s)|`.

## Implementation notes

The source's identity in `CH_k(E)` is stated for every cycle `α'`, as the statement that the
difference of the two sides is canonically rationally equivalent to zero on `E`; the outer
operations are the cycle-level maps `AlgebraicGeometry.Space.gysinCycleMap` and
`AlgebraicGeometry.Space.properCyclePushforward`, so no descent of either to Chow groups is used.

The two inputs `hC` and `hD` of the main results are exactly the two appeals of the source's proof
to Stacks 0EQS: `hD` is the cycle identity of the non-contained case (the first assertion of Stacks
0EQS on `W' → W`, read through `[E ∩ W]_k = div_{ℒ|_W}(s|_W)` of Stacks 0EQF), and `hC` is the
contained case on `W`, in the form in which
`isCanonicallyRationallyEquivalentToZeroWithin_pushforward_firstChernCap_sub_of_comp_ι_eq` asks for
Stacks 0EQT on the component morphisms.

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p')
    (hfqc : IsQuasiCompact D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgqc : IsQuasiCompact D.site D.base D.base_mem g)
    (k : ℤ) (rule : GysinComponentRule D p E k) (rule' : GysinComponentRule D p' E' k)

/-- If `a i * b i j * c i j` is nonzero for finitely many pairs `(i, j)`, then
`a i * ∑ᶠ j, b i j * c i j` is nonzero for finitely many `i`. -/
private theorem hasFiniteSupport_mul_finsum_mul {ι κ : Type*} (a : ι → ℤ) (b : ι → κ → ℤ)
    (c : ι → κ → ℤ) (h : {x : ι × κ | a x.1 * b x.1 x.2 * c x.1 x.2 ≠ 0}.Finite) :
    Function.HasFiniteSupport fun i => a i * ∑ᶠ j, b i j * c i j := by
  refine (h.image Prod.fst).subset fun i hi => ?_
  have hne := Function.mem_support.1 hi
  obtain ⟨j, hj⟩ : ∃ j, b i j * c i j ≠ 0 := by
    by_contra hall
    exact right_ne_zero_of_mul hne (finsum_eq_zero_of_forall_eq_zero fun j =>
      not_not.1 (not_exists.1 hall j))
  refine ⟨(i, j), ?_, rfl⟩
  change a i * b i j * c i j ≠ 0
  rw [mul_assoc]
  exact mul_ne_zero (left_ne_zero_of_mul hne) hj

/-- **The reduction of Stacks 0ER5 to a prime cycle, at canonical rational equivalence.** In the
diagram of Remark 0ER3, with component rules of Stacks 0ER1 on `X` and on `X'`, suppose that for
every integral closed subspace `W' ⊆ X'` of δ-dimension `k + 1`, with `W ⊆ X` the closure of its
image, the cycle

`i^* f_*[W'] - g_* (i')^*[W'] = deg(W'/W) · i^*[W] - g_* (i')^*[W']`

is canonically rationally equivalent to zero on `E`, within the inverse image of `|W|`. Then for
every `(k+1)`-cycle `α'` on `X'` the cycle `i^* f_* α' - g_* (i')^* α'` is canonically rationally
equivalent to zero on `E`. -/
theorem
    isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_properPushforward_sub_of_component
    (h : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
      deltaDimension D p' W' = k + 1 →
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D (E.1.ι ≫ p) hE k
        (properCycleDegree D p' hp' p hp f W' •
            gysinComponentCycle D p E hE k rule
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
                (D.isDecentSpace_of_isGood p hp) f W') -
          properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
            (gysinComponentCycle D p' E' hE' k rule' W'))
        (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
              (D.isDecentSpace_of_isGood p hp) f W').subspace))
    (α' : CycleGroup D p' (k + 1)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D (E.1.ι ≫ p) hE k
      (gysinCycleMap D p E hE k rule
          (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α') -
        properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinCycleMap D p' E' hE' k rule' α'))
      (⋃ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
        if α'.1 W' = 0 then ∅ else
          pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
            subspacePointSet D.site D.base D.base_mem X
              (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
                (D.isDecentSpace_of_isGood p hp) f W').subspace) := by
  classical
  set W := fun W' : IntegralClosedSubspace D.site D.base D.base_mem X' =>
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
      (D.isDecentSpace_of_isGood p hp) f W' with hWdef
  have hlf0 := (locallyFinite_closure_image_pointsMap D p' hp' p hp hfbase hfqc
    (cycleSupportFamily D α'.1) (isClosed_cycleSupportFamily D p' hp' α'.1) α'.2.1).1
  have hloc : LocallyFinite fun W' : IntegralClosedSubspace D.site D.base D.base_mem X' =>
      if α'.1 W' = 0 then (∅ : Set (points D.site D.base D.base_mem E.1.toFunctor)) else
        pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X (W W').subspace := by
    refine (hlf0.preimage_continuous
      (continuous_pointsMap D.site D.base D.base_mem E.1.ι)).subset fun W' => ?_
    split_ifs with hW'
    · exact Set.empty_subset _
    · exact Set.preimage_mono (IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base
        D.base_mem hp.1 (D.isDecentSpace_of_isGood p hp) f W').le
  refine isCycleFamilySumWithin_finsum D (E.1.ι ≫ p) hE k _ hloc
    (fun W' => α'.1 W' • (properCycleDegree D p' hp' p hp f W' •
        gysinComponentCycle D p E hE k rule (W W') -
      properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinComponentCycle D p' E' hE' k rule' W'))) (fun W' => ?_) fun T => ?_
  · split_ifs with hW'
    · rw [hW', zero_smul]
      exact isCycleFamilySumWithin_zero D (E.1.ι ≫ p) hE k _
    · exact (h W' (α'.2.2 W' hW')).zsmul neg_mem_canonicalPrincipalDivisors _
  · have hfin₁ := hasFiniteSupport_mul_finsum_mul (α'.1 ·)
      (properCycleMult D p' hp' p hp f · ·)
      (fun _ W₀ => (gysinComponentCycle D p E hE k rule W₀).1 T)
      (finite_properPushforwardGysinSupport D p hp p' hp' hfbase hfqc E hE k rule α' T)
    have hfin₂ := hasFiniteSupport_mul_finsum_mul (α'.1 ·)
      (fun W' T' => (gysinComponentCycle D p' E' hE' k rule' W').1 T')
      (fun _ T' => properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T)
      (finite_gysinProperPushforwardSupport D p p' hp' E hE E' hE' hgbase hgqc k rule' α' T)
    change (gysinCycleMap D p E hE k rule
        (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α')).1 T -
      (properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k rule' α')).1 T = _
    rw [gysinCoeff_properPushforward D p hp p' hp' hfbase hfqc E hE k rule α' T,
      properPushforward_gysinCoeff D p p' hp' E hE E' hE' hgbase hgqc k rule' α' T,
      ← finsum_sub_distrib hfin₁ hfin₂]
    refine finsum_congr fun W' => ?_
    have hsingle : (∑ᶠ W₀ : IntegralClosedSubspace D.site D.base D.base_mem X,
        properCycleMult D p' hp' p hp f W' W₀ * (gysinComponentCycle D p E hE k rule W₀).1 T) =
        properCycleDegree D p' hp' p hp f W' *
          (gysinComponentCycle D p E hE k rule (W W')).1 T := by
      rw [finsum_eq_single _ (W W') fun W₀ hW₀ => by
        rw [properCycleMult_eq_zero_of_ne D p' hp' p hp f W' (Ne.symm hW₀), zero_mul]]
      unfold properCycleMult
      rw [ite_eq_left rfl]
    rw [hsingle, ← properPushforward_apply D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k]
    rw [AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul, AddSubgroup.coe_sub, Pi.sub_apply,
      AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul, mul_sub]

end Reduction

/-! ### The component cycles of the canonical rules -/

section Canonical

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p')
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgqc : IsQuasiCompact D.site D.base D.base_mem g) (k : ℤ)

/-- For an integral closed subspace `W ⊆ E`, the component cycle of Stacks 0ER1 at the canonical
rule is the pushforward along `W → E` of the extended component cycle
`AlgebraicGeometry.Space.chernComponentCycleOrZero`, whatever the δ-dimension of `W`. -/
theorem gysinComponentCycle_canonicalGysinComponentRule_of_le
    (chern : FirstChernComponentCycleRule D p k)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hWE : W.subspace ≤ E.1) :
    gysinComponentCycle D p E hE k (canonicalGysinComponentRule D p hp E hE k chern) W =
      containedPushforward D p E hE k hWE (chernComponentCycleOrZero D p k chern W) := by
  by_cases hW : deltaDimension D p W = k + 1
  · rw [gysinComponentCycle_of_le D p E hE k _ hW hWE, canonicalGysinComponentRule_chernCycle,
      chernComponentCycleOrZero_of_deltaDimension_eq D p k chern hW]
  · rw [gysinComponentCycle_of_deltaDimension_ne D p E hE k _ hW,
      chernComponentCycleOrZero_of_deltaDimension_ne D p k chern hW, map_zero]

include hfbase in
/-- **The non-contained branch of Stacks 0ER5 when the image drops dimension.** In the diagram of
Remark 0ER3, with `|E'| = |f|⁻¹|E|`, let `W' ⊆ X'` be an integral closed subspace of δ-dimension
`k + 1` not contained in `E'` whose image closure `W ⊆ X` has δ-dimension other than `k + 1`.
Then `g_*[E' ∩ W']_k = 0`; as `f_*[W'] = 0`, both sides of Stacks 0ER5 vanish at `[W']`. -/
theorem properCyclePushforward_gysinIntersectionCycle_eq_zero_of_deltaDimension_closureImage_ne
    (hpt : subspacePointSet D.site D.base D.base_mem X' E'.1 =
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1)
    (hw : g ≫ E.1.ι = E'.1.ι ≫ f)
    {W' : IntegralClosedSubspace D.site D.base D.base_mem X'}
    (hW' : deltaDimension D p' W' = k + 1) (hW'E' : ¬ W'.subspace ≤ E'.1)
    (hdim : deltaDimension D p (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
      (D.isDecentSpace_of_isGood p hp) f W') ≠ k + 1) :
    properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
      (gysinIntersectionCycle D p' hp' E' hE' k W' hW' hW'E') = 0 := by
  set W := IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
    (D.isDecentSpace_of_isGood p hp) f W' with hWdef
  have hWle : deltaDimension D p W ≤ k := by
    have h := IntegralClosedSubspace.deltaDimension_closureImage_le D p' p hp' hp f hfbase W'
    change deltaDimension D p W ≤ _ at h
    omega
  have hWE : ¬ W.subspace ≤ E.1 := not_le_closureImage_of_not_le D p hp p' hp' f E E' hpt W' hW'E'
  refine Subtype.ext (funext fun T => ?_)
  rw [properPushforward_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun T' => ?_
  by_contra hne
  have hc := left_ne_zero_of_mul hne
  have hm := right_ne_zero_of_mul hne
  obtain ⟨hTeq, hdeg⟩ :=
    (properCycleMult_ne_zero_iff D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T).1 hm
  have hT'k : deltaDimension D (E'.1.ι ≫ p') T' = k :=
    (gysinIntersectionCycle D p' hp' E' hE' k W' hW' hW'E').2.2 T' hc
  have hTk : deltaDimension D (E.1.ι ≫ p) T = k := by
    rw [← hTeq, deltaDimension_closureImage_of_properCycleDegree_ne_zero D (E'.1.ι ≫ p') hE'
      (E.1.ι ≫ p) hE g hdeg, hT'k]
  set t := T.ambientGenericPoint D.site D.base D.base_mem with htdef
  have htT : t ∈ subspacePointSet D.site D.base D.base_mem E.1.toFunctor T.subspace := ⟨_, rfl⟩
  have hx : pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι t ∈
      subspacePointSet D.site D.base D.base_mem X W.subspace := by
    rw [← hTeq, IntegralClosedSubspace.subspacePointSet_closureImage] at htT
    refine (closure_minimal ?_ ((isClosed_subspacePointSet_of_isClosedSubspace D hp.1 W.subspace
      W.isClosedSubspace).preimage (continuous_pointsMap D.site D.base D.base_mem E.1.ι))) htT
    rintro - ⟨y, hy, rfl⟩
    have hy' := subspacePointSet_subset_of_gysinIntersectionCycle_ne_zero D p' hp' E' hE' k W' hW'
      hW'E' T' hc hy
    rw [Set.mem_preimage]
    rw [pointsMap_apply_comm D.site D.base D.base_mem hw y, hWdef,
      IntegralClosedSubspace.subspacePointSet_closureImage]
    exact subset_closure ⟨_, hy', rfl⟩
  have hne' : pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι t ≠
      W.ambientGenericPoint D.site D.base D.base_mem := fun h =>
    notMem_subspacePointSet_ambientGenericPoint_of_not_le D hp.1 E.1 E.2 W hWE (h ▸ ⟨t, rfl⟩)
  have hle := inducedDimensionValue_le_of_mem_of_ne D p hp (deltaDimension D p W - 1) W
    (by ring) hx hne'
  have hlqf : IsLocallyQuasiFinite D.site D.base D.base_mem E.1.ι :=
    isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem E.1.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem E.2.2)
  have heq := D.deltaValue_comp_of_isLocallyQuasiFinite hE.1 hp.1 E.1.ι p hlqf hp.2.2 t
  have hTk' : D.deltaValue (E.1.ι ≫ p) t = k := hTk
  change D.deltaValue p _ ≤ _ at hle
  omega

include hfbase in
/-- **The contained branch of Stacks 0ER5, reduced to Stacks 0EQT for the component morphism.**
In the diagram of Remark 0ER3 let `W' ⊆ X'` be an integral closed subspace of δ-dimension `k + 1`
contained in `E'`, so that its image closure `W ⊆ X` lies in `E`
(`AlgebraicGeometry.Space.closureImage_le_of_le`), and let `c₁ ∩ -` on `X` and on `X'` be given by
component rules of Stacks 0EQJ, from which the canonical component rules of Stacks 0ER1 are
formed. Suppose that for every dominant `f_W : W' → W` over `f` the cycle

`(f_W)_*(c₁ ∩ [W']) - deg(W'/W) · (c₁ ∩ [W])` on `W`

is canonically rationally equivalent to zero on `W`; this is Stacks 0EQT for the proper dominant
morphism `f_W` of integral spaces and the cycle `[W']`, in the form in which the reduction
`isCanonicallyRationallyEquivalentToZeroWithin_pushforward_firstChernCap_sub_of_comp_ι_eq` of
Stacks 0EQT asks for it. Then `i^* f_*[W'] - g_* (i')^*[W']` is canonically rationally equivalent
to zero on `E`, within the inverse image of `|W|`. -/
theorem
    isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_properPushforward_sub_of_le
    (hf : IsProper D.site D.base D.base_mem f) (hw : g ≫ E.1.ι = E'.1.ι ≫ f)
    (chern : FirstChernComponentCycleRule D p k) (chern' : FirstChernComponentCycleRule D p' k)
    {W' : IntegralClosedSubspace D.site D.base D.base_mem X'}
    (hW' : deltaDimension D p' W' = k + 1) (hW'E' : W'.subspace ≤ E'.1)
    (hC : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (fW : W'.subspace.toFunctor ⟶ W.subspace.toFunctor)
      (hfW : fW ≫ W.subspace.ι = W'.subspace.ι ≫ f)
      (_hdom : IsDominant D.site D.base D.base_mem fW),
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D (W.subspace.ι ≫ p)
        (isGood_integralClosedSubspace D p hp W) k
        (properCyclePushforward D (W'.subspace.ι ≫ p') (isGood_integralClosedSubspace D p' hp' W')
            (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
            (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hfbase hfW)
            (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hp' hp hf hfW) k
            (chern' W' hW') -
          properCycleDegree D p' hp' p hp f W' • chernComponentCycleOrZero D p k chern W)
        Set.univ) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D (E.1.ι ≫ p) hE k
      (properCycleDegree D p' hp' p hp f W' •
          gysinComponentCycle D p E hE k (canonicalGysinComponentRule D p hp E hE k chern)
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
              (D.isDecentSpace_of_isGood p hp) f W') -
        properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinComponentCycle D p' E' hE' k
            (canonicalGysinComponentRule D p' hp' E' hE' k chern') W'))
      (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
            (D.isDecentSpace_of_isGood p hp) f W').subspace) := by
  have hWE := closureImage_le_of_le D p hp f E E' g hw W' hW'E'
  obtain ⟨fW, hfW⟩ := IntegralClosedSubspace.exists_hom_closureImage D.site D.base D.base_mem hp.1
    (D.isDecentSpace_of_isGood p hp) f W'
  have hdom := IntegralClosedSubspace.isDominant_of_comp_ι_eq_closureImage D.site D.base
    D.base_mem hp.1 (D.isDecentSpace_of_isGood p hp) f W' fW hfW
  have hc := hC _ fW hfW hdom
  generalize IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
    (D.isDecentSpace_of_isGood p hp) f W' = W at fW hfW hdom hWE hc ⊢
  have hWg := isGood_integralClosedSubspace D p hp W
  have hW'g := isGood_integralClosedSubspace D p' hp' W'
  have hsq : fW ≫ Subfunctor.homOfLe hWE = Subfunctor.homOfLe hW'E' ≫ g := by
    rw [← cancel_mono E.1.ι, Category.assoc, Subfunctor.homOfLe_ι, hfW, Category.assoc, hw,
      ← Category.assoc, Subfunctor.homOfLe_ι]
  rw [gysinComponentCycle_canonicalGysinComponentRule_of_le D p hp E hE k chern hWE,
    gysinComponentCycle_of_le D p' E' hE' k _ hW' hW'E', canonicalGysinComponentRule_chernCycle]
  have hpush := properCyclePushforward_cycleGroupClosedPushforward_of_comp_eq D hE' hE hW'g hWg
    (isClosedImmersion_homOfLe_of_le D E' hW'E') (homOfLe_comp_structure D p' E' hW'E')
    (isClosedImmersion_homOfLe_of_le D E hWE) (homOfLe_comp_structure D p E hWE) hsq hgbase hgqc
    (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hfbase hfW)
    (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hp' hp hf hfW) k (chern' W' hW')
  have hpush' : properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (containedPushforward D p' E' hE' k hW'E' (chern' W' hW')) =
      containedPushforward D p E hE k hWE
        (properCyclePushforward D (W'.subspace.ι ≫ p') hW'g (W.subspace.ι ≫ p) hWg
          (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hfbase hfW)
          (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hp' hp hf hfW) k (chern' W' hW')) :=
    hpush
  rw [hpush', ← map_zsmul, ← map_sub]
  have h2 := IsCanonicallyRationallyEquivalentToZeroWithin.closedPushforward (hX := hE)
    (W.subspace.ι ≫ p) hWg (isClosedImmersion_homOfLe_of_le D E hWE)
    (homOfLe_comp_structure D p E hWE) (hc.neg neg_mem_canonicalPrincipalDivisors)
  rw [neg_sub] at h2
  refine IsCycleFamilySumWithin.mono h2 ?_
  rintro _ ⟨w, -, rfl⟩
  rw [Set.mem_preimage, ← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  exact ⟨w, rfl⟩

include hfbase in
/-- **Stacks 0ER5 at canonical rational equivalence, from its two prime-cycle inputs.** In the
diagram of Remark 0ER3, with `|E'| = |f|⁻¹|E|` and `f` proper, let `c₁ ∩ -` on `X` and on `X'` be
given by component rules of Stacks 0EQJ, from which the canonical component rules of Stacks 0ER1
are formed. Suppose:

* (`hC`, the contained branch) for every integral closed subspace `W' ⊆ E'` of δ-dimension
  `k + 1` and every dominant `f_W : W' → W` onto the image closure `W ⊆ X` over `f`, the cycle
  `(f_W)_*(c₁ ∩ [W']) - deg(W'/W) · (c₁ ∩ [W])` is canonically rationally equivalent to zero on
  `W`: Stacks 0EQT for `f_W` and `[W']`, which the source's proof takes from the second assertion
  of Stacks 0EQS;
* (`hD`, the non-contained branch) for every integral closed subspace `W' ⊄ E'` of δ-dimension
  `k + 1` whose image closure `W` has δ-dimension `k + 1`, `g_*[E' ∩ W']_k = deg(W'/W) [E ∩ W]_k`
  as cycles: the identity which the source's proof takes from the first assertion of Stacks 0EQS
  through the identifications `[E ∩ W]_k = div_{ℒ|_W}(s|_W)` of Stacks 0EQF.

Then for every `(k+1)`-cycle `α'` on `X'`

`i^* f_* α' - g_* (i')^* α'`

is canonically rationally equivalent to zero on `E`. The remaining branch, `W' ⊄ E'` with image
closure of smaller δ-dimension, is proved:
`properCyclePushforward_gysinIntersectionCycle_eq_zero_of_deltaDimension_closureImage_ne`. -/
theorem isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_canonical_properPushforward_sub
    (hf : IsProper D.site D.base D.base_mem f)
    (hpt : subspacePointSet D.site D.base D.base_mem X' E'.1 =
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1)
    (hw : g ≫ E.1.ι = E'.1.ι ≫ f)
    (chern : FirstChernComponentCycleRule D p k) (chern' : FirstChernComponentCycleRule D p' k)
    (hC : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
      (hW' : deltaDimension D p' W' = k + 1), W'.subspace ≤ E'.1 →
      ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
        (fW : W'.subspace.toFunctor ⟶ W.subspace.toFunctor)
        (hfW : fW ≫ W.subspace.ι = W'.subspace.ι ≫ f),
        IsDominant D.site D.base D.base_mem fW →
        IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D (W.subspace.ι ≫ p)
          (isGood_integralClosedSubspace D p hp W) k
          (properCyclePushforward D (W'.subspace.ι ≫ p')
              (isGood_integralClosedSubspace D p' hp' W') (W.subspace.ι ≫ p)
              (isGood_integralClosedSubspace D p hp W)
              (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hfbase hfW)
              (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hp' hp hf hfW) k
              (chern' W' hW') -
            properCycleDegree D p' hp' p hp f W' • chernComponentCycleOrZero D p k chern W)
          Set.univ)
    (hD : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
      (hW' : deltaDimension D p' W' = k + 1) (hW'E' : ¬ W'.subspace ≤ E'.1)
      (hW : deltaDimension D p (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f W') = k + 1),
      properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinIntersectionCycle D p' hp' E' hE' k W' hW' hW'E') =
        properCycleDegree D p' hp' p hp f W' •
          gysinIntersectionCycle D p hp E hE k _ hW
            (not_le_closureImage_of_not_le D p hp p' hp' f E E' hpt W' hW'E'))
    (α' : CycleGroup D p' (k + 1)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D (E.1.ι ≫ p) hE k
      (gysinCycleMap D p E hE k (canonicalGysinComponentRule D p hp E hE k chern)
          (properCyclePushforward D p' hp' p hp hfbase hf.2.1.2 (k + 1) α') -
        properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinCycleMap D p' E' hE' k (canonicalGysinComponentRule D p' hp' E' hE' k chern') α'))
      Set.univ := by
  refine
    (isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_properPushforward_sub_of_component
    D p hp p' hp' hfbase hf.2.1.2 E hE E' hE' hgbase hgqc k _ _ (fun W' hW' => ?_) α').mono
    (Set.subset_univ _)
  by_cases hW'E' : W'.subspace ≤ E'.1
  · exact
      isCanonicallyRationallyEquivalentToZeroWithin_gysinComponentCycle_properPushforward_sub_of_le
      D p hp p' hp' hfbase E hE E' hE' hgbase hgqc k hf hw chern chern' hW' hW'E' (hC W' hW' hW'E')
  · have hWE := not_le_closureImage_of_not_le D p hp p' hp' f E E' hpt W' hW'E'
    rw [gysinComponentCycle_of_not_le D p' E' hE' k _ hW' hW'E',
      canonicalGysinComponentRule_intersectionCycle]
    by_cases hW : deltaDimension D p (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hp.1 (D.isDecentSpace_of_isGood p hp) f W') = k + 1
    · rw [gysinComponentCycle_of_not_le D p E hE k _ hW hWE,
        canonicalGysinComponentRule_intersectionCycle, hD W' hW' hW'E' hW, sub_self]
      exact isCycleFamilySumWithin_zero D (E.1.ι ≫ p) hE k _
    · have hdeg : properCycleDegree D p' hp' p hp f W' = 0 := by
        unfold properCycleDegree
        rw [ite_eq_right (by rwa [hW'])]
      rw [hdeg, zero_smul,
        properCyclePushforward_gysinIntersectionCycle_eq_zero_of_deltaDimension_closureImage_ne D p
          hp p' hp' hfbase E hE E' hE' hgbase hgqc k hpt hw hW' hW'E' hW, sub_zero]
      exact isCycleFamilySumWithin_zero D (E.1.ι ≫ p) hE k _

end Canonical

/-! ### Squares of closed subspaces -/

section Square

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The morphism `g : E' ⟶ E` of a commutative square `g ≫ i = i' ≫ f` of closed subspaces is a
morphism over the base when `f` is. -/
theorem comp_structure_of_comp_ι_eq_comp_ι {p : X ⟶ D.space} {p' : X' ⟶ D.space}
    {E : ClosedSubspaces D.site D.base D.base_mem X}
    {E' : ClosedSubspaces D.site D.base D.base_mem X'} {f₀ : X' ⟶ X} (hfbase : f₀ ≫ p = p')
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hw : g ≫ E.1.ι = E'.1.ι ≫ f₀) :
    g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p' := by
  rw [← Category.assoc, hw, Category.assoc, hfbase]

/-- The morphism `g : E' ⟶ E` of a commutative square `g ≫ i = i' ≫ f` of closed subspaces is
quasi-compact when `f` is: `i' ≫ f` is, and `i` is a monomorphism. -/
theorem isQuasiCompact_of_comp_ι_eq_comp_ι {p : X ⟶ D.space} {p' : X' ⟶ D.space}
    (hp : D.IsGood p) (hp' : D.IsGood p') {E : ClosedSubspaces D.site D.base D.base_mem X}
    {E' : ClosedSubspaces D.site D.base D.base_mem X'} {f₀ : X' ⟶ X}
    (hf : IsQuasiCompact D.site D.base D.base_mem f₀)
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hw : g ≫ E.1.ι = E'.1.ι ≫ f₀) :
    IsQuasiCompact D.site D.base D.base_mem g :=
  isQuasiCompact_of_comp_mono D.site D.base D.base_mem g E.1.ι (by
    rw [hw]
    exact isQuasiCompact_comp D.site D.base D.base_mem hp'.1 hp.1 E'.1.ι f₀
      (isQuasiCompact_of_isClosedImmersion D.site D.base D.base_mem E'.1.ι E'.2.1 hp'.1 E'.2.2) hf)

end Square

/-! ### The diagram of Remark 0ER3 for a section -/

section Section

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : (⟨X', hp'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)

/-- **Remark 0ER3 on points.** The vanishing locus `Z(f^*s)` of the pulled-back section has for
point set the inverse image of `|Z(s)|`: it is the inverse image `f^{-1}(Z(s))` as a closed
subspace (`AlgebraicGeometry.Space.zeroScheme_modulePullbackSections`). -/
theorem subspacePointSet_vanishingLocus_pullbackGlobalSection (hL : IsInvertibleSheaf D p hp L) :
    subspacePointSet D.site D.base D.base_mem X'
        (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)).1 =
      pointsMap D.site D.base D.base_mem X' f.hom ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L s).1 := by
  have h : vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
      (pullbackGlobalSection D p hp p' hp' f L s) = _ :=
    zeroScheme_modulePullbackSections D.site D.base D.base_mem ⟨X, hp.1⟩ ⟨X', hp'.1⟩ L hL s f
  rw [h]
  exact subspacePointSet_preimage D.site D.base D.base_mem f.hom _

/-- **Stacks 0ER5 for the refined Gysin homomorphisms of Stacks 0ER1, at canonical rational
equivalence, from its two prime-cycle inputs.** In Situation 0EDT let `f : X' ⟶ X` be a proper
morphism of good algebraic spaces over `B`, let `(ℒ, s, i : E → X)` be as in Stacks 0ER1, and form
the diagram of Remark 0ER3 with `ℒ' = f^*ℒ`, `s' = f^*s`, `E' = Z(s')` and `g : E' ⟶ E`. Given the
inputs `hC` and `hD` of the corresponding statement for the canonical component rules, for the
component cycles `c₁(ℒ|_W) ∩ [W]` and `c₁(ℒ'|_{W'}) ∩ [W']` of Stacks 0ER1, for every
`(k+1)`-cycle `α'` on `X'`

`i^* f_* α' - g_* (i')^* α'`

is canonically rationally equivalent to zero on `E`, the two refined Gysin maps being those of
`AlgebraicGeometry.Space.sectionGysinRule`. The identification `|E'| = |f|⁻¹|E|` is
`AlgebraicGeometry.Space.subspacePointSet_vanishingLocus_pullbackGlobalSection`. -/
theorem
  isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_sectionGysinRule_properPushforward_sub
    (hfbase : f.hom ≫ p = p') (hf : IsProper D.site D.base D.base_mem f.hom)
    (hL : IsInvertibleSheaf D p hp L) (k : ℤ)
    {g : (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)).1.toFunctor ⟶
        (vanishingLocus D p hp L s).1.toFunctor}
    (hw : g ≫ (vanishingLocus D p hp L s).1.ι =
        (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)).1.ι ≫ f.hom)
    (hC : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
      (hW' : deltaDimension D p' W' = k + 1),
      W'.subspace ≤ (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)).1 →
      ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
        (fW : W'.subspace.toFunctor ⟶ W.subspace.toFunctor)
        (hfW : fW ≫ W.subspace.ι = W'.subspace.ι ≫ f.hom),
        IsDominant D.site D.base D.base_mem fW →
        IsCanonicallyRationallyEquivalentToZeroWithin.{u, v} D (W.subspace.ι ≫ p)
          (isGood_integralClosedSubspace D p hp W) k
          (properCyclePushforward D (W'.subspace.ι ≫ p')
              (isGood_integralClosedSubspace D p' hp' W') (W.subspace.ι ≫ p)
              (isGood_integralClosedSubspace D p hp W)
              (IntegralClosedSubspace.comp_structure_of_comp_ι_eq D hfbase hfW)
              (IntegralClosedSubspace.isQuasiCompact_of_comp_ι_eq D hp' hp hf hfW) k
              (restrictedDivisorCycle D p' hp' (pullbackSheaf D p hp p' hp' f L) k
                (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL) W' hW') -
            properCycleDegree D p' hp' p hp f.hom W' •
              chernComponentCycleOrZero D p k (restrictedDivisorCycle D p hp L k hL) W)
          Set.univ)
    (hD : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
      (hW' : deltaDimension D p' W' = k + 1)
      (hW'E' : ¬ W'.subspace ≤ (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)).1)
      (hW : deltaDimension D p (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f.hom W') = k + 1),
      properCyclePushforward D ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _)
          ((vanishingLocus D p hp L s).1.ι ≫ p) (isGood_vanishingLocus D p hp L s)
          (comp_structure_of_comp_ι_eq_comp_ι D hfbase hw)
          (isQuasiCompact_of_comp_ι_eq_comp_ι D hp hp' hf.2.1.2 hw) k
          (gysinIntersectionCycle D p' hp'
            (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)) (isGood_vanishingLocus D p' hp' _ _) k W' hW'
            hW'E') =
        properCycleDegree D p' hp' p hp f.hom W' •
          gysinIntersectionCycle D p hp (vanishingLocus D p hp L s)
            (isGood_vanishingLocus D p hp L s) k _ hW
            (not_le_closureImage_of_not_le D p hp p' hp' f.hom (vanishingLocus D p hp L s)
              (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s))
              (subspacePointSet_vanishingLocus_pullbackGlobalSection D p hp p' hp' f L s hL) W'
              hW'E'))
    (α' : CycleGroup D p' (k + 1)) :
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, max (u + 1) v} D
      ((vanishingLocus D p hp L s).1.ι ≫ p)
      (isGood_vanishingLocus D p hp L s) k
      (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (sectionGysinRule D p hp L s k hL)
          (properCyclePushforward D p' hp' p hp hfbase hf.2.1.2 (k + 1) α') -
        properCyclePushforward D ((vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)).1.ι ≫ p')
          (isGood_vanishingLocus D p' hp' _ _)
          ((vanishingLocus D p hp L s).1.ι ≫ p) (isGood_vanishingLocus D p hp L s)
          (comp_structure_of_comp_ι_eq_comp_ι D hfbase hw)
          (isQuasiCompact_of_comp_ι_eq_comp_ι D hp hp' hf.2.1.2 hw) k
          (gysinCycleMap D p' (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s)) (isGood_vanishingLocus D p' hp' _ _) k
            (sectionGysinRule D p' hp' (pullbackSheaf D p hp p' hp' f L)
              (pullbackGlobalSection D p hp p' hp' f L s) k
              (isInvertibleSheaf_pullbackSheaf D p hp p' hp' f L hL)) α'))
      Set.univ :=
  isCanonicallyRationallyEquivalentToZeroWithin_gysinCycleMap_canonical_properPushforward_sub
    D p hp p' hp' hfbase (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s)
    (vanishingLocus D p' hp' (pullbackSheaf D p hp p' hp' f L)
          (pullbackGlobalSection D p hp p' hp' f L s))
    (isGood_vanishingLocus D p' hp' _ _) (comp_structure_of_comp_ι_eq_comp_ι D hfbase hw)
    (isQuasiCompact_of_comp_ι_eq_comp_ι D hp hp' hf.2.1.2 hw) k hf
    (subspacePointSet_vanishingLocus_pullbackGlobalSection D p hp p' hp' f L s hL) hw _ _ hC hD α'

end Section

end AlgebraicGeometry.Space

end
