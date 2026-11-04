module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.CategoryTheory.SubfunctorFactor

/-!
# The component rule of the refined Gysin map, built from the cycle of the intersection

In Situation 0EDT let `X/B` be good, let `E ⊆ X` be a closed subspace with its closed immersion
`i : E → X`, and let `k ∈ ℤ`.  The refined Gysin map of Stacks 0ER1,
`AlgebraicGeometry.Space.gysinCycleMap`, is built from a
`AlgebraicGeometry.Space.GysinComponentRule`, whose two fields are the two component cycles
Stacks 0ER1(1) prescribes: the cycle `[E ∩ W]_k` of Stacks 0EE9 for an integral closed subspace
`W ⊆ X` of δ-dimension `k + 1` not contained in `E`, and the cap product `c₁(ℒ|_W) ∩ [W]` of
Stacks 0EQJ for one contained in `E`.

This file builds an inhabitant of that structure whose first field is *the* cycle of
Stacks 0EE9, namely `AlgebraicGeometry.Space.closedSubspaceCycle` of the scheme-theoretic
intersection `E ∩ W = i^{-1}(W)` read as a closed subspace of `E`, and whose second field is
the component datum of Stacks 0EQJ, namely
`AlgebraicGeometry.Space.FirstChernComponentCycleRule`.  So the component rule is not free
data: once the two inputs of Stacks 0EQJ and Stacks 0EE9 are fixed, the rule is determined, and
`AlgebraicGeometry.Space.gysinCycleMap` applied to it is a map between cycle groups attached to
`(X, E, ℒ)` and to nothing else.

## Main definitions

* `AlgebraicGeometry.Space.gysinIntersectionSubspace`: the scheme-theoretic intersection
  `E ∩ W = i^{-1}(W)` of `E` with an integral closed subspace `W ⊆ X`, as a closed subspace of
  `E`.  This is the object whose `k`-cycle is clause (1)(a) of Stacks 0ER1.
* `AlgebraicGeometry.Space.gysinIntersectionCycle`: the `k`-cycle `[E ∩ W]_k` on `E` of
  Stacks 0EE9, which is clause (1)(a) itself.
* `AlgebraicGeometry.Space.canonicalGysinComponentRule`: the component rule of Stacks 0ER1 with
  clause (1)(a) given by that cycle and clause (1)(b) by the component datum of Stacks 0EQJ.

## Main results

* `AlgebraicGeometry.Space.le_of_subspacePointSet_subset_of_integral`: **Stacks 03JJ for an
  integral closed subspace.**  An integral closed subspace whose point set is inside the point
  set of a closed subspace `E` is contained in `E` scheme-theoretically.  Hence
  `AlgebraicGeometry.Space.notMem_subspacePointSet_ambientGenericPoint_of_not_le`: one *not*
  contained in `E` does not have its generic point on `E`.
* `AlgebraicGeometry.Space.le_preimage_of_flatPullbackMult_ne_zero` and
  `AlgebraicGeometry.Space.closureImage_le_of_le`: **the case matching of Stacks 0ER5 and
  Stacks 0ER6.**  A subspace occurring in a flat pullback of `[W]` for `W ⊆ E` is contained in
  the base change `f^{-1}(E)`, and the image closure of a subspace contained in `E'` is
  contained in `E`.  These are the two scheme-theoretic containments the source's case analyses
  need and which a point-set containment does not give without integrality.
* `AlgebraicGeometry.Space.inducedDimensionValue_lt_of_mem_of_ne`: the induced dimension
  function of a good space is strictly smaller at a point of an integral closed subspace other
  than its generic point than it is at that generic point.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le`:
  **the δ-dimension bound that makes clause (1)(a) legitimate.**  If `dim_δ(W) = k + 1` and
  `W ⊄ E`, then `dim_δ(E ∩ W) ≤ k`, so the cycle `[E ∩ W]_k` of Stacks 0EE9 exists.
* `AlgebraicGeometry.Space.subspacePointSet_subset_of_gysinIntersectionCycle_ne_zero`: the
  support property that `AlgebraicGeometry.Space.GysinComponentRule` asks of clause (1)(a) —
  the cycle `[E ∩ W]_k` is carried by `i^{-1}(W)` — proved rather than assumed.
* `AlgebraicGeometry.Space.gysinCycleMap_integralCycle_eq_gysinIntersectionCycle`: **Stacks
  0ER1(1)(a), with both sides real objects**: at the rule below, `i^*[W] = [E ∩ W]_k`, the
  right-hand side being the cycle of Stacks 0EE9 of the scheme-theoretic intersection.  This is
  also Stacks 0ER7 for an integral `W` of δ-dimension `k + 1`.

## Implementation notes

### What is canonical and what is a parameter

The `intersectionCycle` field of `AlgebraicGeometry.Space.canonicalGysinComponentRule` is
the cycle of Stacks 0EE9, with no freedom left, and the δ-dimension bound it needs is proved.
One input is a parameter, and it is not a cycle on `E`:

* `chern`, the component datum of Stacks 0EQJ, which is the Weil divisor class of Stacks 0EQE
  taken as a parameter, `AlgebraicGeometry.Space.FirstChernComponentCycleRule`;
  clause (1)(b) of Stacks 0ER1 *is* that datum, so nothing is lost by passing it along, and the
  clause is the same datum the cap product of Stacks 0EQJ uses rather than an unrelated one.

No geometric representative is a parameter either: by Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`, the multiplicity is independent of
the choice, so `AlgebraicGeometry.Space.gysinIntersectionCycle` below feeds
`AlgebraicGeometry.Space.closedSubspaceCycle` the canonical choice
`AlgebraicGeometry.Space.canonicalGeometricPoint`, the same as every other cycle of Stacks 0EE9
in this library.

### Why the δ-dimension bound is where the mathematics is

The cycle `[Y]_k` of Stacks 0EE9 exists only for `dim_δ(Y) ≤ k`, so clause (1)(a) needs
`dim_δ(E ∩ W) ≤ k` from `dim_δ(W) = k + 1`.  This is the reason the source may take the
intersection cycle for granted, and it is proved here in two steps.

First, `W ⊄ E` has to be turned into a statement about points: an integral closed subspace is
reduced, so by Stacks 03JJ —
`AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset` — its inclusion
factors through the closed subspace `E` as soon as `|W| ⊆ |E|`; so `W ⊄ E` gives a point of `|W|`
off `E`, and since `|E|` is closed and `|W|` is the closure of its generic point, that generic
point is itself off `E`.

Second, the point set of `E ∩ W` is `|W| ∩ |E|`, which therefore misses the generic point of
`W`, and the induced dimension function of Stacks 0EDT drops strictly along a nontrivial
specialization — by `AlgebraicGeometry.Space.lt_inducedDimensionValue_of_specializes`, the same
input that `AlgebraicGeometry.Space.deltaDimensionClosed_le_coe_iff` rests on.  Reading the
bound on `E` rather than on `X` is legitimate because the closed immersion `i` is locally
quasi-finite, so it does not change the dimension function.

### Where the intersection is read

`E ∩ W` occurs on `E`, the refined Gysin map of Stacks 0ER1 taking values in cycles on `E`, and
is the inverse image `i^{-1}(W)` of Stacks 083Q — `CategoryTheory.Subfunctor.preimage` — which
is the fibre product `E ×_X W` by `CategoryTheory.Subfunctor.isPullback_preimage`.  This is the
same reading as `AlgebraicGeometry.Space.interOnVanishingLocus`, taken for an integral `W`
rather than for an arbitrary closed subspace.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### An integral closed subspace carried by a closed subspace is contained in it -/

section Containment

/-- **Stacks 03JJ for an integral closed subspace.** An integral closed subspace `W ⊆ X` whose
point set is contained in the point set of a closed subspace `E ⊆ X` is contained in `E`
scheme-theoretically.

An integral algebraic space is reduced, so by Stacks 03JJ the inclusion of `W` factors through
the closed subspace `E` as soon as it does on underlying points; a factorization of the
inclusion is exactly a containment of subfunctors. -/
theorem le_of_subspacePointSet_subset_of_integral
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hsub : subspacePointSet D.site D.base D.base_mem X W.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Y) :
    W.subspace ≤ Y := by
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset D.site D.base
    D.base_mem hX W.isClosedSubspace.1 Y hY
    W.isIntegralSpace.hasEtaleLocalProperty_isReduced W.subspace.ι).mpr hsub
  exact Subfunctor.le_of_comp_eq_ι g hg

/-- The point set of a subfunctor is monotone in the subfunctor: the inclusion of the smaller
one factors through the inclusion of the larger one. -/
public theorem subspacePointSet_mono_of_le {Y Z : Subfunctor X} (hle : Y ≤ Z) :
    subspacePointSet D.site D.base D.base_mem X Y ⊆
      subspacePointSet D.site D.base D.base_mem X Z := by
  rintro - ⟨y, rfl⟩
  rw [← Subfunctor.homOfLe_ι hle, pointsMap_comp]
  exact ⟨_, rfl⟩

/-- An integral closed subspace whose point set is the closure of a subset of `|Y|` lies in the
closed subspace `Y`. -/
private theorem le_of_closure_subset
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    {S : Set (points D.site D.base D.base_mem X)}
    (hS : S ⊆ subspacePointSet D.site D.base D.base_mem X Y)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace = closure S) :
    W.subspace ≤ Y :=
  le_of_subspacePointSet_subset_of_integral D hX Y hY W
    (hW ▸ closure_minimal hS (isClosed_subspacePointSet_of_isClosedSubspace D hX Y hY))

/-- An integral closed subspace of `X` not contained in a closed subspace `E ⊆ X` does not have
its generic point on `E`.

If it did, then `|W|`, which is the closure of that point, would be inside the closed set `|E|`,
and `AlgebraicGeometry.Space.le_of_subspacePointSet_subset_of_integral` would make `W` a
subspace of `E`. -/
theorem notMem_subspacePointSet_ambientGenericPoint_of_not_le
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWY : ¬ W.subspace ≤ Y) :
    W.ambientGenericPoint D.site D.base D.base_mem ∉
      subspacePointSet D.site D.base D.base_mem X Y := by
  intro hmem
  exact hWY (le_of_closure_subset D hX Y hY W (Set.singleton_subset_iff.2 hmem)
    (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX).symm)

end Containment

/-! ### Matching the two cases of Stacks 0ER1 across a morphism

The source's proofs of Stacks 0ER5 and Stacks 0ER6 split on whether an integral closed subspace
is contained in the divisor, and need to know that the two sides of the diagram of Remark 0ER3
split the same way.  Both halves of that are proved here, from Stacks 03JJ: the containment
`W' ⊆ E'` is a *scheme-theoretic* one, so it cannot be read off the point-set containment that
the support of a cycle gives — unless the subspace is integral, which it is. -/

section CaseMatching

variable {X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **The flat-pullback half of the case matching of Stacks 0ER6.** Let `f : X' ⟶ X` be flat of
relative dimension `r`, let `E ⊆ X` be a closed subspace, and let `W ⊆ X` be an integral closed
subspace contained in `E`.  Then every integral closed subspace of `X'` occurring in the flat
pullback `f^*[W]` is contained in the base change `E' = f^{-1}(E)`.

So case (1)(b) of Stacks 0ER1 on `X` forces case (1)(b) on `X'` at every subspace that
contributes.  A contributing subspace is carried by `|f|^{-1}|W| ⊆ |f|^{-1}|E| = |E'|`, by
`AlgebraicGeometry.Space.subspacePointSet_subset_of_flatPullbackMult_ne_zero`, and a *point-set*
containment upgrades to a containment of subspaces because the subspace is integral. -/
theorem le_preimage_of_flatPullbackMult_ne_zero (p : X ⟶ D.space) (hp : D.IsGood p)
    (p' : X' ⟶ D.space) (hp' : D.IsGood p') (f : X' ⟶ X) (hfbase : f ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hWE : W.subspace ≤ E.1)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hW' : flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' ≠ 0) :
    W'.subspace ≤ E.1.preimage f := by
  refine le_of_subspacePointSet_subset_of_integral D hp'.1 (E.1.preimage f)
    (isClosedSubspace_preimage D.site D.base D.base_mem f E.1 hp.1 hp'.1 E.2) W' ?_
  rw [subspacePointSet_preimage]
  exact (subspacePointSet_subset_of_flatPullbackMult_ne_zero D p' hp' p hp f hfbase r hflat hr
    W W' hW').trans (Set.preimage_mono (subspacePointSet_mono_of_le D hWE))

/-- **The proper-pushforward half of the case matching of Stacks 0ER5.** In the diagram of
Remark 0ER3, with `g : E' ⟶ E` commuting with `f`, an integral closed subspace `W' ⊆ X'`
contained in `E'` has the closure of its image under `f` contained in `E`.

So case (1)(b) of Stacks 0ER1 on `X'` forces case (1)(b) on `X` at the subspace the pushforward
of `[W']` is carried by.  The image of `|W'|` lies in the closed set `|E|` because the square
commutes on points, hence so does its closure, which is the point set of the image closure; a
point-set containment upgrades to a containment of subspaces because the image closure is
integral. -/
theorem closureImage_le_of_le (p : X ⟶ D.space) (hp : D.IsGood p) (f : X' ⟶ X)
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (E' : ClosedSubspaces D.site D.base D.base_mem X')
    (g : E'.1.toFunctor ⟶ E.1.toFunctor) (hw : g ≫ E.1.ι = E'.1.ι ≫ f)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X') (hW'E' : W'.subspace ≤ E'.1) :
    (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f W').subspace ≤ E.1 := by
  refine le_of_closure_subset D hp.1 E.1 E.2 _ ?_
    (IntegralClosedSubspace.subspacePointSet_closureImage ..)
  rintro - ⟨x, hx, rfl⟩
  obtain ⟨t, rfl⟩ := subspacePointSet_mono_of_le D hW'E' hx
  rw [pointsMap_apply_comm D.site D.base D.base_mem hw.symm t]
  exact ⟨_, rfl⟩

end CaseMatching

/-! ### The dimension function off the generic point of an integral closed subspace -/

section Drop

variable (p : X ⟶ D.space) (hp : D.IsGood p)

include hp

/-- The induced dimension function of a good algebraic space over the base is strictly smaller
at a point of the point set of an integral closed subspace `W` than at the generic point of `W`,
unless the point is that generic point.

The generic point specializes to every point of `|W|`, and the induced dimension function drops
strictly along a nontrivial specialization. -/
theorem inducedDimensionValue_lt_of_mem_of_ne
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    {x : points D.site D.base D.base_mem X}
    (hx : x ∈ subspacePointSet D.site D.base D.base_mem X W.subspace)
    (hne : x ≠ W.ambientGenericPoint D.site D.base D.base_mem) :
    inducedDimensionValue D.site D.base D.base_mem D.delta p x <
      inducedDimensionValue D.site D.base D.base_mem D.delta p
        (W.ambientGenericPoint D.site D.base D.base_mem) := by
  have hanti : ∀ ⦃a b : points D.site D.base D.base_mem X⦄, a ⤳ b → a ≠ b →
      inducedDimensionValue D.site D.base D.base_mem D.delta p b <
        inducedDimensionValue D.site D.base D.base_mem D.delta p a :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hp.1
      (isDecentSpace_of_isGood D p hp) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta p hp.2.2
  exact hanti ((W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hp.1).specializes
    hx) (Ne.symm hne)

/-- An integral closed subspace of δ-dimension `k + 1` has induced dimension function at most
`k` at every point of its point set other than its generic point. -/
theorem inducedDimensionValue_le_of_mem_of_ne (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1)
    {x : points D.site D.base D.base_mem X}
    (hx : x ∈ subspacePointSet D.site D.base D.base_mem X W.subspace)
    (hne : x ≠ W.ambientGenericPoint D.site D.base D.base_mem) :
    inducedDimensionValue D.site D.base D.base_mem D.delta p x ≤ k := by
  have hgenval : inducedDimensionValue D.site D.base D.base_mem D.delta p
      (W.ambientGenericPoint D.site D.base D.base_mem) = k + 1 := hW
  have hlt := inducedDimensionValue_lt_of_mem_of_ne D p hp W hx hne
  omega

end Drop

/-! ### The scheme-theoretic intersection with an integral closed subspace -/

section Intersection

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))

/-- The scheme-theoretic intersection `E ∩ W = i^{-1}(W)` of the closed subspace `E ⊆ X` with an
integral closed subspace `W ⊆ X`, read as a closed subspace of `E`: the inverse image of `W`
along the closed immersion `i : E → X`, which is the fibre product `E ×_X W` by Stacks 083Q.

This is the object whose `k`-cycle is clause (1)(a) of Stacks 0ER1, and it is
`AlgebraicGeometry.Space.interOnVanishingLocus` for an integral `W`. -/
abbrev gysinIntersectionSubspace (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    ClosedSubspaces D.site D.base D.base_mem E.1.toFunctor :=
  ⟨W.subspace.preimage E.1.ι,
    isClosedSubspace_preimage D.site D.base D.base_mem E.1.ι W.subspace hp.1 hE.1
      W.isClosedSubspace⟩

/-- The point set of `E ∩ W` inside `|E|` is the inverse image of `|W|` along `|i|`. -/
theorem subspacePointSet_gysinIntersectionSubspace
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    subspacePointSet D.site D.base D.base_mem E.1.toFunctor
        (gysinIntersectionSubspace D p hp E hE W).1 =
      pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace :=
  subspacePointSet_preimage D.site D.base D.base_mem E.1.ι W.subspace

include hp hE in
/-- **The δ-dimension bound that makes clause (1)(a) of Stacks 0ER1 legitimate.** If an integral
closed subspace `W ⊆ X` has δ-dimension `k + 1` and its generic point does not lie on `E`, then
the scheme-theoretic intersection `E ∩ W` has δ-dimension at most `k`, so the cycle
`[E ∩ W]_k` of Stacks 0EE9 exists.

Every point of `|E ∩ W|` maps into `|W|` and lands on `E`, so it is not the generic point of
`W`; the induced dimension function of `X` is therefore at most `k` at its image, by
`AlgebraicGeometry.Space.inducedDimensionValue_le_of_mem_of_ne`, and the closed immersion
`i : E → X` is locally quasi-finite, so the induced dimension function of `E` at the point
itself is the same number.  The δ-dimension of a closed set is at most `k` as soon as the
induced dimension function is, by
`AlgebraicGeometry.Space.deltaDimensionClosed_le_coe_iff`. -/
theorem deltaDimensionSubspace_gysinIntersectionSubspace_le (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1)
    (hgen : W.ambientGenericPoint D.site D.base D.base_mem ∉
      subspacePointSet D.site D.base D.base_mem X E.1) :
    deltaDimensionSubspace D (E.1.ι ≫ p) hE (gysinIntersectionSubspace D p hp E hE W).1
        (gysinIntersectionSubspace D p hp E hE W).2 ≤ (k : EInt) := by
  have hlqf : IsLocallyQuasiFinite D.site D.base D.base_mem E.1.ι :=
    isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem E.1.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem E.2.2)
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed]
  refine (deltaDimensionClosed_le_coe_iff D (E.1.ι ≫ p) hE _ _ k).2 fun t ht => ?_
  rw [subspacePointSet_gysinIntersectionSubspace D p hp E hE W] at ht
  have hcomp : inducedDimensionValue D.site D.base D.base_mem D.delta (E.1.ι ≫ p) t =
      inducedDimensionValue D.site D.base D.base_mem D.delta p
        (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι t) :=
    D.deltaValue_comp_of_isLocallyQuasiFinite hE.1 hp.1 E.1.ι p hlqf hp.2.2 t
  have hne : pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι t ≠
      W.ambientGenericPoint D.site D.base D.base_mem := fun h => hgen (h ▸ ⟨t, rfl⟩)
  rw [hcomp]
  exact inducedDimensionValue_le_of_mem_of_ne D p hp k W hW ht hne

include hp hE in
/-- **The δ-dimension bound of clause (1)(a) of Stacks 0ER1, unconditionally.** An integral
closed subspace `W ⊆ X` of δ-dimension `k + 1` which is not contained in `E` has
`dim_δ(E ∩ W) ≤ k`.

The containment hypothesis of clause (1)(a) is exactly what the bound needs: by Stacks 03JJ it
puts the generic point of `W` off `E`, through
`AlgebraicGeometry.Space.notMem_subspacePointSet_ambientGenericPoint_of_not_le`. -/
theorem deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    deltaDimensionSubspace D (E.1.ι ≫ p) hE (gysinIntersectionSubspace D p hp E hE W).1
        (gysinIntersectionSubspace D p hp E hE W).2 ≤ (k : EInt) :=
  deltaDimensionSubspace_gysinIntersectionSubspace_le D p hp E hE k W hW
    (notMem_subspacePointSet_ambientGenericPoint_of_not_le D hp.1 E.1 E.2 W hWE)

end Intersection

/-! ### The cycle of the intersection, and the component rule -/

section Rule

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)

/-- **Clause (1)(a) of Stacks 0ER1.** The `k`-cycle `[E ∩ W]_k` on `E` of Stacks 0EE9 attached to
the scheme-theoretic intersection of `E` with an integral closed subspace `W ⊆ X` of
δ-dimension `k + 1` not contained in `E`.

The δ-dimension bound that Stacks 0EE9 needs is
`AlgebraicGeometry.Space.deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le`, and the
multiplicities are read, as everywhere `AlgebraicGeometry.Space.closedSubspaceCycle` is used, at
the canonical geometric representative of each point. -/
def gysinIntersectionCycle (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    CycleGroup D (E.1.ι ≫ p) k :=
  closedSubspaceCycle D (E.1.ι ≫ p) hE (gysinIntersectionSubspace D p hp E hE W).1
    (gysinIntersectionSubspace D p hp E hE W).2 k
    (deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le D p hp E hE k W hW hWE)

/-- The coefficient family of `[E ∩ W]_k` is the one of Stacks 0EE9 for the intersection. -/
@[simp]
theorem gysinIntersectionCycle_coe (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    (gysinIntersectionCycle D p hp E hE k W hW hWE).1 =
      cycleCoeffOfClosedSubspace D (E.1.ι ≫ p) hE
        (gysinIntersectionSubspace D p hp E hE W).1
        (gysinIntersectionSubspace D p hp E hE W).2 k
        (canonicalGeometricPoint D.site D.base D.base_mem
          (gysinIntersectionSubspace D p hp E hE W).1.toFunctor) :=
  rfl

/-- **The support property of clause (1)(a), proved rather than assumed.** An integral closed
subspace of `E` with a nonzero coefficient in `[E ∩ W]_k` is carried by `i^{-1}(W)`.

This is the field `AlgebraicGeometry.Space.GysinComponentRule.intersectionCycle_support`, and it
is what makes the additive extension of the component rule a cycle.  A subspace occurring in the
cycle of a closed subspace is contained in that subspace, by
`AlgebraicGeometry.Space.subspacePointSet_subset_of_closedSubspaceCycle_ne_zero`, and the point
set of `E ∩ W` is `|i|^{-1}|W|`. -/
theorem subspacePointSet_subset_of_gysinIntersectionCycle_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (hZ : (gysinIntersectionCycle D p hp E hE k W hW hWE).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem E.1.toFunctor Z.subspace ⊆
      pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace := by
  have h := subspacePointSet_subset_of_closedSubspaceCycle_ne_zero D (E.1.ι ≫ p) hE
    (gysinIntersectionSubspace D p hp E hE W).1 (gysinIntersectionSubspace D p hp E hE W).2 k
    (deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le D p hp E hE k W hW hWE) Z hZ
  rwa [subspacePointSet_gysinIntersectionSubspace D p hp E hE W] at h

/-- **The component rule of Stacks 0ER1, with no free cycle left.** Clause (1)(a) is the cycle
`[E ∩ W]_k` of Stacks 0EE9 of the scheme-theoretic intersection, and clause (1)(b) is the
component datum of Stacks 0EQJ, that is the Weil divisor class `c₁(ℒ|_W) ∩ [W]` of Stacks 0EQE
which `AlgebraicGeometry.Space.FirstChernComponentCycleRule` carries.

Both fields are determined by `(X, E)` alone and by the component datum of Stacks 0EQJ; see
this module's implementation notes. -/
def canonicalGysinComponentRule (chern : FirstChernComponentCycleRule D p k) :
    GysinComponentRule D p E k where
  intersectionCycle W hW hWE := gysinIntersectionCycle D p hp E hE k W hW hWE
  intersectionCycle_support W hW hWE Z hZ :=
    subspacePointSet_subset_of_gysinIntersectionCycle_ne_zero D p hp E hE k W hW hWE Z hZ
  chernCycle W hW _ := chern W hW

/-- The intersection-cycle field of `canonicalGysinComponentRule` is `gysinIntersectionCycle`. -/
@[simp]
theorem canonicalGysinComponentRule_intersectionCycle
    (chern : FirstChernComponentCycleRule D p k)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    (canonicalGysinComponentRule D p hp E hE k chern).intersectionCycle W hW hWE =
      gysinIntersectionCycle D p hp E hE k W hW hWE :=
  rfl

/-- The Chern-cycle field of `canonicalGysinComponentRule` is the component datum `chern`. -/
@[simp]
theorem canonicalGysinComponentRule_chernCycle (chern : FirstChernComponentCycleRule D p k)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ E.1) :
    (canonicalGysinComponentRule D p hp E hE k chern).chernCycle W hW hWE = chern W hW :=
  rfl

/-- **Stacks 0ER1(1)(a), and Stacks 0ER7 for an integral closed subspace of δ-dimension
`k + 1`.** At the component rule of
`AlgebraicGeometry.Space.canonicalGysinComponentRule` the refined Gysin map of Stacks 0ER1 sends
the cycle `[W]` of an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` not contained in
`E` to the cycle `[E ∩ W]_k` of Stacks 0EE9 of the scheme-theoretic intersection.

This is `AlgebraicGeometry.Space.gysinCycleMap_integralCycle_of_not_le` with the free parameter
on the right-hand side replaced by the cycle of Stacks 0EE9 that the source means. -/
theorem gysinCycleMap_integralCycle_eq_gysinIntersectionCycle
    (chern : FirstChernComponentCycleRule D p k)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    gysinCycleMap D p E hE k (canonicalGysinComponentRule D p hp E hE k chern)
        (integralCycle D p (k + 1) W hW) =
      gysinIntersectionCycle D p hp E hE k W hW hWE := by
  rw [gysinCycleMap_integralCycle_of_not_le D p E hE k
    (canonicalGysinComponentRule D p hp E hE k chern) hW hWE,
    canonicalGysinComponentRule_intersectionCycle]

end Rule

end AlgebraicGeometry.Space

end
