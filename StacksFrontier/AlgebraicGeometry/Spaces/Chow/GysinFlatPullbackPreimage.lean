module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCoherentCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase

/-!
# The non-contained branch of Stacks 0ER6

In Situation 0EDT let `X/B` and `X'/B` be good, let `f : X' ⟶ X` be flat of relative dimension
`r`, let `E ⊆ X` be a closed subspace with closed immersion `i : E → X`, and form the diagram of
Remark 0ER3

```
E' --i'--> X'
|          |
g          f
|          |
v          v
E  --i-->  X
```

with `E' = f^{-1}(E)` and `g : E' ⟶ E`.  **Stacks 0ER6** is the identity
`(i')^* f^* α = g^* i^* α` of `(k+r)`-cycles on `E'`, which
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility` proves from one carried
coefficient identity at a prime cycle, the single field
`AlgebraicGeometry.Space.GysinFlatPullbackComparison.gysinCoeff_comm`.

The source's proof splits on whether the integral closed subspace `W ⊆ X` is contained in `E`,
and its whole argument in the **non-contained** case is two sentences: the equality of closed
subspaces `W' ∩ D' = g^{-1}(W ∩ D)`, and Lemma 0EPB.  **Both are proved here.**

## Main results

* `AlgebraicGeometry.Space.preimage_preimage_of_comm`: the source's `W' ∩ D' = g^{-1}(W ∩ D)`,
  for any commuting square — the two readings of the intersection of `W` with the corner of the
  square agree.
* `AlgebraicGeometry.Space.closureImage_eq_of_flatPullbackMult_ne_zero`: an integral closed
  subspace occurring in `f^*[W]` dominates `W`.
* `AlgebraicGeometry.Space.not_le_preimage_of_flatPullbackMult_ne_zero`: **the other half of the
  flat-pullback case matching of Stacks 0ER6.**  If `W ⊄ E` then no integral closed subspace
  occurring in `f^*[W]` is contained in `E'`, so the non-contained branch of Stacks 0ER1 on `X`
  forces the non-contained branch on `X'`.  This is the converse direction of
  `AlgebraicGeometry.Space.le_preimage_of_flatPullbackMult_ne_zero`.
* `AlgebraicGeometry.Space.flatPullback_gysinIntersectionCycle_apply`: **the `g`-side of the
  non-contained branch, computed.**  The coefficient at `T' ⊆ E'` of `g^*[E ∩ W]_k` is the
  multiplicity of `T'` in `E' ∩ f^{-1}(W)`.
* `AlgebraicGeometry.Space.gysinCoeff_comm_of_intersectionAdditivity_of_not_le`: **the
  non-contained branch of `AlgebraicGeometry.Space.GysinFlatPullbackComparison.gysinCoeff_comm`**,
  at the canonical component rules, discharged.
* `AlgebraicGeometry.Space.gysinFlatPullbackComparison_of_intersectionAdditivity`: an inhabitant
  of `AlgebraicGeometry.Space.GysinFlatPullbackComparison` from the intersection additivity on
  `X'` together with the contained branch as a hypothesis.
* `AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity`:
  **Stacks 0ER6** as a plain equality of `(k+r)`-cycles on `E'`, from the intersection additivity
  on `X'` and the contained branch.
* `AlgebraicGeometry.Space.isFlat_gysinBaseChange` and
  `AlgebraicGeometry.Space.hasRelativeDimension_gysinBaseChange`: `g` is flat of relative
  dimension `r`, **proved** from the cartesian square rather than assumed.
* `gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity_of_isPullback`:
  **Stacks 0ER6** with nothing about `g` assumed at all — neither that it is a morphism over `B`,
  nor its flatness, nor its relative dimension.

## Implementation notes

### Which branch is closed, and which is not

* `W ⊄ E`: the source writes `W' ∩ D' = g^{-1}(W ∩ D)` and appeals to Lemma 0EPB.  Here
  `AlgebraicGeometry.Space.preimage_preimage_of_comm` is the first sentence and
  `AlgebraicGeometry.Space.flatPullback_closedSubspaceCycle_preimage` — part (1) of Stacks 0EPB —
  is the second, and together they compute the `g`-side coefficient as the multiplicity of `T'`
  in `E' ∩ f^{-1}(W)`.  What it leaves is a
  statement about `X'` alone, with no reference to `E`, to `g` or to the square: the
  multiplicity of `T'` in `E' ∩ f^{-1}(W)` is the sum, over the integral closed subspaces `W'`
  of `X'` occurring in `f^*[W]`, of their multiplicities times the multiplicity of `T'` in
  `E' ∩ W'`.  That is the additivity of the cycles of Stacks 0EE9 under intersection with `E'`,
  the shape of Stacks 0EQL, and it is the hypothesis `hadd` below.  It is the same additivity
  that `AlgebraicGeometry.Space.gysinCycleMap_eq_of_cycleCoeffOfClosedSubspace` — Stacks 0ER7 in
  this library — carries, applied to the closed subspace `f^{-1}(W)`; the source of Stacks 0ER6
  uses it silently in applying the Gysin map, which Definition 0ER1 gives on prime cycles, to
  the cycle `f^*[W] = [f^{-1}(W)]_{k+1+r}` of a closed subspace that need not be integral.
* `W ⊆ E`: the source appeals to Stacks 0EQR, which compares the pullback of `c₁(ℒ|_W) ∩ [W]`
  with `c₁(ℒ'|_{f^{-1}(W)}) ∩ [f^{-1}(W)]`.  Clause (1)(b) of Stacks 0ER1 is the free parameter
  `AlgebraicGeometry.Space.GysinComponentRule.chernCycle`, which
  `AlgebraicGeometry.Space.canonicalGysinComponentRule` passes along unchanged as the component
  datum of Stacks 0EQJ; `chern` on `X` and `chern'` on `X'` are therefore unrelated data and
  **this branch stays a hypothesis**, `hchern` below.  The scheme-theoretic half of its case
  matching is proved: `AlgebraicGeometry.Space.le_preimage_of_flatPullbackMult_ne_zero`.

### Why the case matching needs the dominance

The non-contained branch of Definition 0ER1 is selected on `X'` by `W' ⊄ E'`, and what the
source's case hypothesis gives is `W ⊄ E`.  Passing from one to the other is
`AlgebraicGeometry.Space.not_le_preimage_of_flatPullbackMult_ne_zero`, whose proof is the
dominance `AlgebraicGeometry.Space.closureImage_eq_of_flatPullbackMult_ne_zero`: a subspace `W'`
occurring in `f^*[W]` has δ-dimension `dim_δ(W) + r`, so the closure `V` of its image cannot be
a proper closed subspace of `W` — the inverse image of such a `V` has δ-dimension at most
`dim_δ(V) + r < dim_δ(W) + r` by part (1) of Stacks 0EPB.  Hence `V = W`, and a point-set
containment `|W'| ⊆ |f|^{-1}|E|` pushes down to `|W| ⊆ |E|`, which upgrades to `W ⊆ E` by
Stacks 03JJ because `W` is integral.

### Flatness and the relative dimension of `g` are not assumptions

The source gets both from `f` by base change along `i`.  Flatness is stable under base change, by
`AlgebraicGeometry.Space.isFlat_of_isPullback_of_isAlgebraicSpace`; and the invariance of the
relative dimension under base change is part (1) of Stacks 04NS,
`AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback`.  The latter asks in addition
that `f` be locally of finite type, which is not an extra assumption: Definition 06LR speaks of
the relative dimension only of a morphism locally of finite type, so it is part of the source's
own hypothesis on `f`.

## References

* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u₃ u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The two readings of the intersection with the corner of a commuting square -/

/-- **The source's `W' ∩ D' = g^{-1}(W ∩ D)`.** In a commuting square

```
A' --i'--> X'
|          |
g          f
|          |
v          v
A  --i-->  X
```

the inverse image along `g` of the intersection `i^{-1}(W)` of a subfunctor `W ⊆ X` with `A`
agrees with the intersection along `i'` of the inverse image `f^{-1}(W)` with `A'`.

Both are the inverse image of `W` along the diagonal of the square, so nothing is used but the
commutativity: in particular the square need not be cartesian. -/
theorem preimage_preimage_of_comm {C : Type u₁} [Category.{u₂} C] {X X' A A' : C ⥤ Type u₃}
    {f : X' ⟶ X} {i : A ⟶ X} {i' : A' ⟶ X'} {g : A' ⟶ A} (hw : g ≫ i = i' ≫ f)
    (W : Subfunctor X) :
    (W.preimage i).preimage g = (W.preimage f).preimage i' := by
  rw [← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp, hw]

/-! ### An integral closed subspace occurring in a flat pullback dominates -/

section Dominance

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : X' ⟶ X) (hfbase : f ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- If the points of `W'` map into a closed set `S`, so do those of the closure of its image. -/
private theorem subspacePointSet_closureImage_subset
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    {S : Set (points D.site D.base D.base_mem X)} (hS : IsClosed S)
    (h : subspacePointSet D.site D.base D.base_mem X' W'.subspace ⊆
      pointsMap D.site D.base D.base_mem X' f ⁻¹' S) :
    subspacePointSet D.site D.base D.base_mem X
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f W').subspace ⊆ S := by
  rw [IntegralClosedSubspace.subspacePointSet_closureImage]
  refine closure_minimal ?_ hS
  rintro - ⟨x, hx, rfl⟩
  exact h hx

include hp hp' hfbase hflat hr

/-- **An integral closed subspace occurring in `f^*[W]` dominates `W`.** For `f` flat of relative
dimension `r` and `W ⊆ X` an integral closed subspace, an integral closed subspace `W' ⊆ X'` with
a nonzero multiplicity in `f^*[W]` has the closure of its image under `f` equal to `W`.

The closure `V` of the image is contained in `W`, because `|W'|` lies in `|f|^{-1}|W|` by Stacks
0EP6 and `|W|` is closed; so `dim_δ(V) ≤ dim_δ(W)`.  Conversely `W' ⊆ f^{-1}(V)`, whose
δ-dimension is at most `dim_δ(V) + r` by part (1) of Stacks 0EPB, while `dim_δ(W')` is
`dim_δ(W) + r`; so `dim_δ(W) ≤ dim_δ(V)`.  An integral closed subspace whose generic point lies
on `W` and whose δ-dimension is that of `W` is `W`. -/
theorem closureImage_eq_of_flatPullbackMult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hW' : flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' ≠ 0) :
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f W' = W := by
  set V := IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
    (D.isDecentSpace_of_isGood p hp) f W' with hV
  have hptW' : subspacePointSet D.site D.base D.base_mem X' W'.subspace ⊆
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace :=
    subspacePointSet_subset_of_flatPullbackMult_ne_zero D p' hp' p hp f hfbase r hflat hr W W' hW'
  have hVW : subspacePointSet D.site D.base D.base_mem X V.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace := by
    exact subspacePointSet_closureImage_subset D p hp f W'
      (isClosed_subspacePointSet_of_isClosedSubspace D hp.1 W.subspace W.isClosedSubspace) hptW'
  have hle₁ : deltaDimension D p V ≤ deltaDimension D p W := by
    have h := deltaDimensionClosed_le_of_subset_subspacePointSet D p hp W.subspace
      W.isClosedSubspace (subspacePointSet D.site D.base D.base_mem X V.subspace)
      (isClosed_subspacePointSet_of_isClosedSubspace D hp.1 V.subspace V.isClosedSubspace)
      (deltaDimension D p W)
      (deltaDimensionSubspace_integralClosedSubspace D p hp W).le hVW
    rw [← deltaDimensionSubspace_eq_deltaDimensionClosed D p hp V.subspace V.isClosedSubspace,
      deltaDimensionSubspace_integralClosedSubspace D p hp V] at h
    exact WithBotTop.coe_le_coe.1 h
  have hVc := isClosedSubspace_preimage D.site D.base D.base_mem f V.subspace hp.1 hp'.1
    V.isClosedSubspace
  have hW'V : W'.subspace ≤ V.subspace.preimage f := by
    refine le_of_subspacePointSet_subset_of_integral D hp'.1 (V.subspace.preimage f) hVc W' ?_
    rw [subspacePointSet_preimage, hV, IntegralClosedSubspace.subspacePointSet_closureImage]
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  have hle₂ : deltaDimension D p W ≤ deltaDimension D p V := by
    have hdimW' : deltaDimension D p' W' = deltaDimension D p W + (r : ℤ) :=
      deltaDimension_eq_of_flatPullbackMult_ne_zero D p' hp' p hp f hfbase r hflat hr W W' hW'
    have h := deltaDimensionClosed_le_of_subset_subspacePointSet D p' hp'
      (V.subspace.preimage f) hVc
      (subspacePointSet D.site D.base D.base_mem X' W'.subspace)
      (isClosed_subspacePointSet_of_isClosedSubspace D hp'.1 W'.subspace W'.isClosedSubspace)
      (deltaDimension D p V + (r : ℤ))
      (deltaDimensionSubspace_preimage_integralClosedSubspace_le D p' hp' p hp f hfbase r hflat
        hr V)
      (subspacePointSet_mono_of_le D hW'V)
    rw [← deltaDimensionSubspace_eq_deltaDimensionClosed D p' hp' W'.subspace
        W'.isClosedSubspace,
      deltaDimensionSubspace_integralClosedSubspace D p' hp' W', hdimW'] at h
    have h' : deltaDimension D p W + (r : ℤ) ≤ deltaDimension D p V + (r : ℤ) :=
      WithBotTop.coe_le_coe.1 h
    omega
  exact eq_of_mem_of_deltaDimension_eq D p hp W V (hVW ⟨_, rfl⟩) (le_antisymm hle₁ hle₂)

/-- **The other half of the flat-pullback case matching of Stacks 0ER6.** Let `E ⊆ X` be a closed
subspace and let `W ⊆ X` be an integral closed subspace *not* contained in `E`.  Then no integral
closed subspace of `X'` occurring in `f^*[W]` is contained in the base change `E' = f^{-1}(E)`.

So case (1)(a) of Stacks 0ER1 on `X` forces case (1)(a) on `X'` at every subspace that
contributes; `AlgebraicGeometry.Space.le_preimage_of_flatPullbackMult_ne_zero` is the contained
branch of the same matching.  The argument is the contrapositive: a contributing `W'` dominates
`W`, so if `|W'| ⊆ |f|^{-1}|E|` then `|W| = closure(|f|(|W'|)) ⊆ |E|`, and a point-set
containment upgrades to a containment of subspaces because `W` is integral — Stacks 03JJ,
through `AlgebraicGeometry.Space.le_of_subspacePointSet_subset_of_integral`. -/
theorem not_le_preimage_of_flatPullbackMult_ne_zero
    (E : ClosedSubspaces D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hWE : ¬ W.subspace ≤ E.1)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hW' : flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' ≠ 0) :
    ¬ W'.subspace ≤ E.1.preimage f := by
  intro hle
  refine hWE (le_of_subspacePointSet_subset_of_integral D hp.1 E.1 E.2 W ?_)
  have hdom := closureImage_eq_of_flatPullbackMult_ne_zero D p hp p' hp' f hfbase r hflat hr
    W W' hW'
  have hpt : subspacePointSet D.site D.base D.base_mem X' W'.subspace ⊆
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1 := by
    rw [← subspacePointSet_preimage D.site D.base D.base_mem f E.1]
    exact subspacePointSet_mono_of_le D hle
  rw [← hdom]
  exact subspacePointSet_closureImage_subset D p hp f W'
    (isClosed_subspacePointSet_of_isClosedSubspace D hp.1 E.1 E.2) hpt

end Dominance

/-! ### The `g`-side of the non-contained branch -/

section NonContained

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : X' ⟶ X) (hfbase : f ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    (g : E'.1.toFunctor ⟶ E.1.toFunctor) (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (k : ℤ)

/-- The scheme-theoretic intersection `E' ∩ f^{-1}(W)` of the corner `E'` of the diagram of
Remark 0ER3 with the inverse image of an integral closed subspace `W ⊆ X`, read as a closed
subspace of `E'`.

By `AlgebraicGeometry.Space.preimage_preimage_of_comm` this is also `g^{-1}(E ∩ W)`, which is the
source's identification `W' ∩ D' = g^{-1}(W ∩ D)`. -/
abbrev gysinPreimageIntersectionSubspace
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    ClosedSubspaces D.site D.base D.base_mem E'.1.toFunctor :=
  ⟨(W.subspace.preimage f).preimage E'.1.ι,
    isClosedSubspace_preimage D.site D.base D.base_mem E'.1.ι (W.subspace.preimage f) hp'.1 hE'.1
      (isClosedSubspace_preimage D.site D.base D.base_mem f W.subspace hp.1 hp'.1
        W.isClosedSubspace)⟩

/-- The coefficient family of the cycle of a closed subspace depends on the subspace alone: the
closedness and the δ-dimension bound are propositions. -/
private theorem cycleCoeffOfClosedSubspace_congr
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (n : ℤ) {Z Z' : Subfunctor Y}
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z)
    (hZ' : IsClosedSubspace D.site D.base D.base_mem Z') (h : Z = Z')
    (T : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    cycleCoeffOfClosedSubspace D sY hY Z hZ n
        (canonicalGeometricPoint D.site D.base D.base_mem Z.toFunctor) T =
      cycleCoeffOfClosedSubspace D sY hY Z' hZ' n
        (canonicalGeometricPoint D.site D.base D.base_mem Z'.toFunctor) T := by
  subst h
  rfl

include hp hp' hfbase hflat hr hE hE' hgbase hgflat hgr

/-- **The `g`-side of the non-contained branch of Stacks 0ER6, computed.** The coefficient at an
integral closed subspace `T' ⊆ E'` of the flat pullback `g^*[E ∩ W]_k` of clause (1)(a) of
Stacks 0ER1 is the multiplicity of `T'` in `E' ∩ f^{-1}(W)`.

This is the source's whole argument in the case `W ⊄ D`: the identification
`W' ∩ D' = g^{-1}(W ∩ D)`, which is
`AlgebraicGeometry.Space.preimage_preimage_of_comm` applied to the commuting square, followed by
part (1) of Stacks 0EPB, which is
`AlgebraicGeometry.Space.flatPullback_closedSubspaceCycle_preimage`. -/
theorem flatPullback_gysinIntersectionCycle_apply
    (hw : g ≫ E.1.ι = E'.1.ι ≫ f)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    (flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
          (k + (r : ℤ)) rfl (gysinIntersectionCycle D p hp E hE k W hW hWE)).1 T' =
      cycleCoeffOfClosedSubspace D (E'.1.ι ≫ p') hE'
        (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1
        (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).2 (k + (r : ℤ))
        (canonicalGeometricPoint D.site D.base D.base_mem
          (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1.toFunctor) T' := by
  obtain ⟨hdim, heq⟩ := flatPullback_closedSubspaceCycle_preimage D (E'.1.ι ≫ p') hE'
    (E.1.ι ≫ p) hE g hgbase r hgflat hgr k (gysinIntersectionSubspace D p hp E hE W).1
    (gysinIntersectionSubspace D p hp E hE W).2
    (deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le D p hp E hE k W hW hWE)
  rw [show gysinIntersectionCycle D p hp E hE k W hW hWE =
      closedSubspaceCycle D (E.1.ι ≫ p) hE (gysinIntersectionSubspace D p hp E hE W).1
        (gysinIntersectionSubspace D p hp E hE W).2 k
        (deltaDimensionSubspace_gysinIntersectionSubspace_le_of_not_le D p hp E hE k W hW hWE)
      from rfl, ← heq, closedSubspaceCycle_coe]
  exact cycleCoeffOfClosedSubspace_congr D (E'.1.ι ≫ p') hE' (k + (r : ℤ)) _ _
    (preimage_preimage_of_comm hw W.subspace) T'

/-- **The non-contained branch of
`AlgebraicGeometry.Space.GysinFlatPullbackComparison.gysinCoeff_comm`, discharged**, at the
canonical component rules of `AlgebraicGeometry.Space.canonicalGysinComponentRule`.

What is carried is `hadd`, a statement about `X'` alone: the multiplicity of `T' ⊆ E'` in
`E' ∩ f^{-1}(W)` is the sum, over the integral closed subspaces `W' ⊆ X'`, of their
multiplicities in `f^*[W]` times the component cycle of Stacks 0ER1 at `W'`.  That is the
additivity of the cycles of Stacks 0EE9 under intersection with `E'`, the shape of Stacks 0EQL,
which `AlgebraicGeometry.Space.gysinCycleMap_eq_of_cycleCoeffOfClosedSubspace` — Stacks 0ER7 in
this library — carries for a general closed subspace; here it is needed only at `f^{-1}(W)`.
Nothing in `hadd` mentions `E`, `g` or the square.

The case matching is proved, not assumed: an integral closed subspace of `X'` occurring in
`f^*[W]` is not contained in `E'`, by
`AlgebraicGeometry.Space.not_le_preimage_of_flatPullbackMult_ne_zero`, so clause (1)(a) of
Stacks 0ER1 is the operative one on `X'` as well — which is why `hadd` may be stated with the
component cycle on the right. -/
theorem gysinCoeff_comm_of_intersectionAdditivity_of_not_le
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' (k + (r : ℤ)))
    (hw : g ≫ E.1.ι = E'.1.ι ≫ f)
    (hadd : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → ¬ W.subspace ≤ E.1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        cycleCoeffOfClosedSubspace D (E'.1.ι ≫ p') hE'
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).2 (k + (r : ℤ))
            (canonicalGeometricPoint D.site D.base D.base_mem
              (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1.toFunctor) T' =
          ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
              (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T')
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    (∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
          (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
            (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T') =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
        (gysinComponentCycle D p E hE k
            (canonicalGysinComponentRule D p hp E hE k chern) W).1 T *
          flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T' := by
  rw [← hadd W hW hWE T', ← flatPullback_gysinIntersectionCycle_apply D p hp p' hp' f hfbase r
      hflat hr E hE E' hE' g hgbase hgflat hgr k hw W hW hWE T',
    flatPullbackMap_apply]
  refine finsum_congr fun T => ?_
  rw [gysinComponentCycle_of_not_le D p E hE k (canonicalGysinComponentRule D p hp E hE k chern)
    hW hWE, canonicalGysinComponentRule_intersectionCycle]

/-- **An inhabitant of `AlgebraicGeometry.Space.GysinFlatPullbackComparison` with the
non-contained branch discharged.**  At the canonical component rules of
`AlgebraicGeometry.Space.canonicalGysinComponentRule` the comparison datum of Stacks 0ER6 follows
from the intersection additivity `hadd` on `X'` — the shape of Stacks 0EQL at `f^{-1}(W)` — and
the contained branch `hchern`, which is Stacks 0EQR read coefficientwise at clause (1)(b) of
Stacks 0ER1. -/
def gysinFlatPullbackComparison_of_intersectionAdditivity
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' (k + (r : ℤ)))
    (hw : g ≫ E.1.ι = E'.1.ι ≫ f)
    (hadd : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → ¬ W.subspace ≤ E.1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        cycleCoeffOfClosedSubspace D (E'.1.ι ≫ p') hE'
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).2 (k + (r : ℤ))
            (canonicalGeometricPoint D.site D.base D.base_mem
              (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1.toFunctor) T' =
          ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
              (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T')
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → W.subspace ≤ E.1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        (∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
              (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T') =
          ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
            (gysinComponentCycle D p E hE k
                (canonicalGysinComponentRule D p hp E hE k chern) W).1 T *
              flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T') :
    GysinFlatPullbackComparison D p hp p' hp' f hfbase r hflat hr E hE E' hE' g hgbase hgflat
      hgr k (canonicalGysinComponentRule D p hp E hE k chern)
      (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') where
  gysinCoeff_comm W hW T' := by
    by_cases hWE : W.subspace ≤ E.1
    · exact hchern W hW hWE T'
    · exact gysinCoeff_comm_of_intersectionAdditivity_of_not_le D p hp p' hp' f hfbase r hflat hr
        E hE E' hE' g hgbase hgflat hgr k chern chern' hw hadd W hW hWE T'

/-- **Stacks 0ER6, from the intersection additivity and the contained branch.** In
Situation 0EDT let `f : X' ⟶ X` be a flat morphism of relative dimension `r` of good algebraic
spaces over `B`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1, and form the diagram of
Remark 0ER3, with `E' = E ×_X X'`, `g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every
`(k+1)`-cycle `α` on `X`

  `(i')^* f^* α = g^* i^* α`,

an identity of `(k+r)`-cycles on `E'`, hence of classes in `CH_{k+r}(E')`.

The component rules on both sides are the canonical ones of
`AlgebraicGeometry.Space.canonicalGysinComponentRule`, so clause (1)(a) of Stacks 0ER1 is the
cycle `[E ∩ W]_k` of Stacks 0EE9 that the source means and only clause (1)(b) is free.

**Two inputs are carried.**  `hadd` is the intersection additivity on `X'`, the shape of
Stacks 0EQL at `f^{-1}(W)`; `hchern` is the contained branch, which is Stacks 0EQR read
coefficientwise at clause (1)(b).  These are the two results the source's proof cites, and
nothing else of it is assumed: the case matching, the identification
`W' ∩ D' = g^{-1}(W ∩ D)`, part (1) of Stacks 0EPB on the `g`-side, and the passage from the
prime cycles of the case analysis to an arbitrary cycle are all proved. -/
theorem gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' (k + (r : ℤ)))
    (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (hsq : IsPullback g E'.1.ι E.1.ι f)
    (hadd : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → ¬ W.subspace ≤ E.1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        cycleCoeffOfClosedSubspace D (E'.1.ι ≫ p') hE'
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).2 (k + (r : ℤ))
            (canonicalGeometricPoint D.site D.base D.base_mem
              (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1.toFunctor) T' =
          ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
              (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T')
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → W.subspace ≤ E.1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        (∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
              (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T') =
          ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
            (gysinComponentCycle D p E hE k
                (canonicalGysinComponentRule D p hp E hE k chern) W).1 T *
              flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T')
    (α : CycleGroup D p (k + 1)) :
    gysinCycleMap D p' E' hE' (k + (r : ℤ))
        (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern')
        (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1) hkr α) =
      flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
        (k + (r : ℤ)) rfl
        (gysinCycleMap D p E hE k (canonicalGysinComponentRule D p hp E hE k chern) α) :=
  gysinCycleMap_flatPullbackMap_eq_of_comparison D p hp p' hp' hfbase r hflat hr E hE E' hE'
    hgbase hgflat hgr k (canonicalGysinComponentRule D p hp E hE k chern)
    (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') hkr
    (gysinFlatPullbackComparison_of_intersectionAdditivity D p hp p' hp' f hfbase r hflat hr
      E hE E' hE' g hgbase hgflat hgr k chern chern' hsq.w hadd hchern) hsq α

end NonContained

/-! ### Flatness and the relative dimension of `g`, by base change -/

section BaseChange

/-- **Flatness of `g` in the diagram of Remark 0ER3.** In the cartesian square of Remark 0ER3 the
morphism `g : E' ⟶ E` is flat when `f` is: it is the base change of `f` along the closed
immersion `i : E → X`, and flatness of a morphism of algebraic spaces is stable under base
change. -/
theorem isFlat_gysinBaseChange (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {E : ClosedSubspaces D.site D.base D.base_mem X}
    {E' : ClosedSubspaces D.site D.base D.base_mem X'}
    {f : X' ⟶ X} {g : E'.1.toFunctor ⟶ E.1.toFunctor}
    (hsq : IsPullback g E'.1.ι E.1.ι f) (hflat : IsFlat D.site D.base D.base_mem f) :
    IsFlat D.site D.base D.base_mem g :=
  isFlat_of_isPullback_of_isAlgebraicSpace D.site D.base D.base_mem hsq hp'.1 hp.1 hflat

/-- **The relative dimension of `g` in the diagram of Remark 0ER3.** In the cartesian square of
Remark 0ER3, with `f` locally of finite type, `g` has relative dimension `r` when `f` does, by
part (1) of Stacks 04NS: the relative dimension is invariant under base change.

That `f` be locally of finite type is part of the source's hypothesis: Definition 06LR speaks of
the relative dimension only of a morphism locally of finite type. -/
theorem hasRelativeDimension_gysinBaseChange (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {E : ClosedSubspaces D.site D.base D.base_mem X} (hE : D.IsGood (E.1.ι ≫ p))
    {E' : ClosedSubspaces D.site D.base D.base_mem X'} (r : ℕ)
    {f : X' ⟶ X} {g : E'.1.toFunctor ⟶ E.1.toFunctor}
    (hsq : IsPullback g E'.1.ι E.1.ι f)
    (hft : IsLocallyOfFiniteType D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) :
    HasRelativeDimension r D.site D.base D.base_mem g := fun x =>
  (hasRelativeDimensionAt_iff_of_isPullback D.site D.base D.base_mem hsq.flip hp'.1 hE.1 hp.1
    hft x (r : ℕ∞)).1 (hr _)

end BaseChange

/-! ### Stacks 0ER6 with the two properties of `g` derived -/

section Derived

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hft : IsLocallyOfFiniteType D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hsq : IsPullback g E'.1.ι E.1.ι f) (k : ℤ)

include hp hp' hfbase hflat hft hr hE hE' hsq

/-- **Stacks 0ER6 for the cartesian square of Remark 0ER3.** In
Situation 0EDT let `f : X' ⟶ X` be a flat morphism of relative dimension `r` of good algebraic
spaces over `B` — so locally of finite type, by Definition 06LR — let `(ℒ, s, i : E → X)` be as
in Definition 0ER1, and form the cartesian square of Remark 0ER3, with `E' = E ×_X X'`,
`g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every `(k+1)`-cycle `α` on `X`

  `(i')^* f^* α = g^* i^* α`,

an identity of `(k+r)`-cycles on `E'`, hence of classes in `CH_{k+r}(E')`.

The properties of `g` come from the square: it is a morphism over `B`
(`AlgebraicGeometry.Space.comp_structure_of_isPullback`), flat
(`AlgebraicGeometry.Space.isFlat_gysinBaseChange`) and of relative dimension `r`
(`AlgebraicGeometry.Space.hasRelativeDimension_gysinBaseChange`).  The component rules on both
sides are the canonical ones, so clause (1)(a) of Stacks 0ER1 is the cycle `[E ∩ W]_k` of
Stacks 0EE9 that the source means and only clause (1)(b) is free.

**Two inputs are carried**, and they are the two results the source's proof of this lemma cites
beyond `W' ∩ D' = g^{-1}(W ∩ D)`: `hadd`, the intersection additivity on `X'` — the shape of
Stacks 0EQL at the closed subspace `f^{-1}(W)`, which the source uses silently in applying the
Gysin map of Definition 0ER1 to the cycle of a closed subspace — and `hchern`, the contained
branch, which is Stacks 0EQR read coefficientwise at clause (1)(b). -/
theorem gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity_of_isPullback
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' (k + (r : ℤ)))
    (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (hadd : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → ¬ W.subspace ≤ E.1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        cycleCoeffOfClosedSubspace D (E'.1.ι ≫ p') hE'
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1
            (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).2 (k + (r : ℤ))
            (canonicalGeometricPoint D.site D.base D.base_mem
              (gysinPreimageIntersectionSubspace D p hp p' hp' f E' hE' W).1.toFunctor) T' =
          ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
              (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T')
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → W.subspace ≤ E.1 →
      ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        (∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
            flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
              (gysinComponentCycle D p' E' hE' (k + (r : ℤ))
                (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern') W').1 T') =
          ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
            (gysinComponentCycle D p E hE k
                (canonicalGysinComponentRule D p hp E hE k chern) W).1 T *
              flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g
                (comp_structure_of_isPullback D p p' hfbase hsq) r
                (isFlat_gysinBaseChange D p hp p' hp' hsq hflat)
                (hasRelativeDimension_gysinBaseChange D p hp p' hp' hE r hsq hft hr) T T')
    (α : CycleGroup D p (k + 1)) :
    gysinCycleMap D p' E' hE' (k + (r : ℤ))
        (canonicalGysinComponentRule D p' hp' E' hE' (k + (r : ℤ)) chern')
        (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1) hkr α) =
      flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g
        (comp_structure_of_isPullback D p p' hfbase hsq) r
        (isFlat_gysinBaseChange D p hp p' hp' hsq hflat)
        (hasRelativeDimension_gysinBaseChange D p hp p' hp' hE r hsq hft hr) k
        (k + (r : ℤ)) rfl
        (gysinCycleMap D p E hE k (canonicalGysinComponentRule D p hp E hE k chern) α) :=
  gysinCycleMap_flatPullbackMap_eq_of_intersectionAdditivity D p hp p' hp' f hfbase r hflat hr
    E hE E' hE' g (comp_structure_of_isPullback D p p' hfbase hsq)
    (isFlat_gysinBaseChange D p hp p' hp' hsq hflat)
    (hasRelativeDimension_gysinBaseChange D p hp p' hp' hE r hsq hft hr) k chern chern' hkr
    hsq hadd hchern α

end Derived

end AlgebraicGeometry.Space

end
