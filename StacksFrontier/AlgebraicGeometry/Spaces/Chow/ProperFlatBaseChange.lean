module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceUnramifiedPairSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# Proper pushforward and flat pullback of cycles in a cartesian square

In Situation 0EDT let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of good algebraic spaces over `B`, with `f` proper and `g` flat of
relative dimension `r`. **Stacks 0EPD** asserts three things: that `f'` is proper, that `g'` is
flat of relative dimension `r`, and that for every `k`-cycle `α` on `X`

`g^* f_* α = f'_* (g')^* α`

in `Z_{k+r}(Y')` — an identity of *cycles*, not of Chow classes.

All three are stated and proved here, at the source's hypotheses and with nothing carried. The
degree count at the generic points, `deg(Z/Z')·m_{T'}(g^{-1}(Z')) = ∑_T m_T((g')^{-1}(Z))·
deg(T/T')`, which is the coefficientwise content of the third assertion at a prime cycle, is
proved in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`; this file
adds the collapse of the pushforward sum, the geometry confining both coefficient sums, and the
passage from a prime cycle to an arbitrary cycle.

The third assertion appears in two forms, with the same conclusion.
`AlgebraicGeometry.Space.flatPullback_properPushforward` takes the degree count as a hypothesis,
bundled as `AlgebraicGeometry.Space.ProperFlatBaseChangeComparison`, and carries no tag: it is
the cycle bookkeeping on its own.
`AlgebraicGeometry.Space.flatPullback_properPushforward_of_isPullback` supplies that bundle from
the count, so it takes only the source's hypotheses, and it is where the third assertion of the
tag is registered.

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatBaseChangeComparison`: the degree count
  `deg(Z/Z')·m_{T'}(g^{-1}(Z')) = ∑_T m_T((g')^{-1}(Z))·deg(T/T')` at the generic points, bundled
  as a one-field structure. It is *proved*, so the form of the third assertion that takes it is a
  step and not a registration; the bundle is retained because other files state the comparison
  at it.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isPullback`: **Stacks 0EPD, first assertion**, that `f'`
  is proper. This is Stacks 04WP.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_of_isPullback`: **Stacks 0EPD,
  second assertion**, that `g'` is flat of relative dimension `r`. This is Stacks 03MO for the
  flatness and part (1) of Stacks 04NS for the relative dimension.
* `AlgebraicGeometry.Space.flatPullback_properPushforward_of_isPullback`: **Stacks 0EPD, third
  assertion**, the identity `g^* f_* α = f'_* (g')^* α` in `Z_{k+r}(Y')`, at the source's
  hypotheses and with nothing carried.
* `AlgebraicGeometry.Space.flatPullback_properPushforward`: the same identity with the degree
  count taken as the bundled hypothesis `cmp`. It carries no tag.
* `AlgebraicGeometry.Space.ProperFlatBaseChangeComparison.multiplicity_comm`: Stacks 0EPD at a
  prime cycle, read coefficientwise — the bundled degree count with the pushforward sum put
  back.
* `AlgebraicGeometry.Space.finsum_properCycleMult_mul_flatPullbackMult`: the coefficient of
  `g^*f_*[Z]` at `T'` is the single product `deg(Z/Z')·m_{T'}(g^{-1}(Z'))`, the sum over the
  integral closed subspaces of `Y` collapsing to one term.
* `AlgebraicGeometry.Space.properCycleMult_closureImage`: the multiplicity of the image closure
  of `Z` in `f_*[Z]` is the degree of Stacks 0EP1 at `Z`.
* `AlgebraicGeometry.Space.hasRelativeDimension_of_isPullback`: part (1) of Stacks 04NS read as
  the invariance of the relative dimension of a morphism under base change.
* `AlgebraicGeometry.Space.finite_cycleSupport_mem_closureImage`: the form of Stacks 0ENZ the
  exchange of sums needs — finitely many subspaces of a cycle have a given point of `|Y|` in
  the closure of the image of their point set.

## Implementation notes

**How the square is formed.** The square is a hypothesis `sq : IsPullback g' f' f g` on the
four presheaves, which is the source's "fibre product diagram"; it is *scheme-theoretic*, being
a limit in the category of presheaves on the big fppf site, not a statement about point sets.
The base-change stability results for properness and flatness are stated in the category
`AlgebraicGeometry.AlgebraicSpaces` of Stacks 02X2, so the square is transported there by
`AlgebraicGeometry.Space.isPullback_homMk` of
`StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceUnramifiedPairSplitting`, the inclusion
of that full subcategory being fully faithful. The scheme-theoretic inverse images the flat
pullback is built from are `CategoryTheory.Subfunctor.preimage` of Stacks 083Q, inside
`AlgebraicGeometry.Space.flatPullbackMult`; no inverse image is formed in this file.

**Which hypotheses the cycle identity carries, and why.**

* Goodness of all four corners over `B` is the source's own hypothesis, and the structure
  morphisms with the three commutations `g' ≫ sX = sX'`, `f' ≫ sY' = sX'`, `f ≫ sY = sX` and
  `g ≫ sY = sY'` are what makes the four maps morphisms over `B`, as the proper pushforward and
  the flat pullback of cycles ask.
* `hfproper` is the source's properness of `f`. Only quasi-compactness of `f` and of `f'` is
  used — that is all `AlgebraicGeometry.Space.properCyclePushforward` of Stacks 0EP1 asks for — and
  the quasi-compactness of `f'` is obtained from properness of `f'`, that is from the first
  assertion, which therefore appears in the statement of the third.
* `hg'flat` and `hg'r` are flatness and the relative dimension of `g'`. They are the second
  assertion, and could be discharged from `hgflat` and `hgr` by
  `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_of_isPullback`; they are carried
  explicitly because `AlgebraicGeometry.Space.flatPullbackMap` takes them as arguments, so that
  the two flat pullbacks in the identity are the ones the reader supplies rather than ones
  reconstructed inside the statement.
* The degree count at the generic points is a hypothesis of
  `AlgebraicGeometry.Space.flatPullback_properPushforward` and is supplied, not assumed, in
  `AlgebraicGeometry.Space.flatPullback_properPushforward_of_isPullback`, the form that carries
  the tag. For every integral closed subspace `Z ⊆ X`, with `Z'` the closure of the image of `Z`
  under `f`, and every integral closed subspace `T' ⊆ Y'`,

  `deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`,

  where `deg` is `AlgebraicGeometry.Space.properCycleDegree` of Stacks 0EP1 and the
  multiplicities are `AlgebraicGeometry.Space.flatPullbackMult` of Stacks 0EP8, that is the
  geometric lengths Stacks 0EE9 attaches to the two scheme-theoretic inverse images. This is
  `Space.BaseChangeDegreeCount.properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper`
  of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`, proved along
  the source's route — `[Z] = [𝒪_Z]_k` (Stacks 0EED), part (1) of Stacks 0EP3 on both sides, and
  flat base change in degree zero, part (1) of Stacks 073K — read at the single pair of generic
  points the coefficient identity needs, which is what lets it avoid the cycle identity of
  part (2) of Stacks 0EPB for a coherent module. That the left-hand side is the whole coefficient
  of `g^*f_*[Z]` at `T'` is
  `AlgebraicGeometry.Space.finsum_properCycleMult_mul_flatPullbackMult` below.

**What the third assertion proves.** The passage from the prime-cycle comparison to an
arbitrary cycle. A cycle is a locally finite, in general infinite, sum of prime cycles, so the
additivity of the two maps does not suffice: the coefficient of each side at `T'` is a double
sum, and the two double sums have to be exchanged so that the comparison applies summand by
summand. The finiteness making the exchange legitimate is Stacks 0ENZ for `f`, by
`AlgebraicGeometry.Space.finite_cycleSupport_mem_closureImage`, Stacks 0ENZ for `f'`, by
`AlgebraicGeometry.Space.finite_properCycleFibre`, and the containment of the support of
`(g')^*[Z]` in `(g')^{-1}(Z)`, which is Stacks 0EP6. The geometric step is
`mem_closureImage_of_mult_ne_zero`: the square commutes on points, so a subspace of `X'`
occurring in `(g')^*[Z]` whose image closure is `T'` puts the generic point of `T'` over the
closure of the image of `Z`, which is what confines both outer sums to one finite set of
subspaces of `X`.

**The grading.** An `AlgebraicGeometry.Space.CycleGroup` is never transported along an equality
of degrees, so the identity is stated at a pair `k`, `n` with `k + r = n` and the degree
equality as an explicit argument, which is the convention of
`AlgebraicGeometry.Space.flatPullbackMap`.

## References

* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 0462](https://stacks.math.columbia.edu/tag/0462)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The square in the category of algebraic spaces -/

section Square

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0EPD, first assertion**, by way of Stacks 04WP. In a cartesian square of algebraic
spaces over `S` the base change `f'` of a proper morphism `f` is proper. -/
@[stacks 0EPD "first assertion: the base change of a proper morphism is proper"]
theorem isProper_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (sq : IsPullback g' f' f g) (hf : IsProper B S hS f) :
    IsProper B S hS f' :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_homMk B S hS hX hY' hY hX' sq) hf

/-- **Part (1) of Stacks 04NS, as a statement about the relative dimension of a base change.**
In a cartesian square of algebraic spaces over `S` with `g` locally of finite type of relative
dimension `r`, the base change `g'` has relative dimension `r`.

The relative dimension of `g'` at a point `x'` of `X'` is the relative dimension of `g` at the
image of `x'` in `Y'`, by part (1) of Stacks 04NS read on the square with the two projections
exchanged. -/
theorem hasRelativeDimension_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y) (sq : IsPullback g' f' f g) (r : ℕ)
    (hgft : IsLocallyOfFiniteType B S hS g) (hg : HasRelativeDimension r B S hS g) :
    HasRelativeDimension r B S hS g' := fun x' =>
  (hasRelativeDimensionAt_iff_of_isPullback B S hS sq.flip hY' hX hY hgft x' (r : ℕ∞)).1
    (hg (pointsMap B S hS X' f' x'))

end Square

/-! ### Flatness and the relative dimension of the base change -/

section GoodSquare

variable (D : BaseSpaceDimensionSituation.{u})
    {X' X Y' Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EPD, second assertion.** In Situation 0EDT let the four corners of a cartesian
square of algebraic spaces over `B` be good and let `g : Y' ⟶ Y` be a morphism over `B` which is
flat of relative dimension `r`. Then the base change `g' : X' ⟶ X` is flat of relative
dimension `r`: it is locally of finite type, flat, and of relative dimension `r`.

Local finite type of `g'` is goodness of `X'/B` and the cancellation of Stacks 0462 applied to
`g' ≫ sX = sX'`, flatness is Stacks 03MO, and the relative dimension is
`AlgebraicGeometry.Space.hasRelativeDimension_of_isPullback`, which is part (1) of
Stacks 04NS. -/
@[stacks 0EPD "second assertion: the base change of a morphism flat of relative dimension r is
  flat of relative dimension r"]
theorem isFlat_and_hasRelativeDimension_of_isPullback
    (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hg'base : g' ≫ sX = sX') (hgbase : g ≫ sY = sY') (sq : IsPullback g' f' f g) (r : ℕ)
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g) :
    IsLocallyOfFiniteType D.site D.base D.base_mem g' ∧
      IsFlat D.site D.base D.base_mem g' ∧
        HasRelativeDimension r D.site D.base D.base_mem g' := by
  have hgft : IsLocallyOfFiniteType D.site D.base D.base_mem g :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hY'.1 hY.1 D.isAlgebraicSpace g sY
      (by rw [hgbase]; exact hY'.2.2)
  refine ⟨isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX'.1 hX.1 D.isAlgebraicSpace
      g' sX (by rw [hg'base]; exact hX'.2.2), ?_,
    hasRelativeDimension_of_isPullback D.site D.base D.base_mem hX.1 hY'.1 hY.1 sq r hgft hgr⟩
  exact (isFlat_isStableUnderBaseChange D.site D.base D.base_mem).of_isPullback
    (isPullback_homMk D.site D.base D.base_mem hX.1 hY'.1 hY.1 hX'.1 sq).flip
    hgflat

end GoodSquare

/-! ### The subspaces of a cycle through a point of the target -/

section Fibre

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- For a cycle `α` on `X` and a point `ξ` of `|Y|`, only finitely many of the integral closed
subspaces occurring in `α` have `ξ` in the closure of the image of their point set.

This is the form of Stacks 0ENZ that the exchange of sums below needs: a neighbourhood of `ξ`
witnessing local finiteness of the family of image closures meets all of those closures, and
only finitely many may meet it. -/
theorem finite_cycleSupport_mem_closureImage (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hfbase : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : LocallyFinite (cycleSupportFamily D α)) (ξ : points D.site D.base D.base_mem Y) :
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X | α Z ≠ 0 ∧
      ξ ∈ subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z).subspace}.Finite := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hfbase hf
    (cycleSupportFamily D α) (isClosed_cycleSupportFamily D sX hX α) hα
  obtain ⟨V, hV, hVfin⟩ := hlf ξ
  refine hVfin.subset ?_
  rintro Z ⟨hZne, hZmem⟩
  refine ⟨ξ, ?_, mem_of_mem_nhds hV⟩
  show ξ ∈ closure (pointsMap D.site D.base D.base_mem X f '' cycleSupportFamily D α Z)
  rw [closure_image_cycleSupportFamily D sY hY f α hZne]
  exact hZmem

/-- The multiplicity of the closure of the image of `Z` in `f_*[Z]` is the degree of Stacks 0EP1
at `Z`: it is the branch of `AlgebraicGeometry.Space.properCycleMult` that is not cut to zero. -/
theorem properCycleMult_closureImage (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    properCycleMult D sX hX sY hY f Z
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z) =
      properCycleDegree D sX hX sY hY f Z := by
  unfold properCycleMult
  split_ifs with h
  · rfl
  · exact absurd rfl h

end Fibre

/-! ### The commutation of flat pullback with proper pushforward -/

section Commutation

variable (D : BaseSpaceDimensionSituation.{u})
    {X' X Y' Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hg'base : g' ≫ sX = sX') (hf'base : f' ≫ sY' = sX') (hfbase : f ≫ sY = sX)
    (hgbase : g ≫ sY = sY') (r : ℕ)
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (hg'flat : IsFlat D.site D.base D.base_mem g')
    (hg'r : HasRelativeDimension r D.site D.base D.base_mem g')

/-- **Stacks 0EPD at a prime cycle, with the pushforward sum already carried out.** The
coefficient of an integral closed subspace `T' ⊆ Y'` in `g^*f_*[Z]` is the single product
`deg(Z/Z')·m_{T'}(g^{-1}(Z'))`, for `Z'` the closure of the image of `Z` under `f`: the
pushforward `f_*[Z]` is `deg(Z/Z')·[Z']`, so the sum over the integral closed subspaces of `Y`
collapses to one term.

Only the right-hand side of the comparison stays a sum, and it is the one the source expands
over the irreducible components of `(g')^{-1}(Z)`. -/
theorem finsum_properCycleMult_mul_flatPullbackMult
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem Y') :
    (∑ᶠ Z' : IntegralClosedSubspace D.site D.base D.base_mem Y,
        properCycleMult D sX hX sY hY f Z Z' *
          flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr Z' T') =
      properCycleDegree D sX hX sY hY f Z *
        flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) f Z) T' := by
  rw [finsum_eq_single _ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f Z) fun Z' hZ' => by
        rw [properCycleMult_eq_zero_of_ne D sX hX sY hY f Z (Ne.symm hZ'), zero_mul],
    properCycleMult_closureImage D sX hX sY hY f Z]

/-- **The degree count of Stacks 0EPD at the generic points, bundled.** For an integral closed
subspace `Z ⊆ X` with image closure `Z' ⊆ Y` under `f`, and for an integral closed subspace
`T' ⊆ Y'`,

`deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`,

the sum on the right being over the integral closed subspaces of `X'` whose image closure under
`f'` is `T'`. The multiplicities are the geometric lengths of Stacks 0EE2 that Stacks 0EE9
attaches to the two scheme-theoretic inverse images, and the degrees are the extension degrees
of function fields of Stacks 0EP1.

**The count is a theorem.** Its field is
`Space.BaseChangeDegreeCount.properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper`
of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`, and
`AlgebraicGeometry.Space.flatPullback_properPushforward_of_isPullback` below builds this bundle
from it, so the registered form of the third assertion assumes nothing. The bundle is retained
because other files state the comparison at it. -/
structure ProperFlatBaseChangeComparison where
  /-- The degree count at the generic points: `deg(Z/Z')·m_{T'}(g^{-1}(Z'))` is the sum over the
  integral closed subspaces `T` of `(g')^{-1}(Z)` with image closure `T'` of
  `m_T((g')^{-1}(Z))·deg(T/T')`. -/
  degree_mul_mult : ∀ (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
      (T' : IntegralClosedSubspace D.site D.base D.base_mem Y'),
    properCycleDegree D sX hX sY hY f Z *
        flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) f Z) T' =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
          properCycleMult D sX' hX' sY' hY' f' T T'

/-- **Stacks 0EPD at a prime cycle, read coefficientwise.** The two defining sums producing the
coefficient of `T'` in `g^*f_*[Z]` and in `f'_*(g')^*[Z]` agree.

This is the degree count of
`AlgebraicGeometry.Space.ProperFlatBaseChangeComparison.degree_mul_mult` with the pushforward
sum on the left put back, by
`AlgebraicGeometry.Space.finsum_properCycleMult_mul_flatPullbackMult`. -/
theorem ProperFlatBaseChangeComparison.multiplicity_comm
    (cmp : ProperFlatBaseChangeComparison D sX' hX' sX hX sY' hY' sY hY (f := f) (f' := f')
      hg'base hgbase r hgflat hgr hg'flat hg'r)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem Y') :
    (∑ᶠ Z' : IntegralClosedSubspace D.site D.base D.base_mem Y,
        properCycleMult D sX hX sY hY f Z Z' *
          flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr Z' T') =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
          properCycleMult D sX' hX' sY' hY' f' T T' := by
  rw [finsum_properCycleMult_mul_flatPullbackMult D sX hX sY' hY' sY hY hgbase r hgflat hgr
    Z T', cmp.degree_mul_mult Z T']

/-- An integral closed subspace of `X'` occurring in `(g')^*[Z]` and having `T'` for the closure
of its image under `f'` puts the generic point of `T'` over a point of the closure of the image
of `Z` under `f`.

The square commutes on points, so the image under `f'` of the inverse image of `|Z|` under `g'`
is carried by `|g|^{-1}` of the image of `|Z|` under `f`; that set is closed, so it contains the
closure of the image of the subspace, hence the generic point of `T'`. -/
private theorem mem_closureImage_of_mult_ne_zero (sq : IsPullback g' f' f g)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T' : IntegralClosedSubspace D.site D.base D.base_mem Y')
    (hm : flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T ≠ 0)
    (hT : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY'.1
      (D.isDecentSpace_of_isGood sY' hY') f' T = T') :
    pointsMap D.site D.base D.base_mem Y' g
        (T'.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z).subspace := by
  have hsub := subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX' hX' sX hX g' hg'base r
    hg'flat hg'r Z T hm
  have hclosed : IsClosed (subspacePointSet D.site D.base D.base_mem Y
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z).subspace) :=
    isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 _
  have hcomm : pointsMap D.site D.base D.base_mem Y' g ∘
      pointsMap D.site D.base D.base_mem X' f' =
      pointsMap D.site D.base D.base_mem X f ∘ pointsMap D.site D.base D.base_mem X' g' := by
    rw [← pointsMap_comp D.site D.base D.base_mem X' f' g,
      ← pointsMap_comp D.site D.base D.base_mem X' g' f, sq.w]
  have himg : pointsMap D.site D.base D.base_mem X' f' ''
      subspacePointSet D.site D.base D.base_mem X' T.subspace ⊆
      pointsMap D.site D.base D.base_mem Y' g ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
            (D.isDecentSpace_of_isGood sY hY) f Z).subspace := by
    rintro y ⟨x', hx', rfl⟩
    have hval : pointsMap D.site D.base D.base_mem Y' g
        (pointsMap D.site D.base D.base_mem X' f' x') =
        pointsMap D.site D.base D.base_mem X f
          (pointsMap D.site D.base D.base_mem X' g' x') := congrFun hcomm x'
    rw [Set.mem_preimage, hval,
      IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z]
    exact subset_closure ⟨_, hsub hx', rfl⟩
  have hgen := T'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY'.1
  have hmemT' : T'.ambientGenericPoint D.site D.base D.base_mem ∈
      closure (pointsMap D.site D.base D.base_mem X' f' ''
        subspacePointSet D.site D.base D.base_mem X' T.subspace) := by
    rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY'.1
      (D.isDecentSpace_of_isGood sY' hY') f' T, hT, ← hgen]
    exact subset_closure rfl
  exact closure_minimal himg
    (hclosed.preimage (continuous_pointsMap D.site D.base D.base_mem g)) hmemT'

include hf'base hfbase in
/-- The integral closed subspaces of `X'` which occur in `(g')^*[Z]` for some `Z` occurring in
`α` through the generic point of `T'`, and whose image closure under `f'` is `T'`, form a finite
set.

For each of the finitely many such `Z` the cycle `(g')^*[Z]` is a cycle, so Stacks 0ENZ leaves
only finitely many subspaces in it with image closure `T'`; the set is the union of those
finitely many finite sets. -/
private theorem finite_preimageSupport_closureImage
    (hfqc : IsQuasiCompact D.site D.base D.base_mem f)
    (hf'qc : IsQuasiCompact D.site D.base D.base_mem f')
    (k : ℤ) (α : CycleGroup D sX k)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem Y') :
    {T : IntegralClosedSubspace D.site D.base D.base_mem X' |
      ∃ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        (α.1 Z ≠ 0 ∧ pointsMap D.site D.base D.base_mem Y' g
            (T'.ambientGenericPoint D.site D.base D.base_mem) ∈
          subspacePointSet D.site D.base D.base_mem Y
            (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) f Z).subspace) ∧
          flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T ≠ 0 ∧
            IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY'.1
              (D.isDecentSpace_of_isGood sY' hY') f' T = T'}.Finite := by
  have hinner : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      {T : IntegralClosedSubspace D.site D.base D.base_mem X' |
        flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T ≠ 0 ∧
          IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY'.1
            (D.isDecentSpace_of_isGood sY' hY') f' T = T'}.Finite := fun Z =>
    finite_properCycleFibre D sX' hX' sY' hY' hf'base hf'qc
      (flatPullbackIntegralCycle D sX' hX' sX hX g' hg'base r hg'flat hg'r Z).1
      (flatPullbackIntegralCycle D sX' hX' sX hX g' hg'base r hg'flat hg'r Z).2.1 T'
  refine ((finite_cycleSupport_mem_closureImage D sX hX sY hY hfbase hfqc α.1 α.2.1
    (pointsMap D.site D.base D.base_mem Y' g
      (T'.ambientGenericPoint D.site D.base D.base_mem))).biUnion fun Z _ => hinner Z).subset ?_
  rintro T ⟨Z, hZA, hm, hT⟩
  exact Set.mem_biUnion (x := Z) hZA ⟨hm, hT⟩

/-- **Stacks 0EPD, third assertion, with the degree count taken as a hypothesis.** In
Situation 0EDT let the four corners of a cartesian square of good algebraic spaces over `B` be
good, let `f : X ⟶ Y` be proper and let `g : Y' ⟶ Y` be flat of relative dimension `r`. Then,
granted the bundled degree count `cmp`, for every `k`-cycle `α` on `X`

`g^*f_*α = f'_*(g')^*α`

in `Z_{k+r}(Y')`.

**This is the conditional form and it carries no tag.** The bundle `cmp` is a theorem, proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`;
`AlgebraicGeometry.Space.flatPullback_properPushforward_of_isPullback` below supplies it and so
takes only the source's hypotheses, and that unconditional form is where the third assertion of
Stacks 0EPD is registered. What is kept here is the cycle bookkeeping the two forms share.

The pushforward along `f'` is legitimate because `f'` is proper, which is the first assertion
`AlgebraicGeometry.Space.isProper_of_isPullback` and appears in the statement; the pullback
along `g'` is legitimate because `g'` is flat of relative dimension `r`, which is the second
assertion `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_of_isPullback` and is carried
here as the hypotheses `hg'flat` and `hg'r` so that the degree bookkeeping stays explicit.

**What this declaration adds to the degree count.** The passage to an arbitrary cycle, the
bookkeeping the source performs tacitly — a cycle is a locally finite, in general infinite, sum
of prime cycles, so the coefficient of each side at `T'` is a double sum and the two have to be
exchanged for the degree count to apply summand by summand. The finiteness making that
legitimate is Stacks 0ENZ for `f` and for `f'` together with the containment of the support of
`(g')^*[Z]` in `(g')^{-1}(Z)`, which is Stacks 0EP6. That the left-hand side of the count is the
whole coefficient of `g^*f_*[Z]` at `T'` is
`AlgebraicGeometry.Space.finsum_properCycleMult_mul_flatPullbackMult`. No conjunct of the
conclusion is a hypothesis and no map is assumed to commute with anything. -/
theorem flatPullback_properPushforward (sq : IsPullback g' f' f g)
    (hfproper : IsProper D.site D.base D.base_mem f)
    (cmp : ProperFlatBaseChangeComparison D sX' hX' sX hX sY' hY' sY hY (f := f) (f' := f')
      hg'base hgbase r hgflat hgr hg'flat hg'r)
    (k n : ℤ) (hkn : k + (r : ℤ) = n) (α : CycleGroup D sX k) :
    flatPullbackMap D sY' hY' sY hY g hgbase r hgflat hgr k n hkn
        (properCyclePushforward D sX hX sY hY hfbase hfproper.2.1.2 k α) =
      properCyclePushforward D sX' hX' sY' hY' hf'base
        (isProper_of_isPullback D.site D.base D.base_mem hX'.1 hX.1 hY'.1 hY.1 sq hfproper).2.1.2
        n (flatPullbackMap D sX' hX' sX hX g' hg'base r hg'flat hg'r k n hkn α) := by
  have hf'qc : IsQuasiCompact D.site D.base D.base_mem f' :=
    (isProper_of_isPullback D.site D.base D.base_mem hX'.1 hX.1 hY'.1 hY.1 sq hfproper).2.1.2
  refine Subtype.ext (funext fun T' => ?_)
  set ξ : points D.site D.base D.base_mem Y :=
    pointsMap D.site D.base D.base_mem Y' g
      (T'.ambientGenericPoint D.site D.base D.base_mem) with hξ
  have hL : (flatPullbackMap D sY' hY' sY hY g hgbase r hgflat hgr k n hkn
        (properCyclePushforward D sX hX sY hY hfbase hfproper.2.1.2 k α)).1 T' =
      ∑ᶠ Z' : IntegralClosedSubspace D.site D.base D.base_mem Y,
        ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
          α.1 Z * properCycleMult D sX hX sY hY f Z Z' *
            flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr Z' T' := by
    rw [flatPullbackMap_apply]
    exact finsum_congr fun Z' => by
      rw [properPushforward_apply D sX hX sY hY hfbase hfproper.2.1.2 k α Z', finsum_mul]
  have hR : (properCyclePushforward D sX' hX' sY' hY' hf'base hf'qc n
        (flatPullbackMap D sX' hX' sX hX g' hg'base r hg'flat hg'r k n hkn α)).1 T' =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem X',
        ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
          α.1 Z * flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
            properCycleMult D sX' hX' sY' hY' f' T T' := by
    rw [properPushforward_apply]
    exact finsum_congr fun T => by rw [flatPullbackMap_apply, finsum_mul]
  set S : Set (IntegralClosedSubspace D.site D.base D.base_mem X) :=
    {Z | α.1 Z ≠ 0 ∧ ξ ∈ subspacePointSet D.site D.base D.base_mem Y
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z).subspace}
  have hfin := finite_cycleSupport_mem_closureImage D sX hX sY hY hfbase hfproper.2.1.2 α.1 α.2.1 ξ
  have hvanL : ∀ (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      α.1 Z * properCycleMult D sX hX sY hY f Z Z' *
          flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr Z' T' ≠ 0 →
      Z' ∈ (fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
            IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
              (D.isDecentSpace_of_isGood sY hY) f Z) '' S ∧ Z ∈ S := by
    intro Z' Z hne
    have hαZ : α.1 Z ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have him : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z = Z' :=
      ((properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1
        (right_ne_zero_of_mul (left_ne_zero_of_mul hne))).1
    have hZS : Z ∈ S := ⟨hαZ, by
      rw [him]
      exact mem_subspacePointSet_of_flatPullbackMult_ne_zero D sY' hY' sY hY g hgbase r hgflat hgr
        Z' T' (right_ne_zero_of_mul hne)⟩
    exact ⟨⟨Z, hZS, him⟩, hZS⟩
  have hvanR : ∀ (T : IntegralClosedSubspace D.site D.base D.base_mem X')
      (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      α.1 Z * flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T *
          properCycleMult D sX' hX' sY' hY' f' T T' ≠ 0 →
      T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X' |
          ∃ Z ∈ S, flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T ≠ 0 ∧
            IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY'.1
              (D.isDecentSpace_of_isGood sY' hY') f' T = T'} ∧ Z ∈ S := by
    intro T Z hne
    have hm : flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T ≠ 0 :=
      right_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have hT : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY'.1
        (D.isDecentSpace_of_isGood sY' hY') f' T = T' :=
      ((properCycleMult_ne_zero_iff D sX' hX' sY' hY' f' T T').1
        (right_ne_zero_of_mul hne)).1
    have hZS : Z ∈ S := ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hne),
      mem_closureImage_of_mult_ne_zero D sX' hX' sX hX sY' hY' sY hY hg'base r
        hg'flat hg'r sq Z T T' hm hT⟩
    exact ⟨⟨Z, hZS, hm, hT⟩, hZS⟩
  rw [hL, hR,
    finsum_exchange_of_vanishing _ (hfin.image _) hfin hvanL,
    finsum_exchange_of_vanishing _
      (finite_preimageSupport_closureImage D sX' hX' sX hX sY' hY' sY hY hg'base hf'base hfbase
        r hg'flat hg'r hfproper.2.1.2 hf'qc k α T')
      hfin hvanR]
  refine finsum_congr fun Z => ?_
  rw [finsum_congr fun Z' => mul_assoc (α.1 Z) (properCycleMult D sX hX sY hY f Z Z')
      (flatPullbackMult D sY' hY' sY hY g hgbase r hgflat hgr Z' T'),
    ← mul_finsum, finsum_congr fun T => mul_assoc (α.1 Z)
      (flatPullbackMult D sX' hX' sX hX g' hg'base r hg'flat hg'r Z T)
      (properCycleMult D sX' hX' sY' hY' f' T T'),
    ← mul_finsum,
    ProperFlatBaseChangeComparison.multiplicity_comm D sX' hX' sX hX sY' hY' sY hY hg'base
      hgbase r hgflat hgr hg'flat hg'r cmp Z T']

/-- **Stacks 0EPD, third assertion.** In Situation 0EDT let the four corners of a cartesian
square of good algebraic spaces over `B` be good, let `f : X ⟶ Y` be proper and let
`g : Y' ⟶ Y` be flat of relative dimension `r`. Then for every `k`-cycle `α` on `X`

`g^*f_*α = f'_*(g')^*α`

in `Z_{k+r}(Y')`.

**Nothing is carried.** The pushforward along `f'` is legitimate because `f'` is proper, which is
the first assertion `AlgebraicGeometry.Space.isProper_of_isPullback` and appears in the
statement; the pullback along `g'` is legitimate because `g'` is flat of relative dimension `r`,
which is the second assertion
`AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_of_isPullback` and is written out as the
hypotheses `hg'flat` and `hg'r` so that the degree bookkeeping stays explicit.

The two numerical inputs are proved. One is the degree count at the generic points,
`deg(Z/Z')·m_{T'}(g^{-1}(Z')) = ∑_T m_T((g')^{-1}(Z))·deg(T/T')`, which is
`Space.BaseChangeDegreeCount.properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper`
of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`: the source's
route (`[Z] = [𝒪_Z]_k`, part (1) of Stacks 0EP3 on both sides, and flat base change in degree
zero, part (1) of Stacks 073K) read at one pair of generic points. The other is that the
left-hand side of the count is the whole coefficient of `g^*f_*[Z]` at `T'`, by
`AlgebraicGeometry.Space.finsum_properCycleMult_mul_flatPullbackMult`. The count is bundled into
`AlgebraicGeometry.Space.ProperFlatBaseChangeComparison` and handed to
`AlgebraicGeometry.Space.flatPullback_properPushforward` above, which is where the passage from a
prime cycle to an arbitrary cycle is carried out. -/
@[stacks 0EPD "third assertion: the identity g^* f_* α = f'_* (g')^* α in Z_{k+r}(Y') for an
  arbitrary k-cycle α, at the source's hypotheses"]
theorem flatPullback_properPushforward_of_isPullback (sq : IsPullback g' f' f g)
    (hfproper : IsProper D.site D.base D.base_mem f)
    (k n : ℤ) (hkn : k + (r : ℤ) = n) (α : CycleGroup D sX k) :
    flatPullbackMap D sY' hY' sY hY g hgbase r hgflat hgr k n hkn
        (properCyclePushforward D sX hX sY hY hfbase hfproper.2.1.2 k α) =
      properCyclePushforward D sX' hX' sY' hY' hf'base
        (isProper_of_isPullback D.site D.base D.base_mem hX'.1 hX.1 hY'.1 hY.1 sq hfproper).2.1.2
        n (flatPullbackMap D sX' hX' sX hX g' hg'base r hg'flat hg'r k n hkn α) :=
  flatPullback_properPushforward D sX' hX' sX hX sY' hY' sY hY hg'base hf'base hfbase hgbase r
    hgflat hgr hg'flat hg'r sq hfproper
    ⟨fun Z T' =>
      BaseChangeDegreeCount.properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper D sX'
        hX' sX hX sY' hY' sY hY hg'base hf'base hfbase hgbase r hgflat hgr hg'flat hg'r sq
        hfproper Z T'⟩
    k n hkn α

end Commutation

end AlgebraicGeometry.Space

end
