module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImageDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeGenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardModuleCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingGenericPointField
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition

/-!
# The third assertion of Stacks 0EPD at the source's hypotheses

In Situation 0EDT let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of good algebraic spaces over `B`, with `f` proper and `g` flat of relative
dimension `r`.  The third assertion of **Stacks 0EPD**, the identity
`g^* f_* α = f'_* (g')^* α` in `Z_{k+r}(Y')`, is proved for an arbitrary `k`-cycle `α` in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange`, at the source's hypotheses and
with nothing carried; its one numerical input, the degree count at the generic points

`deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`

for an integral closed subspace `Z ⊆ X` with `f`-image closure `Z'` and an integral closed
subspace `T' ⊆ Y'`, is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`.

**This file states the third assertion with the flatness and the relative dimension of `g'`
written out rather than supplied**, and keeps, as aliases, the names under which the degree count
and the four results it is proved from were stated here while the assertion still carried the
count.

## Main results

* `AlgebraicGeometry.Space.properFlatBaseChangeComparison`: the inhabitant of
  `AlgebraicGeometry.Space.ProperFlatBaseChangeComparison` the degree count provides, so that
  bundle is a theorem and not a hypothesis.
* `AlgebraicGeometry.Space.flatPullback_properPushforward_unconditional`: **Stacks 0EPD, third
  assertion**, at the source's hypotheses and with nothing assumed.

## Implementation notes

**Relation to `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeGenericPoints`.**
That file derives the degree count from a carried `GenericPointComparisonDatum`, by way of the
length identity `Stacks.Length.finrank_mul_length_eq_sum_finrank_mul_length_localizedModule`
stated there; the count is proved outright, with no datum, in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`, so that route is now
one derivation among two rather than the only one.

**Flatness and the relative dimension of `g'`.**  The third assertion below does not carry them:
they are the second assertion, and the statement writes them out as
`AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_of_isPullback` applied to the square, so
the hypotheses are exactly the source's.

## References

* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The degree count at the generic points

The count and the four results it is proved from are stated in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeDegreeCount`, which sits above
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange` because the third assertion of
Stacks 0EPD there carries no hypothesis and so needs the count before it.  The names below are
where they were stated while that assertion still carried the count, and are kept here. -/

section Indicator

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)

/-- **Alias** of
`BaseChangeDegreeCount.eq_ambientGenericPoint_of_mem_of_inducedDimensionValue_eq`:
a point of `|Z|` at which the induced dimension function attains `dim_δ(Z)` is the generic point
of `Z`. -/
alias eq_ambientGenericPoint_of_mem_of_inducedDimensionValue_eq :=
  BaseChangeDegreeCount.eq_ambientGenericPoint_of_mem_of_inducedDimensionValue_eq

/-- **Alias** of `AlgebraicGeometry.Space.BaseChangeDegreeCount.eq_of_mem_of_deltaDimension_eq`:
an integral closed subspace whose generic point lies in `|Z|` and whose δ-dimension equals that
of `Z` is `Z` itself. -/
alias eq_of_mem_of_deltaDimension_eq := BaseChangeDegreeCount.eq_of_mem_of_deltaDimension_eq

/-- **Alias** of
`AlgebraicGeometry.Space.BaseChangeDegreeCount.closedSubspaceCycle_integral_apply_self`: the
coefficient of an integral closed subspace in its own fundamental cycle is one. -/
alias closedSubspaceCycle_integral_apply_self :=
  BaseChangeDegreeCount.closedSubspaceCycle_integral_apply_self

/-- **Alias** of
`AlgebraicGeometry.Space.BaseChangeDegreeCount.closedSubspaceCycle_integral_apply_of_ne`: the
fundamental cycle of an integral closed subspace vanishes off that subspace. -/
alias closedSubspaceCycle_integral_apply_of_ne :=
  BaseChangeDegreeCount.closedSubspaceCycle_integral_apply_of_ne

/-- **Alias** of
`AlgebraicGeometry.Space.BaseChangeDegreeCount.isPullback_closedSubspacePreimage`: the square cut
out of a cartesian square by a closed subspace of `X` is cartesian. -/
alias isPullback_closedSubspacePreimage :=
  BaseChangeDegreeCount.isPullback_closedSubspacePreimage

/-- **Alias** of
`AlgebraicGeometry.Space.BaseChangeDegreeCount.isProper_closedSubspaceHom_comp`: the composite of
the inclusion of a closed subspace and a proper morphism is proper. -/
alias isProper_closedSubspaceHom_comp := BaseChangeDegreeCount.isProper_closedSubspaceHom_comp

/-- **Alias** of
`BaseChangeDegreeCount.nonempty_modulePullbackIso_closedSubspaceDirectImageStructureSheaf`:
flat base change in degree zero for the direct image of the structure sheaf of a closed
subspace. -/
alias nonempty_modulePullbackIso_closedSubspaceDirectImageStructureSheaf :=
  BaseChangeDegreeCount.nonempty_modulePullbackIso_closedSubspaceDirectImageStructureSheaf

/-- **Alias** of
`BaseChangeDegreeCount.properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper`:
**the degree count of Stacks 0EPD at the generic points**,
`deg(Z/Z') · m_{T'}(g^{-1}(Z')) = ∑_{T ⊆ X'} m_T((g')^{-1}(Z)) · deg(T/T')`. -/
alias properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper :=
  BaseChangeDegreeCount.properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper

end Indicator

/-! ### The comparison bundle -/

section Comparison

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

include hg'base hf'base hfbase hgbase in
/-- **An inhabitant of `AlgebraicGeometry.Space.ProperFlatBaseChangeComparison`.**  The degree
count at the generic points holds at every pair of an integral closed subspace of `X` and an
integral closed subspace of `Y'`, so the comparison the general-cycle identity of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange` is reduced to is available with
no hypothesis beyond the source's. -/
theorem properFlatBaseChangeComparison (sq : IsPullback g' f' f g)
    (hfproper : IsProper D.site D.base D.base_mem f) :
    ProperFlatBaseChangeComparison D sX' hX' sX hX sY' hY' sY hY (f := f) (f' := f')
      hg'base hgbase r hgflat hgr hg'flat hg'r :=
  ⟨fun Z T' => properCycleDegree_mul_flatPullbackMult_eq_finsum_of_isProper D sX' hX' sX hX sY'
    hY' sY hY
    hg'base hf'base hfbase hgbase r hgflat hgr hg'flat hg'r sq hfproper Z T'⟩

end Comparison

/-! ### The third assertion of Stacks 0EPD -/

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X' X Y' Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX' : X' ⟶ D.space) (hX' : D.IsGood sX') (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hg'base : g' ≫ sX = sX') (hf'base : f' ≫ sY' = sX') (hfbase : f ≫ sY = sX)
    (hgbase : g ≫ sY = sY') (r : ℕ)
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)

include hg'base hf'base hfbase in
/-- **Stacks 0EPD, third assertion.**  In Situation 0EDT let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of good algebraic spaces over `B`, let `f : X ⟶ Y` be proper and let
`g : Y' ⟶ Y` be flat of relative dimension `r`.  Then for every `k`-cycle `α` on `X`

`g^*f_*α = f'_*(g')^*α`

in `Z_{k+r}(Y')`.

Nothing is assumed: the pushforward along `f'` is legitimate because `f'` is proper, which is the
first assertion `AlgebraicGeometry.Space.isProper_of_isPullback`; the pullback along `g'` is
legitimate because `g'` is flat of relative dimension `r`, which is the second assertion
`AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_of_isPullback`; and both are written out
in the statement rather than carried.  The identity itself is
`AlgebraicGeometry.Space.flatPullback_properPushforward`, whose comparison at the generic points
is `AlgebraicGeometry.Space.properFlatBaseChangeComparison`.

A `CycleGroup` is never transported along an equality of degrees, so the identity is stated at a
pair `k`, `n` with `k + r = n` and the degree equality as an explicit argument, which is the
convention of `AlgebraicGeometry.Space.flatPullbackMap`. -/
@[stacks 0EPD "third assertion: the identity g^* f_* α = f'_* (g')^* α in Z_{k+r}(Y') for an
  arbitrary k-cycle α, at the source's hypotheses"]
theorem flatPullback_properPushforward_unconditional (sq : IsPullback g' f' f g)
    (hfproper : IsProper D.site D.base D.base_mem f)
    (k n : ℤ) (hkn : k + (r : ℤ) = n) (α : CycleGroup D sX k) :
    flatPullbackMap D sY' hY' sY hY g hgbase r hgflat hgr k n hkn
        (properCyclePushforward D sX hX sY hY hfbase hfproper.2.1.2 k α) =
      properCyclePushforward D sX' hX' sY' hY' hf'base
        (isProper_of_isPullback D.site D.base D.base_mem hX'.1 hX.1 hY'.1 hY.1 sq hfproper).2.1.2
        n (flatPullbackMap D sX' hX' sX hX g' hg'base r
          (isFlat_and_hasRelativeDimension_of_isPullback D sX' hX' sX hX sY' hY' sY hY hg'base
            hgbase sq r hgflat hgr).2.1
          (isFlat_and_hasRelativeDimension_of_isPullback D sX' hX' sX hX sY' hY' sY hY hg'base
            hgbase sq r hgflat hgr).2.2 k n hkn α) :=
  flatPullback_properPushforward D sX' hX' sX hX sY' hY' sY hY hg'base hf'base hfbase hgbase r
    hgflat hgr _ _ sq hfproper
    (properFlatBaseChangeComparison D sX' hX' sX hX sY' hY' sY hY hg'base hf'base hfbase hgbase r
      hgflat hgr _ _ sq hfproper) k n hkn α

end Main

end AlgebraicGeometry.Space

end
