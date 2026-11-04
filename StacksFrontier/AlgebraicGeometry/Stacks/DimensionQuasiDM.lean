module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMChartDimensionBound
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMFieldFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute

/-!
# Non-negativity of the dimension of a quasi-DM algebraic stack

**Stacks 0DS5** records that an algebraic stack may have negative dimension, the classifying
stack `[Spec k/𝐆_m]` having dimension `-1`, but that a quasi-DM algebraic stack is of
non-negative dimension, so that a quasi-DM 1-morphism has fibres of non-negative dimension.
This file proves the second of those two assertions, in the fibre form the remark states it. The
first, the example `[Spec k/𝐆_m] ⟶ Spec k`, is
`AlgebraicGeometry.Stack.classifyingStack_multiplicativeGroup_dimension_lt` in
`StacksFrontier/AlgebraicGeometry/Stacks/ClassifyingStackMultiplicativeGroupExample.lean`.

## Main results

* `AlgebraicGeometry.Stack.zero_le_dimensionSubNat`: subtracting a relative dimension `d` from a
  finite dimension `m ≥ d` of an algebraic space leaves a non-negative value.
* `AlgebraicGeometry.Stack.zero_le_dimensionAtPoint`: the dimension arithmetic — the dimension of
  a locally Noetherian algebraic stack at a point is non-negative at a smooth chart whose
  relative dimension there is at most the dimension of the chart, given the reading of
  Stacks 0AFM at that chart as the hypothesis `h0AFM`.
* `AlgebraicGeometry.Stack.zero_le_dimensionAtPoint_fieldFibreStackSquare`: the non-negativity of
  the dimension at a fibre of a quasi-DM 1-morphism locally of finite type, which the Stacks 0DS5
  statement
  `AlgebraicGeometry.Stack.isQuasiDMAbs_and_zero_le_dimensionAtPoint_fieldFibreStackSquare`
  (in `StacksFrontier/AlgebraicGeometry/Stacks/QuasiDMFibreDimension.lean`) combines with the
  quasi-DM-ness of the fibre.
* `AlgebraicGeometry.Stack.zero_le_dimension`: the dimension of such a stack is non-negative.

## Implementation notes

`AlgebraicGeometry.Stack.dimensionAtPoint` is the infimum of the admissible values of the
formula of Stacks 0AFN. Negativity therefore runs the favourable way, a single chart bounding the
dimension from above, and that is how
`AlgebraicGeometry.Stack.dimensionAtPoint_le_neg_one` is proved. Non-negativity runs the
unfavourable way: a lower bound for an infimum is a statement about every chart, and one chart
gives it only once Stacks 0AFM identifies the dimension with the value read there. That
identification is a theorem of the library — Stacks 0AFM is
`AlgebraicGeometry.Stack.dimensionSubNat_eq_dimensionSubNat_of_isSmooth` and the dimension
formula it yields is Stacks 0DRJ,
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`, both in
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionChartIndependence.lean`. The arithmetic statement
`AlgebraicGeometry.Stack.zero_le_dimensionAtPoint` nevertheless keeps the reading as its
hypothesis `h0AFM`: it is a statement of the library that predates this file's work and is left
exactly as it stands. The Stacks 0DS5 statement below does not go through it; it bounds the
infimum of the formula of Stacks 0AFN chart by chart and needs no such reading.

What quasi-DM-ness contributes is the inequality `hdm`, that the relative dimension `d` of the
chart at `t` does not exceed the dimension `m` of the chart there — equivalently that the fibre
`T_x` of the chart is no larger at `t` than `T` is. Stacks 0DS5 asserts this of a quasi-DM stack
without citation; it is proved, at a fibre, as
`AlgebraicGeometry.Stack.relativeDimensionAt_le_dimensionAtPoint_of_isQuasiDM` in
`StacksFrontier/AlgebraicGeometry/Stacks/QuasiDMChartDimensionBound.lean`, and
`AlgebraicGeometry.Stack.zero_le_dimensionAtPoint_fieldFibreStackSquare` applies it at every
chart the formula of Stacks 0AFN admits. The two arithmetic statements
take `hdm` as an argument and so bear no tag themselves, the quasi-DM hypothesis of
`AlgebraicGeometry.Stack.zero_le_dimensionAtPoint` being unused for that reason. Nor does the
negative half of the remark bear one:
`AlgebraicGeometry.Stack.dimensionAtPoint_le_neg_one` takes the chart computation of Stacks 0DRK
as its arguments `m`, `d` and `m < d`, so it deduces the conclusion of that half of the remark
from its own content rather than proving it.

The pointwise input `hdm` rests on is Stacks 04NV: a locally quasi-finite morphism of algebraic
spaces has relative dimension `0` at every point of its source. By itself it does not give
`hdm`, and what quasi-DM-ness supplies about the diagonal has to be read with care. Stacks 0CPL
part (1) says that for algebraic spaces `T₁`, `T₂` over a quasi-DM 1-morphism `f : 𝒳 ⟶ 𝒴`
the comparison `T₁ ×_𝒳 T₂ ⟶ T₁ ×_𝒴 T₂` is locally quasi-finite, and
part (2) says the same of the induced map on isomorphism spaces, which at one point is the
stabilizer; both are theorems of the library, in
`StacksFrontier/AlgebraicGeometry/Stacks/SeparatedIsomPullback.lean`, part (1) at `:258` and
part (2) at `:473`. Two readings of part (1) have to be kept apart, because they do not have the
same answer.

*The absolute reading fails.* `AlgebraicGeometry.Stack.IsQuasiDMAbs` is quasi-DM-ness over
`Spec(ℤ)`, Stacks 050D part (6), so for a bare quasi-DM algebraic stack the only comparison
part (1) offers is against `T ×_{Spec(ℤ)} Spec κ`. That bounds `d` by the relative dimension of
`T ⟶ Spec(ℤ)` at `t`, not by `m`, and the step from one to the other — that the base change of
`T` along a field-valued point of the base has dimension at most `dim_t(T)` at the image of
`t` — is false. Take `T = Spec k(y)` over a field `k`: its unique point has `m = 0`, while
`k(y) ⊗_k k(y)` is a localisation of the one-dimensional domain `k(y)[z]` in which the prime
`(z - y)` survives, so it is one-dimensional and that prime is a closed point of it whose every
open neighbourhood has dimension `1`. The classical repair, `T` locally of finite type over the
base, is not merely missing from the formula of Stacks 0AFN but unavailable: `Spec k(y)` is
itself a locally Noetherian quasi-DM algebraic stack no smooth chart of which is locally of
finite type over the base, so the chart independence of Stacks 0AFM cannot be used to choose a
better chart.

*The fibre reading succeeds.* Remark Stacks 0DS5 appeals to non-negativity at the fibres of the
1-morphism of the lemma preceding it, and that 1-morphism is locally of finite type. So let
`f : 𝒯 ⟶ 𝒳` be quasi-DM and locally of finite type and let `p` be a field-valued point of `𝒳`
with field spectrum `Spec k`. The fibre `𝒯 ×_𝒳 Spec k` is a quasi-DM algebraic stack whose
projection to `Spec k` is quasi-DM, by
`AlgebraicGeometry.Stack.isQuasiDM_fieldFibreStackSquare_fst` and
`AlgebraicGeometry.Stack.isQuasiDMAbs_fieldFibreStackSquare` in
`StacksFrontier/AlgebraicGeometry/Stacks/QuasiDMFieldFibre.lean`; that projection is locally of
finite type by Stacks 06FU, so a chart `T ⟶ 𝒯 ×_𝒳 Spec k` of the formula of Stacks 0AFN, which
is locally of finite type by that formula's own requirement, is locally of finite type over
`Spec k` by Stacks 06FT. Over a field spectrum the obstruction above disappears and `hdm`
follows:

* part (1) at `T₁ = T` and `T₂ = Spec κ`, for a field-valued point `Spec κ` of the fibre
  representing the image of `t`, makes `T ×_{𝒯_p} Spec κ ⟶ T ×_{Spec k} Spec κ` locally
  quasi-finite; its source is the field fibre of Stacks 0DRG, whose dimension at the point above
  `t` is `d`;
* its target is locally of finite type over `Spec κ`, being a base change of `T ⟶ Spec k`, and
  has dimension `dim_t(T) = m` at the image point, by
  `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra`
  (`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDimensionAtPoint.lean:844`);
* `d ≤ m` is then `Space.dimensionAtPoint_le_dimensionAtPoint_of_isLocallyQuasiFinite_fieldTarget`
  in `StacksFrontier/AlgebraicGeometry/Stacks/QuasiDMChartDimensionComparison.lean`, the
  flatness-free dimension bound over a field spectrum: Stacks 04NV makes the comparison of
  relative dimension `0`, Stacks 04NR part (1) adds the relative dimensions of the two legs over
  `Spec κ`, and both of them are absolute dimensions because the base is a field spectrum,
  Stacks 0D4M.

So the chart comparison that `hdm` needs is available, and the flat locally quasi-finite chart of
Stacks 06MF is not what the fibre form of the remark requires.

*The bridge of Stacks 04XB is now closed.* Part (1) delivers
`AlgebraicGeometry.Stack.IsLocallyQuasiFinite` of the comparison 1-morphism, a condition on its
base changes to schemes of the site, whereas the dimension bound above is about a morphism of
algebraic-space presheaves. The forward half of that bridge is
`AlgebraicGeometry.Stack.prop_representingMap_of_relativeProperty` in
`StacksFrontier/AlgebraicGeometry/Stacks/DiagonalSchemePoint.lean`, and the comparison is
representable by algebraic spaces by
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_mapBase` in
`StacksFrontier/AlgebraicGeometry/Stacks/SeparationComposition.lean`. The three things that bridge
used to want are theorems of
`StacksFrontier/AlgebraicGeometry/Stacks/QuasiDMComparisonRepresentingMap.lean`:

* the two representability witnesses are one statement read at two cospans, namely
  `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpace_twoFibreProduct`: the
  projection of `𝒯₁ ×_𝒵 𝒯₂` to `𝒯₁` is a base change of the other leg, which is representable
  by algebraic spaces because `𝒵` is an algebraic stack, so **Stacks 0300** applies over the
  representable `𝒯₁`;
* the detection hypothesis for local quasi-finiteness is
  `AlgebraicGeometry.Space.prop_homMk_of_forall_yoneda` at the fppf locality of **Stacks 0427**,
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fppf`;
* the two together give
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_representingMap_mapBase`, and
  that with the keystone gives
  `dimensionAtPoint_le_dimensionAtPoint_representingMap_mapBase` of the same namespace: the
  comparison does not raise the dimension at a point once its target is locally of finite type
  over a field spectrum.

The cospan there is an arbitrary pair of 1-morphisms of algebraic stacks whose sources are
representable by algebraic spaces, rather than the pair of algebraic-space-valued points of
`AlgebraicGeometry.Stack.HigherDiagonal.isLocallyQuasiFinite_mapBase_of_isQuasiDM`, because the
second leg the chain above needs is the 1-morphism of a field-valued point, whose source is the
algebraic stack of a scheme of the site.

*How `hdm` is discharged.* The two dimensions are identified with `d` and with `m` at the cospan
whose first leg `x₁` is the chart `T ⟶ 𝒯_p`, whose second leg `x₂` is the 1-morphism of a
field-valued point `Spec κ` of `𝒯_p` representing the image of `t`, and whose `h` is the
projection `𝒯_p ⟶ Spec k`. Both are in
`StacksFrontier/AlgebraicGeometry/Stacks/QuasiDMChartDimensionBound.lean`.

* The source side needs nothing new. `AlgebraicGeometry.Stack.relativeDimensionAt` is by
  definition `AlgebraicGeometry.Stack.fieldFibreDimensionAt` at choices which
  `AlgebraicGeometry.Stack.exists_eq_fieldFibreDimensionAt` exhibits, that is the dimension of an
  algebraic space representing `T ×_{𝒯_p} Spec κ` at a point above `t`, by
  `AlgebraicGeometry.Stack.fieldFibreDimensionAt_eq_dimensionAtPoint` and the bijection on points
  `AlgebraicGeometry.Stack.bijective_spacePointMap_representing`; and that 2-fibre product is the
  one of the source cospan, `AlgebraicGeometry.Stack.fieldFibreSquare` being the canonical square
  of the cospan `(f, the point)` in that same order.
* The target side is
  `AlgebraicGeometry.Stack.dimensionAtPoint_representingMap_twoFibreProduct_eq_dimensionAtPoint`:
  an algebraic space `Q` representing `T ×_{Spec k} Spec κ` has dimension `m` at the image of
  that point. It is **Stacks 04SD** at the target square,
  `AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare`, which makes the
  square of representing presheaves exhibit `Q` as a pullback of `T ⟶ Spec k` along
  `Spec κ ⟶ Spec k`, followed by
  `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra'` —
  the form of that base-change invariance whose two field-valued points may lie on different
  based categories, which is what `Spec κ` living over `𝒯_p` and `Spec k` over `𝒳` requires. Its
  hypothesis that `T ⟶ Spec k` be locally of finite type comes from Stacks 06FT and Stacks 06FU
  through the bridge `AlgebraicGeometry.Stack.isLocallyOfFiniteType_representingMap`. That `Q` is
  locally of finite type over `Spec κ` is the same bridge at the second projection, a base change
  of `T ⟶ Spec k`, composed with
  `AlgebraicGeometry.Stack.baseSpectrumIso` — the field spectrum the dimension comparison is
  indexed by is the spectrum of the field of `Spec κ` rather than its recorded base. The point
  bookkeeping is the compatibility of the comparison with the first projections,
  `CategoryTheory.TwoFibreProductOver.mapBase_comp_fst`, which holds definitionally at the level
  of 1-morphisms of algebraic stacks and puts the image of the chosen point of the source above
  `t`.

`AlgebraicGeometry.Stack.zero_le_dimensionAtPoint_fieldFibreStackSquare` is those two sides and
the keystone chained together, at the hypotheses of the remark: `f` quasi-DM and locally of
finite type, a field-valued point of its target, and a chart of the fibre of the formula of
Stacks 0AFN with finite dimension at the point in question.

For the absolute form of the remark — every quasi-DM algebraic stack is of non-negative
dimension — the surjective, flat, locally finitely presented, locally quasi-finite chart
`U ⟶ 𝒳` of Stacks 06MF remains the route: on `P = T ×_𝒳 U` the projection to `T` is flat and
locally quasi-finite, hence of relative dimension `0` by Stacks 04NV, so `dim_p(P) = m` by
Stacks 0AFH, while the projection to `U` is smooth of relative dimension `d`, so
`dim_p(P) = dim_u(U) + d ≥ d` by Stacks 0AFI and the non-negativity of the dimension of an
algebraic space at a point; that is
`AlgebraicGeometry.Space.le_dimensionAtPoint_natCast_of_isLocallyQuasiFinite_isSmooth`. The
Stacks project's own proof of Stacks 06MF derives the same comparison at a finite type point,
and it does so from part (2) of Stacks 0CPL — the stabilizer is locally quasi-finite over the
residue field — through the vanishing of the dimension of `u ×_𝒳 u`, regularity of the smooth
fibre, a regular sequence in the local ring of the chart and two shrinking lemmas. So part (2)
is no shortcut around Stacks 06MF either. Stacks 06MF is not proved here.

The dimension of the chart is taken finite, as a natural number `m` together with
`Space.dimensionAtPoint = m`, again as in
`AlgebraicGeometry.Stack.dimensionAtPoint_le_neg_one`; the relative dimension of a smooth chart
is a natural number already, the defining condition of Stacks 0AFN requiring it.

## References

* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0AFH](https://stacks.math.columbia.edu/tag/0AFH)
* [Stacks Project, Tag 0AFI](https://stacks.math.columbia.edu/tag/0AFI)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRK](https://stacks.math.columbia.edu/tag/0DRK)
* [Stacks Project, Tag 0DS5](https://stacks.math.columbia.edu/tag/0DS5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Subtracting a relative dimension `d` from a finite dimension `m` of an algebraic space with
`d ≤ m` leaves a non-negative value. -/
theorem zero_le_dimensionSubNat {m d : ℕ} (h : d ≤ m) :
    0 ≤ dimensionSubNat (m : WithBot ℕ∞) d := by
  have hz : dimensionSubNat (m : WithBot ℕ∞) d = (((m : ℤ) - (d : ℤ) : ℤ) : EInt) := rfl
  rw [hz, show (0 : EInt) = ((0 : ℤ) : EInt) from rfl, WithBotTop.coe_le_coe]
  omega

/-- A quasi-DM locally Noetherian algebraic stack has non-negative dimension at a point `x` as
soon as some smooth, locally of finite type 1-morphism `T ⟶ 𝒳` from an algebraic space has, at a
point `t` above `x`, relative dimension `d` at most the dimension `m` of `T` there: the value
`m - d` of the formula of Stacks 0AFN is then non-negative. -/
theorem zero_le_dimensionAtPoint (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (_hQuasiDM : IsQuasiDMAbs.{u, w, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (_hsm : AlgebraicStacks.IsSmooth B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS T)
    (_ht : pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
      𝒳.val.property f.hom.hom (stackPointOfSpacePoint B S hS T t) = x)
    (m : ℕ) (hm : Space.dimensionAtPoint B S hS T hT t = (m : WithBot ℕ∞))
    (d : ℕ) (_hd : relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞))
    (hdm : d ≤ m)
    (h0AFM : dimensionAtPoint B S hS 𝒳 h𝒳 x =
      dimensionSubNat (Space.dimensionAtPoint B S hS T hT t) d) :
    0 ≤ dimensionAtPoint B S hS 𝒳 h𝒳 x := by
  rw [h0AFM, hm]
  exact zero_le_dimensionSubNat hdm

/-- **Non-negativity of the dimension at a fibre (Stacks 0DS5).** Let `f : 𝒯 ⟶ 𝒳` be a quasi-DM
1-morphism of algebraic stacks over `S`, locally of finite type, and let `p` be a field-valued
point of `𝒳` with field spectrum `Spec k`. Then the fibre `𝒯 ×_𝒳 Spec k` has non-negative
dimension at every one of its points, which is what Remark Stacks 0DS5 asserts of it.

The dimension of Stacks 0AFN at a point is an infimum, over the smooth, locally of finite type
1-morphisms `T ⟶ 𝒯 ×_𝒳 Spec k` from an algebraic space and the points `t` of `T` above that
point, of the value `dim_t(T) - d` for the relative dimension `d` of the chart at `t`, so it is
enough that every such value be non-negative. The fibre's projection to `Spec k` is quasi-DM and
locally of finite type, so `d ≤ dim_t(T)` by
`AlgebraicGeometry.Stack.relativeDimensionAt_le_dimensionAtPoint_of_isQuasiDM`. That inequality
rules out `dim_t(T) = -∞`, leaves the value `⊤` where `dim_t(T)` is infinite, and makes the
difference non-negative where `dim_t(T)` is finite. No chart need be supplied: the bound holds at
every chart the formula of Stacks 0AFN admits. -/
theorem zero_le_dimensionAtPoint_fieldFibreStackSquare
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hqdm : AlgebraicStacks.IsQuasiDM B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (x : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property) :
    0 ≤ dimensionAtPoint B S hS (fieldFibreStackSquare B S hS f p).pt
      (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p) x := by
  classical
  refine le_sInf ?_
  rintro z ⟨T, hT, x₁, -, hx₁, t, -, d, hd, rfl⟩
  have hle := relativeDimensionAt_le_dimensionAtPoint_of_isQuasiDM.{u, w} B S hS p
    (fieldFibreStackSquare B S hS f p).fst
    (isQuasiDM_fieldFibreStackSquare_fst B S hS f hqdm p)
    (isLocallyOfFiniteType_fieldFibreStackSquare_fst.{u, w} B S hS f hf p) T hT x₁ hx₁ t
  rw [hd] at hle
  obtain ⟨δ, hδ⟩ : ∃ δ, Space.dimensionAtPoint B S hS T hT t = δ := ⟨_, rfl⟩
  rw [hδ] at hle ⊢
  clear hδ
  induction δ using WithBotTop.rec with
  | bot =>
    have hle' : ((d : ℕ) : WithBot ℕ∞) ≤ ⊥ := hle
    exact absurd (le_bot_iff.mp hle') (by simp)
  | top => exact le_top
  | coe m =>
    have hle' : ((d : ℕ) : WithBot ℕ∞) ≤ ((m : ℕ) : WithBot ℕ∞) := hle
    exact zero_le_dimensionSubNat (by exact_mod_cast hle')

/-- **Stacks 0DS5.** The relative dimension `dim_t(𝒯_x)` of Stacks 0DRL of a quasi-DM 1-morphism
`f : 𝒯 ⟶ 𝒳` locally of finite type of locally Noetherian algebraic stacks is non-negative at
every point `t` of `𝒯`.

The relative dimension is the infimum, over the field-valued points `p` of `𝒳` representing the
image of `t` and the points `q` above `t`, of the dimension of the fibre `𝒯 ×_𝒳 Spec k` at `q`,
so the non-negativity of each of those fibre dimensions —
`AlgebraicGeometry.Stack.zero_le_dimensionAtPoint_fieldFibreStackSquare` — bounds the infimum
from below. The two choices the formula of Stacks 0DRL makes are therefore immaterial here.

The Stacks 0DS5 registration sits on the fibre statement
`AlgebraicGeometry.Stack.isQuasiDMAbs_and_zero_le_dimensionAtPoint_fieldFibreStackSquare`, so this
reformulation at `AlgebraicGeometry.Stack.relativeStackDimensionAt` carries no second one. -/
theorem zero_le_relativeStackDimensionAt
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hqdm : AlgebraicStacks.IsQuasiDM B S hS f)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    0 ≤ relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  classical
  refine le_sInf ?_
  rintro z ⟨p, q, -, -, rfl⟩
  exact zero_le_dimensionAtPoint_fieldFibreStackSquare.{u, w} B S hS f hqdm hf p q

/-- A quasi-DM locally Noetherian algebraic stack of non-negative dimension at one of its points
has non-negative dimension: its dimension of Stacks 0AFP is a supremum over its points, and one
point of non-negative dimension bounds it from below. -/
theorem zero_le_dimension (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (_hQuasiDM : IsQuasiDMAbs.{u, w, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : 0 ≤ dimensionAtPoint B S hS 𝒳 h𝒳 x) :
    0 ≤ dimension B S hS 𝒳 h𝒳 :=
  hx.trans (le_iSup (fun y => dimensionAtPoint B S hS 𝒳 h𝒳 y) x)

end AlgebraicGeometry.Stack

end
