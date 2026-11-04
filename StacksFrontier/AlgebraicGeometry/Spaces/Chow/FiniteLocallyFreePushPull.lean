module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCoherentCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite

/-!
# Push and pull along a finite locally free morphism

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be finite locally free of
degree `d` in the sense of Stacks 03ZV. **Stacks 0EPE** asserts three things: `f` is proper,
`f` is flat of relative dimension `0`, and `f_*f^*α = dα` for every `α ∈ Z_k(Y)`.

## Main definitions

* `AlgebraicGeometry.Space.FiniteLocallyFreeRankChartComparison`: the chart comparison that
  Stacks 03ZU owes, which relates the direct-image definition of Stacks 03ZV to the
  representable reading of Stacks 03ZW; it is the hypothesis of
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison`.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isFiniteLocallyFreeOfRank`: **Stacks 0EPE**, that `f` is
  proper, for an arbitrary morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_zero_of_isFiniteLocallyFreeOfRank`:
  **Stacks 0EPE**, that `f` is flat of relative dimension `0`, likewise.
* `AlgebraicGeometry.Space.properPushforward_flatCyclePullback`: **Stacks 0EPE**, the identity
  `f_*f^*α = dα` on `Z_k(Y)`.
* `AlgebraicGeometry.Space.isFinite_and_isFlat_of_isFiniteLocallyFreeOfRank`: a finite locally
  free morphism of degree `d` is finite, flat and locally of finite presentation, which is
  Stacks 0416 for the definition of Stacks 03ZV.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isFinite`: a finite morphism of algebraic
  spaces over `S` is locally quasi-finite, which is what makes the relative dimension vanish.
* `AlgebraicGeometry.Space.eq_of_mem_subspacePointSet_ambientGenericPoint`: an integral closed
  subspace whose generic point lies in another one of the same δ-dimension is that one.
* `AlgebraicGeometry.Space.eq_cycleImageSubspace_of_mult_ne_zero`: the only integral closed
  subspace of `Y` whose inverse image carries a given integral closed subspace of `X` with a
  nonzero weight is the integral closed image of the latter.

## Implementation notes

**The hypothesis of the source.** Finite local freeness of degree `d` is the definition of
Stacks 03ZV, `AlgebraicGeometry.Space.IsFiniteLocallyFreeOfRank`: `f` is affine and `f_*𝒪_X`
is a finite locally free `𝒪_Y`-module of rank `d` on the small étale ringed site of `Y`. The
source proves properness and flatness from Morphisms of Spaces, Lemma 0416, which this
development states for the *representable* reading of finite local freeness — every represented
base change of `f` is a finite locally free morphism of schemes — and the comparison of the two
readings is Stacks 03ZU, which is not available here. The reason is recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteLocallyFreeRepresentable.lean`: the comparison needs
clause (2) of Stacks 03DL for the Zariski versus small étale sites of a scheme, and that
comparison cannot be a morphism of ringed sites in the sense this development can state. The
missing input is isolated there as a chart comparison, carried here as
`AlgebraicGeometry.Space.FiniteLocallyFreeRankChartComparison` and consumed through
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison`. It is the
only input to the properness and flatness clauses that is not proved.

**Flat of relative dimension zero.** As in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/FlatCompositeRelativeDimension.lean`, being flat of
relative dimension `r` is written out as the conjunction of `AlgebraicGeometry.Space.IsFlat` of
Stacks 03ML, `AlgebraicGeometry.Space.IsLocallyOfFiniteType` of Stacks 03XF — which the
relative-dimension predicate presupposes — and
`AlgebraicGeometry.Space.HasRelativeDimension` of Stacks 06LR, part (2). The source omits the
verification that a finite morphism has relative dimension `0`; it is carried out here from
Stacks 04NV, `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero`,
together with local quasi-finiteness of a finite morphism.

Neither of the first two clauses uses the base, the dimension function or goodness, so both are
stated for an arbitrary morphism of algebraic spaces over `S` rather than inside
Situation 0EDT; specialized to the situation they are the source's first two conclusions.

**The cycle identity.** Flat pullback of cycles along a morphism of algebraic spaces is
Stacks 0EP8, which this repository does not construct; as in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/FlatPullbackFirstChernCap.lean` it is carried as
`AlgebraicGeometry.Space.FlatCyclePullback`, that is as data *together with the formula that
defines it*: the multiplicity of an integral closed subspace `T ⊆ X` in the inverse image
`f^{-1}(W)` of an integral closed subspace `W ⊆ Y`, and the statement that the coefficient of
`f^*α` at `T` is `∑_W α_W · m_{T,f^{-1}(W)}`. Proper pushforward of cycles is the library's own
`AlgebraicGeometry.Space.properPushforward` of Stacks 0EP1, whose only hypothesis beyond the
situation is quasi-compactness of `f` — supplied here by the properness clause, which is all
that finite local freeness itself contributes to this clause.

The one further input is `hdeg`, the degree of the fibre of `f` over the generic point of an
integral closed subspace `W ⊆ Y` of δ-dimension `k`: the sum, over the integral closed subspaces
of `X` whose integral closed image is `W`, of the multiplicity in `f^{-1}(W)` times the degree
of the residue field extension there, is `d`. It is the local computation the source performs with
lengths of modules: base change keeps `f` finite locally free of degree `d` by Stacks 03ZY, so
`f_*f^*𝒪_W` is locally free of rank `d` on `W`, and the chain
`f_*f^*[W] = f_*f^*[𝒪_W]_k = f_*[f^*𝒪_W]_k = [f_*f^*𝒪_W]_k = d[W]` runs through Stacks 0EPB,
part (2), Stacks 0EP3, part (2), and Stacks 0EEC, which reads the multiplicity of `W` in the
cycle of a coherent module as the length at the generic point. Of that chain this repository
has 0EPB, and 0EP3 conditionally on three hypotheses of its own; what it does not have is the
pullback or the direct image of a module along a morphism of algebraic spaces — the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/ProperPushforwardCoherentCycle.lean` record that
there is no stalk formula for a direct image at all — so the identity is assumed at one generic
point, at degrees, and nothing is assumed about cycles.

What is proved from it is the source's reduction. For an arbitrary `α ∈ Z_k(Y)` and an
arbitrary integral closed subspace `W' ⊆ Y`, the coefficient of `f_*f^*α` at `W'` is a sum over
the integral closed subspaces `T ⊆ X` with integral closed image `W'`, each weighted by
Stacks 0EP0; in it only the term `W = W'` of the flat pullback survives, because a subspace `W`
contributing a nonzero multiplicity at such a `T` contains `W'` and has the same δ-dimension,
hence equals it by
`AlgebraicGeometry.Space.eq_of_mem_subspacePointSet_ambientGenericPoint`, which is Stacks 0EE6.
The surviving sum is `α_{W'}` times the degree of `hdeg`, the weight of Stacks 0EP0 being the
residue degree exactly where the multiplicity does not vanish.

A subspace of δ-dimension other than `k` has coefficient zero in `α`, so `hdeg` is asked for
only at δ-dimension `k`; and there the conclusion returns it, by evaluating the conclusion on
the cycle of that one subspace. The hypothesis is thus the one-subspace case of the statement,
and what is added is the passage from it to every cycle. This is the same division of labour as
in Stacks 0EP3 above, whose hypothesis `hlen` is likewise the pointwise case of its
conclusion.

## References

* [Stacks Project, Tag 0EPE](https://stacks.math.columbia.edu/tag/0EPE)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZY](https://stacks.math.columbia.edu/tag/03ZY)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EEC](https://stacks.math.columbia.edu/tag/0EEC)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EP0](https://stacks.math.columbia.edu/tag/0EP0)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-! ### A finite morphism is locally quasi-finite, and the two clauses that follow -/

section QuasiFinite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A finite morphism of algebraic spaces over `S` is locally quasi-finite.

Finiteness is a condition on the represented base changes by Stacks 03ZQ, a finite morphism of
schemes is locally of finite type and locally quasi-finite, and local quasi-finiteness in the
sense of Stacks 03XJ is étale local on the source and target, stable under base change and
local on the target for the fpqc, hence for the fppf, topology, so Stacks 03MJ reads the
every-chart condition off the represented base changes. -/
theorem isLocallyQuasiFinite_of_isFinite {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : IsFinite B S hS f) :
    IsLocallyQuasiFinite B S hS f := by
  obtain ⟨hrep, hpfin⟩ := (isFinite_iff_representable B S hS f hX hY).mp hf
  have : MorphismProperty.IsStableUnderBaseChange
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  refine (holdsOnEveryEtaleChart_iff_relative B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hX hY f hrep).mpr ?_
  exact presheaf_inverseImage_mono B S hS
    (fun p hp => by
      have : _root_.AlgebraicGeometry.IsFinite p := hp
      exact ⟨inferInstance, inferInstance⟩) hpfin

/-- **The chart comparison that Stacks 03ZU owes, in its rank form.** At an étale chart `V` of
the target of a representable morphism `g` of algebraic spaces over `S`, the rank of the
restriction of `g_*𝒪` to the slice of the small étale ringed site at `V` agrees with the rank of
the base change of `g` over `V` as a morphism of schemes.

This is the hypothesis of
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison`, which is
where it is explained; it is named here because the three clauses of Stacks 0EPE all carry
it. -/
abbrev FiniteLocallyFreeRankChartComparison : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (hg : yoneda.relativelyRepresentable g.hom) (r : ℕ)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C),
    (RingedSite.IsFiniteLocallyFreeOfRank
        ((smallEtaleRingedSite B S hS Y.1 Y.2).over V)
        ((pushforwardStructureModule B S hS g).over V) r ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map (hg.snd V.1.hom)) r)

/-- A finite locally free morphism of degree `d` of algebraic spaces over `S` is finite, flat
and locally of finite presentation.

Granted the chart comparison, the direct-image definition of Stacks 03ZV passes to the
representable reading of Stacks 03ZW by Stacks 03ZU, where it weakens to finite local freeness
without a rank, and there the equivalence is Stacks 0416. -/
theorem isFinite_and_isFlat_of_isFiniteLocallyFreeOfRank
    (hcross : FiniteLocallyFreeRankChartComparison B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank B S hS f d) :
    IsFinite B S hS f.hom ∧ IsFlat B S hS f.hom ∧
      IsLocallyOfFinitePresentation B S hS f.hom := by
  have hrep : yoneda.relativelyRepresentable f.hom :=
    relativelyRepresentable_of_isAffineHom B S hS f hf.1.1
  have hrank := (isFiniteLocallyFreeOfRank_iff_presheaf_of_chartComparison B S hS hcross
    f hrep d).1 hf
  refine (isFiniteLocallyFree_presheaf_iff B S hS X.property Y.property f.hom).1
    (presheaf_inverseImage_mono B S hS (fun p hp => ?_) hrank)
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p d := hp
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p d

/-! ### Stacks 0EPE: properness and flatness of relative dimension zero -/

/-- **Stacks 0EPE, first conclusion.** A finite locally free morphism of degree `d` of algebraic
spaces over `S` is proper.

A finite locally free morphism is finite by Stacks 0416, and a finite morphism is proper by
Stacks 04NZ. The goodness hypotheses of Situation 0EDT are not used, so the conclusion is drawn
for an arbitrary morphism of algebraic spaces over `S`. -/
@[stacks 0EPE "f is proper"]
theorem isProper_of_isFiniteLocallyFreeOfRank
    (hcross : FiniteLocallyFreeRankChartComparison B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank B S hS f d) :
    IsProper B S hS f.hom :=
  ((isFinite_iff_isAffineHom_and_isProper B S hS X.property Y.property f.hom).1
    (isFinite_and_isFlat_of_isFiniteLocallyFreeOfRank B S hS hcross f d hf).1).2

/-- A finite locally free morphism of degree `d` is quasi-compact: it is proper, and a proper
morphism is of finite type. -/
theorem isQuasiCompact_of_isFiniteLocallyFreeOfRank
    (hcross : FiniteLocallyFreeRankChartComparison B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank B S hS f d) :
    IsQuasiCompact B S hS f.hom :=
  (isProper_of_isFiniteLocallyFreeOfRank B S hS hcross f d hf).2.1.2

/-- **Stacks 0EPE, second conclusion.** A finite locally free morphism of degree `d` of
algebraic spaces over `S` is flat of relative dimension `0`: it is flat and locally of finite
type, and has relative dimension `0` at every point of its source.

Flatness is Stacks 0416. For the relative dimension, the morphism is finite, hence locally
quasi-finite and locally of finite type, and Stacks 04NV turns local quasi-finiteness into the
vanishing of the relative dimension at every point. The goodness hypotheses of Situation 0EDT
are not used. -/
@[stacks 0EPE "f is flat of relative dimension 0"]
theorem isFlat_and_hasRelativeDimension_zero_of_isFiniteLocallyFreeOfRank
    (hcross : FiniteLocallyFreeRankChartComparison B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank B S hS f d) :
    IsFlat B S hS f.hom ∧ IsLocallyOfFiniteType B S hS f.hom ∧
      HasRelativeDimension 0 B S hS f.hom := by
  obtain ⟨hfin, hflat, -⟩ :=
    isFinite_and_isFlat_of_isFiniteLocallyFreeOfRank B S hS hcross f d hf
  have hlft : IsLocallyOfFiniteType B S hS f.hom :=
    isLocallyOfFiniteType_of_isFinite B S hS X.property Y.property hfin
  exact ⟨hflat, hlft, (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
    f.hom hlft).1 (isLocallyQuasiFinite_of_isFinite B S hS X.property Y.property hfin)⟩

end QuasiFinite

/-! ### Equal δ-dimension inside an integral closed subspace -/

section Maximality

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- An integral closed subspace of a good algebraic space whose generic point lies in another
integral closed subspace of the same δ-dimension is that subspace.

The generic point attains the δ-dimension bound of the ambient subspace, so Stacks 0EE6 makes
it a generic point of an irreducible component of it; that subspace is irreducible, so the
component is the whole of it, and an integral closed subspace is determined by its set of
points by Stacks 0ENF. -/
theorem eq_of_mem_subspacePointSet_ambientGenericPoint (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (W W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hmem : W'.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem Y W.subspace)
    (hdim : deltaDimension D sY W' = deltaDimension D sY W) :
    W' = W := by
  have _hsober : QuasiSober (points D.site D.base D.base_mem Y) :=
    quasiSober_points_of_isGood D sY hY
  set T : IrreducibleCloseds (points D.site D.base D.base_mem Y) :=
    integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 W with hT
  have hTcl : IsClosed (subspacePointSet D.site D.base D.base_mem Y W.subspace) := T.isClosed
  have hirr : deltaDimensionIrreducible D sY hY T = deltaDimension D sY W :=
    deltaDimensionIrreducible_eq_of_isGenericPoint D sY hY T
      (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1)
  have hbound : deltaDimensionClosed D sY hY
      (subspacePointSet D.site D.base D.base_mem Y W.subspace) hTcl ≤
      ((deltaDimension D sY W : ℤ) : EInt) := by
    have h := deltaDimensionClosed_eq_deltaDimensionIrreducible D sY hY T
    rw [hirr] at h
    exact le_of_eq h
  obtain ⟨C, hC⟩ := isGenericPoint_of_deltaDimensionClosed_le D sY hY
    (subspacePointSet D.site D.base D.base_mem Y W.subspace) hTcl
    (W'.ambientGenericPoint D.site D.base D.base_mem) hmem (deltaDimension D sY W) hbound hdim
  have hTspace : IrreducibleSpace
      (subspacePointSet D.site D.base D.base_mem Y W.subspace) :=
    Subtype.irreducibleSpace T.isIrreducible
  have hTsober : QuasiSober (subspacePointSet D.site D.base D.base_mem Y W.subspace) :=
    hTcl.isClosedEmbedding_subtypeVal.quasiSober
  have hCuniv : C.1 = (Set.univ : Set (subspacePointSet D.site D.base D.base_mem Y W.subspace)) :=
    irreducibleComponents_eq_singleton.subset C.2
  have himg := hTcl.isClosedEmbedding_subtypeVal.closure_image_eq
    ({⟨W'.ambientGenericPoint D.site D.base D.base_mem, hmem⟩} :
      Set (subspacePointSet D.site D.base D.base_mem Y W.subspace))
  rw [Set.image_singleton, hC, hCuniv, Set.image_univ, Subtype.range_coe] at himg
  refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
    (IrreducibleCloseds.ext ?_)
  exact (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).symm.trans himg

end Maximality

/-! ### Stacks 0EPE: pushforward after pullback is multiplication by the degree -/

section Formula

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : AlgebraicSpaces D.site D.base D.base_mem}

/-- The subspaces of `Y` with a nonzero multiplicity at an integral closed subspace `T ⊆ X`
whose integral closed image carries a nonzero weight are the integral closed image of `T`.

A nonzero multiplicity puts the generic point of `T` over `|W|` and pins the δ-dimension of `T`
to that of `W`; a nonzero weight pins the δ-dimension of the image of `T` to that of `T`. So
the image lies in `W` with the same δ-dimension, and
`AlgebraicGeometry.Space.eq_of_mem_subspacePointSet_ambientGenericPoint` identifies them. -/
theorem eq_cycleImageSubspace_of_mult_ne_zero (sX : X.obj ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (pb : FlatCyclePullback D sX hX sY hY f.hom 0)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X.obj)
    (hweight : properPushforwardWeight D sX hX sY hY f.hom T ≠ 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj)
    (hmult : pb.mult W T ≠ 0) :
    cycleImageSubspace D sY hY f.hom T = W := by
  have hTW : deltaDimension D sX T = deltaDimension D sY W := by
    simpa using pb.deltaDimension_eq_of_mult_ne_zero W T hmult
  have himg : deltaDimension D sY (cycleImageSubspace D sY hY f.hom T) =
      deltaDimension D sX T := by
    by_contra h
    exact hweight (properPushforwardWeight_eq_zero D sX hX sY hY f.hom h)
  refine eq_of_mem_subspacePointSet_ambientGenericPoint D sY hY W _ ?_ (himg.trans hTW)
  rw [IntegralClosedSubspace.ambientGenericPoint_closureImage D hX.1 hY.1
    (D.isDecentSpace_of_isGood sY hY) f.hom T]
  exact pb.mult_support W T hmult

/-- **Stacks 0EPE, third conclusion.** In Situation 0EDT let `X/B` and `Y/B` be good and let
`f : X ⟶ Y` be finite locally free of degree `d`. Then `f_*f^*α = dα` for every `α ∈ Z_k(Y)`.

Only the term of the flat pullback at `W'` itself survives in the coefficient of `f_*f^*α` at
an integral closed subspace `W' ⊆ Y`, by
`AlgebraicGeometry.Space.eq_cycleImageSubspace_of_mult_ne_zero`, and what is left is `α_{W'}`
times the degree `hdeg` of the fibre over the generic point of `W'`; at a `W'` of δ-dimension
other than `k` the coefficient of `α` there vanishes and both sides are zero. -/
@[stacks 0EPE "f_* f^* alpha = d alpha"]
theorem properPushforward_flatCyclePullback
    (hcross : FiniteLocallyFreeRankChartComparison D.site D.base D.base_mem)
    (sX : X.obj ⟶ D.space) (hX : D.IsGood sX) (sY : Y.obj ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f.hom ≫ sY = sX) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank D.site D.base D.base_mem f d)
    (pb : FlatCyclePullback D sX hX sY hY f.hom 0)
    (k : ℤ)
    (hdeg : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj,
      deltaDimension D sY W = k →
      ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W},
        pb.mult W T * (cycleResidueDegree D sX hX sY hY f.hom
          (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ) = (d : ℤ))
    (α : CycleGroup D sY k) :
    properPushforward D sX hX sY hY hbase
        (isQuasiCompact_of_isFiniteLocallyFreeOfRank D.site D.base D.base_mem hcross f d hf) k
        (pb.map k k (by simp) α) = (d : ℤ) • α := by
  have h0 : k + ((0 : ℕ) : ℤ) = k := by simp
  refine Subtype.ext (funext fun W' => ?_)
  -- where the multiplicity does not vanish, the weight of Stacks 0EP0 is the residue degree
  have hweq : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X.obj,
      cycleImageSubspace D sY hY f.hom T = W' →
      pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T =
        pb.mult W' T * (cycleResidueDegree D sX hX sY hY f.hom
          (T.ambientGenericPoint D.site D.base D.base_mem) : ℤ) := by
    intro T hT
    by_cases hmult : pb.mult W' T = 0
    · rw [hmult, zero_mul, zero_mul]
    · refine congrArg _ (properPushforwardWeight_eq_cycleResidueDegree D sX hX sY hY f.hom ?_)
      rw [hT]
      simpa using (pb.deltaDimension_eq_of_mult_ne_zero W' T hmult).symm
  -- only the term of the flat pullback at `W'` itself contributes
  have hterm : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem X.obj,
      cycleImageSubspace D sY hY f.hom T = W' →
      (pb.map k k h0 α).1 T * properPushforwardWeight D sX hX sY hY f.hom T =
        α.1 W' * (pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T) := by
    intro T hT
    by_cases hweight : properPushforwardWeight D sX hX sY hY f.hom T = 0
    · rw [hweight, mul_zero, mul_zero, mul_zero]
    · have hsingle : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.obj, W ≠ W' →
          α.1 W * pb.mult W T = 0 := by
        intro W hW
        by_cases hmult : pb.mult W T = 0
        · rw [hmult, mul_zero]
        · exact absurd ((eq_cycleImageSubspace_of_mult_ne_zero D sX hX sY hY f pb T hweight
            W hmult).symm.trans hT) hW
      rw [pb.coeff k k h0 α T, finsum_eq_single _ W' hsingle, mul_assoc]
  calc _
      = ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W'},
          α.1 W' * (pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T) :=
        finsum_mem_congr rfl hterm
    _ = α.1 W' * ∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
          cycleImageSubspace D sY hY f.hom T = W'},
          pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T :=
        (mul_finsum_mem _ _).symm
    _ = ((d : ℤ) • α).1 W' := by
        rw [AddSubgroup.coe_zsmul, Pi.smul_apply, zsmul_eq_mul]
        by_cases hk : deltaDimension D sY W' = k
        · have hsum : (∑ᶠ T ∈ {T : IntegralClosedSubspace D.site D.base D.base_mem X.obj |
              cycleImageSubspace D sY hY f.hom T = W'},
              pb.mult W' T * properPushforwardWeight D sX hX sY hY f.hom T) = (d : ℤ) :=
            (finsum_mem_congr rfl hweq).trans (hdeg W' hk)
          rw [hsum, mul_comm]
          norm_cast
        · have hαW' : α.1 W' = 0 := by
            by_contra hne
            exact hk (α.2.2 W' hne)
          rw [hαW', zero_mul, mul_zero]

end Formula

end AlgebraicGeometry.Space

end
