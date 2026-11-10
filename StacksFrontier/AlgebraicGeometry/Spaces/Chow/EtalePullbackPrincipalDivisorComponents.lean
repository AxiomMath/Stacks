module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponentChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPreimageDominance
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimensionOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPushforwardFibreLength

/-!
# Étale pullback of a principal divisor: the canonical reading and its components

This file sits on top of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor` and carries the part of
**Stacks 0EQ2** that is read at the *canonical* embeddings `R(·) → Q(𝒪^h_{·,ξ})` of Stacks 0ENK
rather than at an arbitrary family of embeddings: the canonical data itself
(`AlgebraicGeometry.Space.integralSpaceFractionEmbedding`), both sides of the identity formed at
it (`AlgebraicGeometry.Space.targetPrincipalDivisorCycle`,
`AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycleOfGood`,
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood`), the facts that make the data on the
irreducible components of `X` derived rather than assumed — the dominance of `f|_{X'}`, goodness
of a component, the three ring-theoretic conditions of Stacks 0ENK — and the two reductions of
the source's identity, together with its proof for an integral source.

The chart material the component case needs — an étale chart of `X` read as an étale chart of `Y`
(`AlgebraicGeometry.Space.etaleChartComp`), the étale invariance of the order of vanishing
(`AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_ord_of_isEtale`), the fact that the
irreducible components of the chart `W ×_X X'` of an irreducible component are components of `W`,
the nonzerodivisor condition that follows from it, the chart reading of `g ∘ f|_{X'}` and the
dominance of `f|_{X'}`
(`AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`) —
is imported from
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponentChartReading` and
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackOrderOfVanishing`.

## References

* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0EML](https://stacks.math.columbia.edu/tag/0EML)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The canonical embeddings of Stacks 0ENK -/

/-- **Stacks 0ENK on a good integral algebraic space over the base.** The conclusions of that
lemma at every prime divisor of `X` — the henselian local ring at the generic point is a
nontrivial Noetherian local ring of dimension at most one, and `R(X)` embeds in its total ring
of fractions — assembled in `AlgebraicGeometry.Space.genericFractionEmbedding`.

Nothing is assumed: decency is `AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace` and the
étale-local Noetherian property comes from goodness over the locally Noetherian base by
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isGood`. This is the
embedding at which both sides of Stacks 0EQ2 are read, so that the order of vanishing on the
target and the order of vanishing on an irreducible component of the source are taken at the
canonical embedding and not at two unrelated ones. -/
def integralSpaceFractionEmbedding (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X) :
    GenericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 :=
  genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.2.1 hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)

/-- `AlgebraicGeometry.Space.integralSpaceFractionEmbedding` at an integral closed subspace
`W ⊆ X` of a good algebraic space, which is again good over the base by
`AlgebraicGeometry.Space.isGood_integralClosedSubspace`. -/
abbrev integralClosedSubspaceFractionEmbedding (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    GenericFractionEmbedding D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W).1 W.isIntegralSpace.2.1 :=
  integralSpaceFractionEmbedding D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace

/-! ### The principal divisors on the irreducible components -/

/-- The data on the irreducible components of `X` which the right-hand side of Stacks 0EQ2
needs beyond `g ∈ R(Y)^*` itself. For each irreducible component `X' ⊆ X`, in the notation of
that tag:

* `dom` — `f|_{X'} : X' ⟶ Y` carries the generic point of `X'` to the generic point of `Y`.
  This is the source's first step, and it is what makes `g ∘ f|_{X'}` defined (Morphisms of
  Spaces, Section 0EML).
* `locallyFinite` — local finiteness of the support of `div_{X'}(g ∘ f|_{X'})`, which is
  Stacks 0ENN on `X'`.

Everything else the right-hand side needs is proved rather than taken: goodness of `X'` over
the base is `AlgebraicGeometry.Space.isGood_integralClosedSubspace`, decency is
`AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace`, the three ring-theoretic conditions of
Stacks 0ENK on the henselian local rings at the generic points of the prime divisors of `X'`
and the embeddings `R(X') → Q(𝒪^h_{X',ξ})` they go with are
`AlgebraicGeometry.Space.integralClosedSubspaceFractionEmbedding`, that `g ∘ f|_{X'}` lies in
`R(X')^*` follows from `g ∈ R(Y)^*` because `g ∘ f|_{X'}` is the image of `g` under a ring
homomorphism, the dimension function `δ_{X'/B}` of Stacks 0EDN is
`AlgebraicGeometry.Space.deltaDimensionFunction`, and `dim_δ(X') = dim_δ(Y)` is
`AlgebraicGeometry.Space.deltaDimensionClosed_univ_irreducibleComponentSubspace`.

That this is a *special case* of the data of Stacks 0EQ2 and not a parallel copy of it is
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood.toEtaleComponentDivisorData`, which fills
every field of `AlgebraicGeometry.Space.EtaleComponentDivisorData` from these two; the right-hand
side of the tag and its coefficients are then the ones of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor`, read through that
map. -/
structure EtaleComponentDivisorDataOfGood (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) (n : ℤ)
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g) where
  /-- The restriction of `f` to an irreducible component is dominant: it carries the generic
  point of the component to the generic point of `Y`. -/
  dom : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    pointsMap D.site D.base D.base_mem W.1.subspace.toFunctor (W.1.subspace.ι ≫ f)
        (genericPoint D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX W.1).1 W.1.isIntegralSpace) =
      genericPoint D.site D.base D.base_mem hY.1 hintY
  /-- **Stacks 0ENN** on an irreducible component: the prime divisors of `X'` along which
  `g ∘ f|_{X'}` has nonzero order of vanishing are locally finite in `|X'|`. -/
  locallyFinite : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    letI E := integralClosedSubspaceFractionEmbedding D sX hX W.1
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor =>
      if principalDivisorCoefficients D.site D.base D.base_mem
            (isGood_integralClosedSubspace D sX hX W.1).1 W.1.isIntegralSpace.2.1 E.emb
            (rationalFunctionMap D.site D.base D.base_mem
              (isGood_integralClosedSubspace D sX hX W.1).1 hY.1
              W.1.isIntegralSpace hintY (W.1.subspace.ι ≫ f) (dom W) g)
            (fun Q => (hg.map (rationalFunctionMap D.site D.base D.base_mem
              (isGood_integralClosedSubspace D sX hX W.1).1 hY.1
              W.1.isIntegralSpace hintY (W.1.subspace.ι ≫ f) (dom W))).map (E.emb Q)) P = 0 then ∅
        else P.support D.site D.base D.base_mem W.1.subspace.toFunctor

namespace EtaleComponentDivisorDataOfGood

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {f : X ⟶ Y} {hbase : f ≫ sY = sX} {hetale : IsEtale D.site D.base D.base_mem f}
    {hintY : IsIntegralSpace D.site D.base D.base_mem Y} {n : ℤ}
    {hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)}
    {g : rationalFunctions D.site D.base D.base_mem hY.1} {hg : IsUnit g}
    (data : EtaleComponentDivisorDataOfGood D sX hX sY hY f hbase hetale hintY n hnY g hg)
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)

/-- **The canonical data on the components is a special case of the data of Stacks 0EQ2.** The
data `AlgebraicGeometry.Space.EtaleComponentDivisorData` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor`, out of which the
right-hand side of that tag is formed, built from the two fields carried here and from nothing
else:

* `good` — a component is good over the base by
  `AlgebraicGeometry.Space.isGood_integralClosedSubspace`;
* `nontrivial`, `noetherian`, `krullDimLE`, `emb` — the three hypotheses of Stacks 0ENK on the
  henselian local ring at the generic point of a prime divisor of a component, and the embedding
  `R(X') → Q(𝒪^h_{X',ξ})` they go with, are the fields of the canonical
  `AlgebraicGeometry.Space.integralClosedSubspaceFractionEmbedding`;
* `dom`, `locallyFinite` — the two fields carried here;
* `unit` — `g ∘ f|_{X'}` lies in `R(X')^*` because it is the image of the unit `g ∈ R(Y)^*` under
  a ring homomorphism;
* `dimFun`, `dimFun_eq` — the dimension function `δ_{X'/B}` of Stacks 0EDN is
  `AlgebraicGeometry.Space.deltaDimensionFunction`.

Everything the right-hand side of Stacks 0EQ2 needs is therefore read off the base module through
this map: `g ∘ f|_{X'} ∈ R(X')` is
`AlgebraicGeometry.Space.EtaleComponentDivisorData.componentRationalFunction`,
`div_{X'}(g ∘ f|_{X'})` is `…componentDivisorCycle`, its pushforward along `X' ⟶ X` is
`…componentDivisorPushforward`, and the coefficient of the sum at an integral closed subspace of
`X` is `…componentPushforwardCoeff`, which vanishes away from δ-dimension `n - 1` by
`…componentPushforwardCoeff_eq_zero`. None of those is restated here. -/
def toEtaleComponentDivisorData :
    EtaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g where
  good V := isGood_integralClosedSubspace D sX hX V.1
  nontrivial V := (integralClosedSubspaceFractionEmbedding D sX hX V.1).nontrivial
  noetherian V := (integralClosedSubspaceFractionEmbedding D sX hX V.1).isNoetherianRing
  krullDimLE V := (integralClosedSubspaceFractionEmbedding D sX hX V.1).krullDimLE
  emb V := (integralClosedSubspaceFractionEmbedding D sX hX V.1).emb
  dom V := data.dom V
  unit V P :=
    (hg.map (rationalFunctionMap D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX V.1).1 hY.1 V.1.isIntegralSpace hintY
        (V.1.subspace.ι ≫ f) (data.dom V))).map
      ((integralClosedSubspaceFractionEmbedding D sX hX V.1).emb P)
  locallyFinite V := data.locallyFinite V
  dimFun V :=
    deltaDimensionFunction D (V.1.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX V.1)
  dimFun_eq V :=
    deltaDimensionFunction_apply D (V.1.subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX V.1)

end EtaleComponentDivisorDataOfGood

/-! ### The data on the components is not an input -/

/-- **Stacks 0ENN on each irreducible component of `X`.** The prime divisors of an irreducible
component `X' ⊆ X` along which `g ∘ f|_{X'}` has nonzero order of vanishing are locally finite
in `|X'|`, the order being taken at the canonical embedding of Stacks 0ENK on `X'` and the
pullback of `g` being formed along the dominance proved in
`AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`.

This is what makes `div_{X'}(g ∘ f|_{X'})` a cycle at all; it is Stacks 0ENN on `X'`, and this
repository proves that lemma from a nonempty open subset over which the function is invertible
(`AlgebraicGeometry.Space.locallyFinite_principalDivisorCoefficients_ne_zero`), which is the form
in which Stacks 0EQ1 itself takes it — on the target as
`AlgebraicGeometry.Space.TargetDivisorLocallyFinite`, on an integral source as
`AlgebraicGeometry.Space.PullbackDivisorLocallyFinite`. It is the *only* thing the right-hand
side of Stacks 0EQ2 needs beyond the source's own hypotheses: the dominance of `f|_{X'}` on each
component, which was the other field of
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood`, is proved. -/
abbrev ComponentDivisorLocallyFinite (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g) : Prop :=
  ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
    letI E := integralClosedSubspaceFractionEmbedding D sX hX W.1
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem W.1.subspace.toFunctor =>
      if principalDivisorCoefficients D.site D.base D.base_mem
            (isGood_integralClosedSubspace D sX hX W.1).1 W.1.isIntegralSpace.2.1 E.emb
            (rationalFunctionMap D.site D.base D.base_mem
              (isGood_integralClosedSubspace D sX hX W.1).1 hY.1
              W.1.isIntegralSpace hintY (W.1.subspace.ι ≫ f)
              (pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace
                D sX hX sY hY hetale hintY W) g)
            (fun Q => (hg.map (rationalFunctionMap D.site D.base D.base_mem
              (isGood_integralClosedSubspace D sX hX W.1).1 hY.1
              W.1.isIntegralSpace hintY (W.1.subspace.ι ≫ f)
              (pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace
                D sX hX sY hY hetale hintY W))).map (E.emb Q)) P = 0 then ∅
        else P.support D.site D.base D.base_mem W.1.subspace.toFunctor

/-- **The data on the irreducible components of `X` is not an input of Stacks 0EQ2.** The
right-hand side `∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})` is formed from the source's own
hypotheses together with the local finiteness of Stacks 0ENN on each component, which is all that
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood` carries once its dominance field is
discharged.

The dominance of `f|_{X'}` — the source's first step, and what makes `g ∘ f|_{X'}` defined at all
— is `AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`
and is supplied here rather than assumed. -/
theorem etaleComponentDivisorData (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) (n : ℤ)
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g)
    (hfin : ComponentDivisorLocallyFinite D sX hX sY hY hetale hintY g hg) :
    EtaleComponentDivisorDataOfGood D sX hX sY hY f hbase hetale hintY n hnY g hg where
  dom W :=
    pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace D sX hX sY hY hetale
      hintY W
  locallyFinite := hfin

/-! ### Stacks 0EQ2 -/

section Identity

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g)

include hX hY hetale in
/-- **Stacks 0EQ2, the first step of the source, for an integral source.** An étale morphism
`f : X ⟶ Y` of good algebraic spaces over the base with `X` and `Y` integral is dominant: it
carries the generic point of `X` to the generic point of `Y`.

This is the source's own argument. The map on points of an étale morphism is open by
Stacks 03IR, so its range is a nonempty open subset of the irreducible `|Y|` and therefore
contains the generic point of `Y`; that point is thus the image of a point of `|X|`, which is a
specialization of the generic point of `X`, so the image of the generic point of `X` is a
generic point of `|Y|` as well, hence is the generic point, `|Y|` being Kolmogorov by
Stacks 03K3. For `X` with several irreducible components this is dominance of `f` restricted to
each of them, which is the field `dom` of
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood`. -/
theorem pointsMap_genericPoint_eq_genericPoint_of_isEtale
    (hintX : IsIntegralSpace D.site D.base D.base_mem X) :
    pointsMap D.site D.base D.base_mem X f
        (genericPoint D.site D.base D.base_mem hX.1 hintX) =
      genericPoint D.site D.base D.base_mem hY.1 hintY := by
  have hT0 : T0Space (points D.site D.base D.base_mem Y) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY)
  have hopen : IsOpen (Set.range (pointsMap D.site D.base D.base_mem X f)) :=
    isOpen_range_pointsMap_of_isEtale D.site D.base D.base_mem f hX.1 hY.1 hetale
  obtain ⟨x, hx⟩ : genericPoint D.site D.base D.base_mem hY.1 hintY ∈
      Set.range (pointsMap D.site D.base D.base_mem X f) :=
    ((isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY).mem_open_set_iff
      hopen).2 ⟨_, Set.mem_univ _,
        Set.mem_range_self (genericPoint D.site D.base D.base_mem hX.1 hintX)⟩
  have hspec : pointsMap D.site D.base D.base_mem X f
      (genericPoint D.site D.base D.base_mem hX.1 hintX) ⤳
      genericPoint D.site D.base D.base_mem hY.1 hintY :=
    hx ▸ ((isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hintX).specializes
      (Set.mem_univ x)).map (continuous_pointsMap D.site D.base D.base_mem f)
  refine IsGenericPoint.eq ?_ (isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY)
  refine subset_antisymm (Set.subset_univ _) ?_
  rw [← (isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY).def]
  exact hspec.closure_subset

include hbase hetale hintY in
/-- **Stacks 0EQ2, second paragraph, for an integral source.** An étale morphism `f : X ⟶ Y` of
good algebraic spaces over the base with `X` and `Y` integral and `dim_δ(Y) = n` has
`dim_δ(X) = n`.

Both δ-dimensions are the value of `δ` at a generic point, `|X|` and `|Y|` being irreducible,
and `f` is étale hence locally quasi-finite by Stacks 03XU, so the dimension function of
Situation 0EDT does not change along it; the generic point of `X` lies over the generic point of
`Y` by `AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_of_isEtale`. This is
`AlgebraicGeometry.Space.deltaDimensionClosed_univ_irreducibleComponentSubspace` with the
component taken to be the whole of `X`, which the inclusion of a component being an immersion is
no longer needed for. -/
theorem deltaDimensionClosed_univ_eq_of_isEtale
    (hintX : IsIntegralSpace D.site D.base D.base_mem X) {n : ℤ}
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) :
    deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt) := by
  have h2 := D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 f sY
    (isLocallyQuasiFinite_of_isEtale D.site D.base D.base_mem hY.1 hetale) hY.2.2
    (genericPoint D.site D.base D.base_mem hX.1 hintX)
  rw [hbase] at h2
  rw [deltaDimensionClosed_univ_eq_deltaValue_genericPoint D sX hX hintX, h2,
    pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY hintX,
    ← deltaDimensionClosed_univ_eq_deltaValue_genericPoint D sY hY hintY]
  exact hnY

include hbase hetale in
/-- **Every integral closed subspace of `X` is an irreducible component of the inverse image of
its image.** Let `f : X ⟶ Y` be an étale morphism of good algebraic spaces over the base and let
`T ⊆ X` be an integral closed subspace. Then `T` is an irreducible component of `f^{-1}(Z)` for
`Z ⊆ Y` the integral closed subspace on the closure of the image of `|T|`, which is the image of
`T` of Stacks 0EEG.

This is the surjectivity of
`AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponent`, the map whose injectivity is
`AlgebraicGeometry.Space.IntegralClosedSubspace.injective_preimageComponent`, and it is what
makes the coefficient computation of
`AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_preimageComponent` available
at *every* integral closed subspace of `X` rather than only at those presented as a component of
an inverse image.

Write `ξ` for the generic point of `|T|`, so that `|Z|` is the closure of `{f(ξ)}`. Some
irreducible component `C` of `f^{-1}(|Z|)` contains `ξ`; it is closed and irreducible in `|X|`,
hence has a generic point `w`, and `ξ` is a specialization of `w`. Then `f(w)` and `f(ξ)` are
specializations of one another — the first because `f` is continuous, the second because `f(w)`
lies in `|Z|` — so the dimension function `δ_{Y/B}` of Situation 0EDT, which drops strictly along
a nontrivial specialization, takes the same value at both. Since `f` is locally quasi-finite,
`δ_{X/B}` therefore takes the same value at `w` and at `ξ`, and the same strictness on `|X|`
forces `w = ξ`. So `C` is the closure of `{ξ}`, which is `|T|`, and an integral closed subspace
is determined by its point set by Stacks 0ENF. -/
theorem IntegralClosedSubspace.exists_eq_preimageComponent
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    ∃ (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
      (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)),
      Z.preimageComponent D.site D.base D.base_mem f hX.1
          (D.isDecentSpace_of_isGood sX hX) hY.1 C = T := by
  have hsoberX : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  set ξ := T.ambientGenericPoint D.site D.base D.base_mem with hξdef
  have hξ : IsGenericPoint ξ
      (subspacePointSet D.site D.base D.base_mem X T.subspace) :=
    T.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  -- the image of `T`, an integral closed subspace of `Y` with generic point `f ξ`
  set Z := T.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) f with hZdef
  have hZpts : subspacePointSet D.site D.base D.base_mem Y Z.subspace =
      closure {pointsMap D.site D.base D.base_mem X f ξ} := by
    rw [hZdef, T.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f, ← hξ.def]
    refine subset_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
    · exact (image_closure_subset_closure_image
        (continuous_pointsMap D.site D.base D.base_mem f)).trans
        (by rw [Set.image_singleton])
    · rw [← Set.image_singleton]
      exact Set.image_mono subset_closure
  -- `ξ` lies in the inverse image of `|Z|`
  have hξmem : ξ ∈ Z.preimagePointSet D.site D.base D.base_mem f := by
    rw [IntegralClosedSubspace.preimagePointSet, Set.mem_preimage, hZpts]
    exact subset_closure rfl
  -- an irreducible component of the inverse image through `ξ`
  obtain ⟨C, hC, hξC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({(⟨ξ, hξmem⟩ : Z.preimagePointSet D.site D.base D.base_mem f)} :
      Set (Z.preimagePointSet D.site D.base D.base_mem f)) isIrreducible_singleton
  have hCirr : IsIrreducible (Subtype.val '' C) := hC.1.image _ continuous_subtype_val.continuousOn
  have hCclosed : IsClosed (Subtype.val '' C) :=
    (Z.isClosed_preimagePointSet D.site D.base D.base_mem f
      hY.1).isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨w, hw⟩ := hsoberX.sober hCirr hCclosed
  -- the generic point of the component is `ξ`
  have hξmemC : ξ ∈ Subtype.val '' C := ⟨⟨ξ, hξmem⟩, hξC rfl, rfl⟩
  have hwξ : w ⤳ ξ := hw.specializes hξmemC
  have hfw : pointsMap D.site D.base D.base_mem X f w ⤳
      pointsMap D.site D.base D.base_mem X f ξ :=
    hwξ.map (continuous_pointsMap D.site D.base D.base_mem f)
  have hfξ : pointsMap D.site D.base D.base_mem X f ξ ⤳
      pointsMap D.site D.base D.base_mem X f w := by
    have hwC : w ∈ Subtype.val '' C := by
      rw [← hw.def]
      exact subset_closure rfl
    obtain ⟨⟨u, hu⟩, -, rfl⟩ := hwC
    refine IsGenericPoint.specializes rfl ?_
    rw [← hZpts]
    exact hu
  have hδY : D.deltaValue sY (pointsMap D.site D.base D.base_mem X f w) =
      D.deltaValue sY (pointsMap D.site D.base D.base_mem X f ξ) := by
    rw [← deltaDimensionFunction_apply D sY hY, ← deltaDimensionFunction_apply D sY hY]
    by_cases heq : pointsMap D.site D.base D.base_mem X f w =
        pointsMap D.site D.base D.base_mem X f ξ
    · rw [heq]
    · exact absurd ((deltaDimensionFunction D sY hY).strictAnti_specializes hfw heq)
        (not_lt.2 ((deltaDimensionFunction D sY hY).strictAnti_specializes hfξ
          (Ne.symm heq)).le)
  have hδX : D.deltaValue sX w = D.deltaValue sX ξ := by
    have hqf := isLocallyQuasiFinite_of_isEtale D.site D.base D.base_mem hY.1 hetale
    have h1 := D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 f sY hqf hY.2.2 w
    have h2 := D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 f sY hqf hY.2.2 ξ
    rw [hbase] at h1 h2
    rw [h1, h2, hδY]
  have hwξ' : w = ξ := by
    by_contra hne
    have hlt := (deltaDimensionFunction D sX hX).strictAnti_specializes hwξ hne
    rw [deltaDimensionFunction_apply D sX hX, deltaDimensionFunction_apply D sX hX, hδX] at hlt
    exact lt_irrefl _ hlt
  refine ⟨Z, ⟨C, hC⟩, ?_⟩
  refine eq_integralClosedSubspaceOfPoints D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) T (Z.preimageComponentPoints D.site D.base D.base_mem f
      hY.1 ⟨C, hC⟩) ?_ |>.symm
  change subspacePointSet D.site D.base D.base_mem X T.subspace = Subtype.val '' C
  rw [← hξ.def, ← hwξ', hw.def]

/-- The local finiteness of Stacks 0ENN on the integral target `Y`: the prime divisors of `Y`
along which `g` has nonzero order of vanishing, the order being taken at the canonical
embeddings of Stacks 0ENK, are locally finite in `|Y|`. -/
abbrev TargetDivisorLocallyFinite : Prop :=
  letI E := integralSpaceFractionEmbedding D sY hY hintY
  letI := E.nontrivial
  letI := E.isNoetherianRing
  letI := E.krullDimLE
  LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem Y =>
    if principalDivisorCoefficients D.site D.base D.base_mem hY.1 hintY.2.1 E.emb g
        (fun Q => hg.map (E.emb Q)) P = 0 then ∅
      else P.support D.site D.base D.base_mem Y

variable (hfinY : TargetDivisorLocallyFinite D sY hY hintY g hg) {n : ℤ}
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))

/-- **Stacks 0EQ1 on the integral target.** The principal divisor `div_Y(g)` of `g ∈ R(Y)^*` as
an element of `Z_{n-1}(Y)`, the order of vanishing being taken at the canonical embeddings
`R(Y) → Q(𝒪^h_{Y,ξ})` of Stacks 0ENK. -/
def targetPrincipalDivisorCycle : CycleGroup D sY (n - 1) :=
  letI E := integralSpaceFractionEmbedding D sY hY hintY
  letI := E.nontrivial
  letI := E.isNoetherianRing
  letI := E.krullDimLE
  principalDivisorCycle D sY hY hintY.2.1 E.emb g (fun Q => hg.map (E.emb Q)) hfinY hintY
    (deltaDimensionFunction D sY hY) (deltaDimensionFunction_apply D sY hY) hnY

/-- The left-hand side of Stacks 0EQ2: the étale pullback `f^*(div_Y(g))` of the principal
divisor of `g ∈ R(Y)^*`, as an element of `Z_{n-1}(X)`, read at the canonical embeddings
`R(Y) → Q(𝒪^h_{Y,ξ})` of Stacks 0ENK.

This is `AlgebraicGeometry.Space.etalePullbackCycleMap` applied to
`AlgebraicGeometry.Space.targetPrincipalDivisorCycle`. Étaleness of `f` is all that goes in: an
étale morphism is flat by Stacks 0467 and of relative dimension `0` by
`AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isEtale`, so the relative dimension is not
a hypothesis here. -/
def etalePullbackPrincipalDivisorCycleOfGood : CycleGroup D sX (n - 1) :=
  etalePullbackCycleMap D sX hX sY hY hbase hetale
    (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hetale) (n - 1)
    (targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY)

include hY in
/-- **Stacks 0ENF.** Two integral closed subspaces of `Y` with a common generic point are equal:
each point set is the closure of that point, and an integral closed subspace is determined by
its point set. -/
private theorem eq_of_isGenericPoint_subspacePointSet
    {Z W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    {ξ : points D.site D.base D.base_mem Y}
    (hZ : IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem Y Z.subspace))
    (hW : IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem Y W.subspace)) :
    Z = W :=
  injective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
    (IrreducibleCloseds.ext (hZ.symm.trans hW))

/-- The generic point of a component of the inverse image of `Z` is carried by an étale `f` to a
generic point of `|Z|`. -/
private theorem isGenericPoint_pointsMap_ambientGenericPoint_preimageComponent
    (hf : IsEtale D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :
    IsGenericPoint (pointsMap D.site D.base D.base_mem X f
      ((Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).ambientGenericPoint D.site D.base D.base_mem))
      (subspacePointSet D.site D.base D.base_mem Y Z.subspace) :=
  Z.isGenericPoint_pointsMap_of_isGenericPoint D sX hX sY hY hf C _
    ((Z.preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1 C).isGenericPoint_ambientGenericPoint
        D.site D.base D.base_mem hX.1)

/-- **Stacks 0EQ2, the coefficient of the left-hand side, from Stacks 0EPY.** The coefficient of
`f^*(div_Y(g))` at an irreducible component of the inverse image `f^{-1}(Z)` of an integral
closed subspace `Z ⊆ Y` is the coefficient `ord_Z(g)` of `div_Y(g)` at `Z` itself.

This is the source's sentence "observe that the coefficient of `Z` in `f^*div_Y(g)` is the same
integer, see Lemma 0EPY". The coefficient of a flat pullback is the sum over the integral closed
subspaces `W ⊆ Y` of the coefficient of `div_Y(g)` at `W` times the multiplicity of the
component in `f^{-1}(W)`
(`AlgebraicGeometry.Space.flatPullbackMap_apply`); Stacks 0EPY, in the form
`AlgebraicGeometry.Space.IntegralClosedSubspace.flatPullbackMult_eq_preimageComponentsCycle`,
identifies that multiplicity with the coefficient of the formal sum of the components of
`f^{-1}(W)`, which is one at `W = Z` and zero at every other `W`: a component of `f^{-1}(W)` has
its generic point carried by `f` to a generic point of `|W|`, so `W` is determined by the
component through Stacks 0ENF. -/
theorem etalePullbackPrincipalDivisorCycle_apply_preimageComponent
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :
    (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg hfinY hnY).1
        (Z.preimageComponent D.site D.base D.base_mem f hX.1
          (D.isDecentSpace_of_isGood sX hX) hY.1 C) =
      (targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY).1 Z := by
  classical
  set hflat := isFlat_of_isEtale D.site D.base D.base_mem hetale with hflatdef
  set hr := hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hetale with hrdef
  set α := targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY with hαdef
  have hsum : (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg
        hfinY hnY).1
        (Z.preimageComponent D.site D.base D.base_mem f hX.1
          (D.isDecentSpace_of_isGood sX hX) hY.1 C) =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
        α.1 W * flatPullbackMult D sX hX sY hY f hbase 0 hflat hr W
          (Z.preimageComponent D.site D.base D.base_mem f hX.1
            (D.isDecentSpace_of_isGood sX hX) hY.1 C) := rfl
  have hmem : Z.preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1 C ∈
      {V : IntegralClosedSubspace D.site D.base D.base_mem X |
        ∃ C, Z.preimageComponent D.site D.base D.base_mem f hX.1
          (D.isDecentSpace_of_isGood sX hX) hY.1 C = V} := ⟨C, rfl⟩
  have hone : flatPullbackMult D sX hX sY hY f hbase 0 hflat hr Z
      (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C) = 1 := by
    rw [hflatdef, hrdef, Z.flatPullbackMult_eq_preimageComponentsCycle D sX hX sY hY hetale hbase,
      IntegralClosedSubspace.preimageComponentsCycle, Set.indicator_of_mem hmem, Pi.one_apply]
  rw [hsum, finsum_eq_single _ Z ?_, hone, mul_one]
  intro W hWZ
  have hzero : flatPullbackMult D sX hX sY hY f hbase 0 hflat hr W
      (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C) = 0 := by
    rw [hflatdef, hrdef, W.flatPullbackMult_eq_preimageComponentsCycle D sX hX sY hY hetale hbase]
    by_contra hne
    obtain ⟨C', hC'⟩ := (W.preimageComponentsCycle_ne_zero_iff D sX hX sY hY f _).1 hne
    have h1 := isGenericPoint_pointsMap_ambientGenericPoint_preimageComponent D sX hX sY hY hetale
      W C'
    rw [hC'] at h1
    have h2 := isGenericPoint_pointsMap_ambientGenericPoint_preimageComponent D sX hX sY hY hetale
      Z C
    exact hWZ (eq_of_isGenericPoint_subspacePointSet D sY hY h1 h2)
  rw [hzero, mul_zero]

/-- **The left-hand side of Stacks 0EQ2, at an arbitrary `X`.** The coefficient of
`f^*(div_Y(g))` at *any* integral closed subspace `Z ⊆ X` is the coefficient `ord_{Z'}(g)` of
`div_Y(g)` at the image `Z' ⊆ Y` of `Z`, the integral closed subspace on the closure of the image
of `|Z|` (Stacks 0EEG). Nothing is assumed of `X` beyond the source's hypotheses: in particular
`X` is not assumed integral and `Z` is not assumed of δ-dimension `n - 1`.

This is the source's sentence "observe that the coefficient of `Z` in `f^*div_Y(g)` is the same
integer, see Lemma 0EPY", stated at every `Z` at once. Every integral closed subspace of `X` is
an irreducible component of the inverse image of its image
(`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_eq_preimageComponent`), so
`AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_preimageComponent` computes the
coefficient there; the integral closed subspace of `Y` it produces is the image of `Z`, both
having the image of the generic point of `Z` as generic point (Stacks 0ENF). -/
theorem etalePullbackPrincipalDivisorCycle_apply_eq_apply_closureImage
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg hfinY hnY).1 Z =
      (targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY).1
        (Z.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f) := by
  obtain ⟨Z', C, hZC⟩ := IntegralClosedSubspace.exists_eq_preimageComponent D sX hX sY hY hbase
    hetale Z
  subst hZC
  set T := Z'.preimageComponent D.site D.base D.base_mem f hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1 C with hTdef
  rw [etalePullbackPrincipalDivisorCycle_apply_preimageComponent D sX hX sY hY hbase hetale
    hintY g hg hfinY hnY Z' C]
  refine congrArg _ (eq_of_isGenericPoint_subspacePointSet D sY hY
    (isGenericPoint_pointsMap_ambientGenericPoint_preimageComponent D sX hX sY hY hetale Z' C) ?_)
  rw [← T.ambientGenericPoint_closureImage D hX.1 hY.1 (D.isDecentSpace_of_isGood sY hY) f]
  exact (T.closureImage D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) f).isGenericPoint_ambientGenericPoint
      D.site D.base D.base_mem hY.1

/-- **Stacks 0EQ2, reduced to one identity of orders of vanishing, and with no data on the
components assumed.** In Situation 0EDT let `f : X ⟶ Y` be an étale morphism of good algebraic
spaces over `B`, let `Y` be integral with `dim_δ(Y) = n` and let `g ∈ R(Y)^*`. Then the identity
of cycles on `X`

`f^*(div_Y(g)) = ∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`,

read coefficientwise over the irreducible components `X'` of `X` (Remark 0EE8), holds **if and
only if** at every integral closed subspace `Z ⊆ X` of δ-dimension `n - 1`

`∑_{X'} ord_Z(g ∘ f|_{X'}) = ord_{Z'}(g)`,

`Z'` being the image of `Z` in `Y`. That one identity of integers — the last step of the source's
third to sixth paragraphs — is the whole of what is left.

Nothing about the components is assumed: the right-hand side is formed through
`AlgebraicGeometry.Space.etaleComponentDivisorData`, whose only input is the local finiteness of
Stacks 0ENN on each component, which is what makes `div_{X'}(g ∘ f|_{X'})` a cycle at all and
which Stacks 0EQ1 takes in the same form on `Y`. In particular the dominance of `f|_{X'}` is
proved, not assumed
(`AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`).

Two reductions are combined. Away from δ-dimension `n - 1` both sides vanish, both being
`(n-1)`-cycles — on the right because every component has `dim_δ(X') = n`, the source's second
paragraph, which is proved — the reduction of
`AlgebraicGeometry.Space.etalePullback_principalDivisorCycle_eq_sum_components_iff`, taken here
at the canonical embeddings and hence re-run rather than cited. At
δ-dimension `n - 1` the left-hand side is `ord_{Z'}(g)`, which is Lemma 0EPY in the form
`AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_eq_apply_closureImage`,
and that holds for an arbitrary `X`, not only an integral one. -/
@[stacks 0EQ2 "REDUCED to ONE identity of integers, with NOTHING about the components assumed.
  The displayed equality of cycles on X — coefficientwise, the sum over the irreducible components
  of X — HOLDS IF AND ONLY IF at every integral closed subspace Z of X of δ-dimension n-1 the sum
  over the components X' of ord_Z(g ∘ f|_{X'}), computed on X', equals ord_{Z'}(g) for Z' the
  image of Z in Y. This is that equivalence. Proved here, in both halves: away from δ-dimension
  n-1 both sides vanish, both being (n-1)-cycles, which on the right uses dim_δ(X') = n for every
  component (the source's second paragraph, PROVED in
  deltaDimensionClosed_univ_irreducibleComponentSubspace); and at δ-dimension n-1 the coefficient
  of the left side is ord_{Z'}(g) by Lemma 0EPY, for an ARBITRARY X, which is
  etalePullbackPrincipalDivisorCycle_apply_eq_apply_closureImage together
  with IntegralClosedSubspace.exists_eq_preimageComponent. The right side is formed through
  etaleComponentDivisorData, so the dominance of f restricted to a component — the source's first
  step, what makes g ∘ f|_{X'} defined, and formerly a field of EtaleComponentDivisorDataOfGood — is
  PROVED, in pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace: an étale
  morphism is flat, so generizations lift along |X| → |Y|, and a continuous generalizing map into
  a quasi-sober space carries the generic point of an irreducible component to the generic point
  of one, which for the irreducible |Y| is its generic point. The source's own route, openness of
  |f| plus local finiteness of the components, is not needed. The only input beyond the source's
  hypotheses is ComponentDivisorLocallyFinite, which is Stacks 0ENN on each component and is what
  makes div_{X'}(g ∘ f|_{X'}) a cycle at all; Stacks 0EQ1 takes it in the same shape on Y
  (TargetDivisorLocallyFinite) and this repository proves it from a nonempty open subset over
  which the function is invertible (locallyFinite_principalDivisorCoefficients_ne_zero). For X
  INTEGRAL the remaining identity of integers is PROVED and with it the whole of the source's
  displayed identity, which then reads f^* div_Y(g) = div_X(g ∘ f) in Z_{n-1}(X):
  etalePullbackPrincipalDivisorCycle_eq_principalDivisorCycle_of_isIntegralSpace, coefficientwise
  etalePullbackPrincipalDivisorCycle_apply_of_isIntegralSpace, through
  ord_rationalFunctionMap_eq_ord_of_isEtale. WHAT IS STILL MISSING, for an X with several
  components, is exactly the right-hand side of this equivalence, and it is the source's grouping
  of the branches at the generic point of Z over the components through it: ord_Z(g ∘ f|_{X'}) has
  to be identified with the sum of Ring.minimalPrimeOrd over the minimal primes 𝔭 of the local
  ring of an affine étale chart W of X at a point over the generic point of Z with
  componentOfBranch 𝔭 = X'. The partition itself is available
  (finsum_flatBranch_eq_finsum_component_finsum_flatBranch), the chart reading of g ∘ f|_{X'} is
  available with no flatness of f|_{X'}
  (rationalFunctionsToTotalFractionRing_rationalFunctionMap_componentChart,
  nonZeroDivisors_le_comap_chartGlobalSectionsRestrict), and the components of W ×_X X' are
  components of W (mem_irreducibleComponents_image_closedSubspaceBaseChangeChartProj), in the
  stalk-level form comap_stalkMap_closedSubspaceBaseChangeChartProj_mem_minimalPrimes; and the
  transport of Ring.minimalPrimeOrd along the surjection of local rings
  𝒪_{W,w} → 𝒪_{W ×_X X', w'} is Ring.minimalPrimeOrd_map_of_surjective. So the grouping of the
  branches over the components is now proved, as
  finsum_minimalPrimeOrd_stalkMap_eq_finsum_branch_on_component, and so is the recognition of its
  left-hand side as ord_Z(g ∘ f|_{X'}): ord_rationalFunctionMap_eq_finsum_branch_on_component,
  through the stalk-level chart reading
  chartPointRationalFunctionMap_rationalFunctionMap_componentChart, which composes the two halves,
  rationalFunctionsToTotalFractionRing_rationalFunctionMap_componentChart on global sections and
  Scheme.totalFractionRingToStalkFractionRing_map_appTop from global sections to the local ring.
  The sum over ALL the branches of 𝒪_{W,w} is ord_{Z'}(g) on Y, with the same element of
  Q(𝒪_{W,w}): PrimeDivisor.ord_eq_finsum_minimalPrimeOrd_etaleChartComp. So the whole grouping of
  the branches, the content of the source's third to sixth paragraphs, is proved. The coefficient
  of the pushforward along the inclusion of a component is proved too, in
  componentDivisorPushforward_apply_pushforward and _apply_of_forall_ne, through
  properCyclePushforward_ι_eq_integralClosedSubspacePushforward: the inclusion of an irreducible
  component is the inclusion of an integral closed subspace, so the pushforward of Stacks 0EP1
  along it is integralClosedSubspacePushforward, whose coefficients are the extension by zero of
  the coefficients on the component. WHAT NO DECLARATION PROVIDES is the CONVERSE presentation —
  that an integral closed subspace Z of X whose points lie in |X'| is the image of an integral
  closed subspace of X', of δ-dimension making it a prime divisor of X' — which is what cuts
  componentPushforwardCoeff Z, a sum over ALL the components, down to the components through the
  generic point of Z and matches each term with ord_{Z ∩ X'}(g ∘ f|_{X'}); nor is the partition of
  the minimal primes of 𝒪_{W,w} over those components
  (finsum_flatBranch_eq_finsum_component_finsum_flatBranch) joined to the two sums above"]
theorem etalePullback_principalDivisorCycle_eq_sum_components_iff_eq_ord_closureImage
    (hfin : ComponentDivisorLocallyFinite D sX hX sY hY hetale hintY g hg) :
    (∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg
            hfinY hnY).1 Z =
          (etaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g hg
            hfin).toEtaleComponentDivisorData.componentPushforwardCoeff Z) ↔
      ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        deltaDimension D sX Z = n - 1 →
          (etaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g hg
              hfin).toEtaleComponentDivisorData.componentPushforwardCoeff Z =
            (targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY).1
              (Z.closureImage D.site D.base D.base_mem hY.1
                (D.isDecentSpace_of_isGood sY hY) f) := by
  refine ⟨fun h Z _ => ?_, fun h Z => ?_⟩
  · rw [← h Z, etalePullbackPrincipalDivisorCycle_apply_eq_apply_closureImage
      D sX hX sY hY hbase hetale hintY g hg hfinY hnY Z]
  · by_cases hZ : deltaDimension D sX Z = n - 1
    · rw [etalePullbackPrincipalDivisorCycle_apply_eq_apply_closureImage
        D sX hX sY hY hbase hetale hintY g hg hfinY hnY Z, h Z hZ]
    · rw [(etaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g hg
        hfin).toEtaleComponentDivisorData.componentPushforwardCoeff_eq_zero hZ]
      by_contra hne
      exact hZ ((etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg
        hfinY hnY).2.2 Z hne)

/-! ### Stacks 0EQ2 for an integral source -/

/-- The local finiteness of Stacks 0ENN on an integral source `X`, for the pullback
`g ∘ f ∈ R(X)^*` of `g`: the prime divisors of `X` along which `g ∘ f` has nonzero order of
vanishing, the order being taken at the canonical embeddings of Stacks 0ENK, are locally finite
in `|X|`.

This is `AlgebraicGeometry.Space.TargetDivisorLocallyFinite` on `X` and `g ∘ f`, and it is what
makes `div_X(g ∘ f)` an element of `Z_{n-1}(X)`; Stacks 0EQ1 takes it in exactly this form, and
`AlgebraicGeometry.Space.locallyFinite_principalDivisorCoefficients_ne_zero` discharges it from a
nonempty open subset of `|X|` over which `g ∘ f` is invertible. -/
abbrev PullbackDivisorLocallyFinite
    (hintX : IsIntegralSpace D.site D.base D.base_mem X) : Prop :=
  letI E := integralSpaceFractionEmbedding D sX hX hintX
  letI := E.nontrivial
  letI := E.isNoetherianRing
  letI := E.krullDimLE
  LocallyFinite fun P : PrimeDivisor D.site D.base D.base_mem X =>
    if principalDivisorCoefficients D.site D.base D.base_mem hX.1 hintX.2.1 E.emb
          (rationalFunctionMap D.site D.base D.base_mem hX.1 hY.1 hintX hintY f
            (pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY hintX)
            g)
          (fun Q => (hg.map (rationalFunctionMap D.site D.base D.base_mem hX.1 hY.1 hintX hintY f
            (pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY
              hintX))).map (E.emb Q)) P = 0 then ∅
      else P.support D.site D.base D.base_mem X

/-- **Stacks 0EQ2 for an integral source, coefficientwise.** In Situation 0EDT let `f : X ⟶ Y` be
an étale morphism of good algebraic spaces over `B`, let `X` and `Y` be integral with
`dim_δ(Y) = n` and let `g ∈ R(Y)^*`. Then at every integral closed subspace `Z ⊆ X`

`f^*(div_Y(g))` and `div_X(g ∘ f)` have the same coefficient,

both sides being formed at the canonical embeddings of Stacks 0ENK — on `Y` for `g` and on `X`
for its pullback `g ∘ f` under `AlgebraicGeometry.Space.rationalFunctionMap`.

For `X` integral this is the displayed identity of the source read coefficientwise: `X` has
exactly one irreducible component, namely `X` itself, the morphism `X' ⟶ X` of the source's sum
is the identity and `g ∘ f|_{X'}` is `g ∘ f`, so the right-hand side
`∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})` is `div_X(g ∘ f)`.

Away from the integral closed subspaces of δ-dimension `n - 1` both coefficients vanish, both
sides being `(n-1)`-cycles — on the right because a subspace of another δ-dimension is not a
prime divisor, by Stacks 0EPZ, and `dim_δ(X) = n` by
`AlgebraicGeometry.Space.deltaDimensionClosed_univ_eq_of_isEtale`. At an integral closed subspace
`Z` of δ-dimension `n - 1` the two coefficients are orders of vanishing along prime divisors, and
the identity is the two halves of the source's argument:

* `Z` is an irreducible component of `f^{-1}(Z')` for `Z'` its image in `Y`
  (`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_eq_preimageComponent`), so the
  coefficient of the left-hand side at `Z` is `ord_{Z'}(g)` by Stacks 0EPY, which is
  `AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_preimageComponent`;
* `ord_Z(g ∘ f) = ord_{Z'}(g)`, which is
  `AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_ord_of_isEtale`: both orders of vanishing
  are computed on one affine étale chart of `X` through the generic point of `Z`, which is also a
  chart of `Y` through the generic point of `Z'` because `f` is étale.

The second replaces the source's steps three to six — the square of henselian local rings of
Remark 0EPL, the length equality of Lemma 02M1 and the length decomposition of Lemma 02QG — whose
purpose there is to produce the multiplicity one of `Z` over `Z'`, and which are only needed in
that form when the branches at the generic point have to be grouped over several components. -/
theorem etalePullbackPrincipalDivisorCycle_apply_of_isIntegralSpace
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    letI E := integralSpaceFractionEmbedding D sX hX hintX
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg hfinY hnY).1 T =
      principalDivisorCycleCoefficients D sX hX hintX.2.1 E.emb
        (rationalFunctionMap D.site D.base D.base_mem hX.1 hY.1 hintX hintY f
          (pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY hintX) g)
        (fun Q => (hg.map (rationalFunctionMap D.site D.base D.base_mem hX.1 hY.1 hintX hintY f
          (pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY
            hintX))).map (E.emb Q)) T := by
  let EY := integralSpaceFractionEmbedding D sY hY hintY
  let := EY.nontrivial
  let := EY.isNoetherianRing
  let := EY.krullDimLE
  let EX := integralSpaceFractionEmbedding D sX hX hintX
  let := EX.nontrivial
  let := EX.isNoetherianRing
  let := EX.krullDimLE
  have hnX := deltaDimensionClosed_univ_eq_of_isEtale D sX hX sY hY hbase hetale hintY hintX hnY
  by_cases hdim : deltaDimension D sX T = n - 1
  · have hcodT : codimension
        (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 T) = 1 :=
      ((isPrimeDivisor_tfae_of_isIntegralSpace' D sX hX hintX hnX T).out 3 2).mp hdim
    obtain ⟨Z, C, hZC⟩ := IntegralClosedSubspace.exists_eq_preimageComponent D sX hX sY hY hbase
      hetale T
    have hdimZ : deltaDimension D sY Z = n - 1 := by
      rw [← hdim, ← hZC]
      exact (Z.deltaDimension_preimageComponent D sX hX sY hY hetale hbase C).symm
    have hcodZ : codimension
        (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z) = 1 :=
      ((isPrimeDivisor_tfae_of_isIntegralSpace' D sY hY hintY hnY Z).out 3 2).mp hdimZ
    have hLHS : (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg
          hfinY hnY).1 T =
        (targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY).1 Z := by
      rw [← hZC]
      exact etalePullbackPrincipalDivisorCycle_apply_preimageComponent D sX hX sY hY hbase hetale
        hintY g hg hfinY hnY Z C
    -- the generic point of `Z` lies over the generic point of its image
    have hgenT : pointsMap D.site D.base D.base_mem X f
        (T.ambientGenericPoint D.site D.base D.base_mem) =
        Z.ambientGenericPoint D.site D.base D.base_mem :=
      eq_pointsMap_genericPoint_of_isGenericPoint D.site D.base D.base_mem hY.1 Z _
        (hZC ▸ isGenericPoint_pointsMap_ambientGenericPoint_preimageComponent D sX hX sY hY hetale
          Z C)
    have hPT : (T.toPrimeDivisor D.site D.base D.base_mem hX.1 hcodT).genericPoint
          D.site D.base D.base_mem X =
        T.ambientGenericPoint D.site D.base D.base_mem :=
      eq_pointsMap_genericPoint_of_isGenericPoint D.site D.base D.base_mem hX.1 T _
        ((T.toPrimeDivisor D.site D.base D.base_mem hX.1 hcodT).isGenericPoint_genericPoint
          D.site D.base D.base_mem X)
    have hQZ : (Z.toPrimeDivisor D.site D.base D.base_mem hY.1 hcodZ).genericPoint
          D.site D.base D.base_mem Y =
        Z.ambientGenericPoint D.site D.base D.base_mem :=
      eq_pointsMap_genericPoint_of_isGenericPoint D.site D.base D.base_mem hY.1 Z _
        ((Z.toPrimeDivisor D.site D.base D.base_mem hY.1 hcodZ).isGenericPoint_genericPoint
          D.site D.base D.base_mem Y)
    have hord := ord_rationalFunctionMap_eq_ord_of_isEtale D.site D.base D.base_mem hX.1 hY.1
      hintX.2.1 hintY.2.1 hintX hintY
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) hetale
      (pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY hintX)
      (T.toPrimeDivisor D.site D.base D.base_mem hX.1 hcodT)
      (Z.toPrimeDivisor D.site D.base D.base_mem hY.1 hcodZ)
      (by rw [hPT, hQZ, hgenT]) hg.unit
    rw [hLHS, show (targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY).1 Z =
        principalDivisorCycleCoefficients D sY hY hintY.2.1
          (integralSpaceFractionEmbedding D sY hY hintY).emb g
          (fun Q => hg.map ((integralSpaceFractionEmbedding D sY hY hintY).emb Q)) Z from rfl,
      principalDivisorCycleCoefficients, principalDivisorCycleCoefficients, dite_eq_left hcodZ,
      dite_eq_left hcodT]
    exact hord.symm
  · have hcodT : codimension
        (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 T) ≠ 1 := fun hcod =>
      hdim (((isPrimeDivisor_tfae_of_isIntegralSpace' D sX hX hintX hnX T).out 2 3).mp hcod)
    rw [principalDivisorCycleCoefficients_of_codimension_ne_one D sX hX hintX.2.1 _ _ _ hcodT]
    by_contra hne
    exact hdim ((etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg
      hfinY hnY).2.2 T hne)

/-- **Stacks 0EQ2 for an integral source.** In Situation 0EDT let `f : X ⟶ Y` be an étale
morphism of good algebraic spaces over `B`, let `X` and `Y` be integral with `dim_δ(Y) = n` and
let `g ∈ R(Y)^*`. Then, in `Z_{n-1}(X)`,

`f^*(div_Y(g)) = div_X(g ∘ f)`,

which is the identity of the source when `X` is integral: the sum over the irreducible components
`X'` of `X` has the single term `X' = X`, the morphism `X' ⟶ X` is the identity and
`g ∘ f|_{X'}` is `g ∘ f`.

This is
`AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_of_isIntegralSpace` read in the
group of cycles rather than coefficientwise. What the right-hand side takes beyond the source's
hypotheses is the local finiteness of Stacks 0ENN for `g ∘ f`, which is what makes `div_X(g ∘ f)`
a cycle at all and which Stacks 0EQ1 takes in the same way on the target
(`AlgebraicGeometry.Space.TargetDivisorLocallyFinite`); `dim_δ(X) = n` is proved, not assumed. -/
theorem etalePullbackPrincipalDivisorCycle_eq_principalDivisorCycle_of_isIntegralSpace
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hfinX : PullbackDivisorLocallyFinite D sX hX sY hY hetale hintY g hg hintX) :
    letI E := integralSpaceFractionEmbedding D sX hX hintX
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg hfinY hnY =
      principalDivisorCycle D sX hX hintX.2.1 E.emb
        (rationalFunctionMap D.site D.base D.base_mem hX.1 hY.1 hintX hintY f
          (pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY hintX) g)
        (fun Q => (hg.map (rationalFunctionMap D.site D.base D.base_mem hX.1 hY.1 hintX hintY f
          (pointsMap_genericPoint_eq_genericPoint_of_isEtale D sX hX sY hY hetale hintY
            hintX))).map (E.emb Q)) hfinX hintX (deltaDimensionFunction D sX hX)
        (deltaDimensionFunction_apply D sX hX)
        (deltaDimensionClosed_univ_eq_of_isEtale D sX hX sY hY hbase hetale hintY hintX hnY) :=
  Subtype.ext (funext fun T =>
    etalePullbackPrincipalDivisorCycle_apply_of_isIntegralSpace D sX hX sY hY hbase hetale hintY
      g hg hfinY hnY hintX T)

end Identity

end AlgebraicGeometry.Space

end
