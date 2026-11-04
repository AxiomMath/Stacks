module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentPushforwardOrdJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisorComponents

/-!
# Stacks 0EQ2

In Situation 0EDT let `f : X ⟶ Y` be an étale morphism of good algebraic spaces over `B`, let `Y`
be integral with `dim_δ(Y) = n` and let `g ∈ R(Y)^*`. This file proves the identity of cycles on
`X`

`f^*(div_Y(g)) = ∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`,

the sum being over the irreducible components `X'` of `X` (Remark 0EE8), read coefficientwise
because that family is only locally finite.

The two reductions of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor` leave exactly one
identity of integers, `∑_{X'} ord_{Z ∩ X'}(g ∘ f|_{X'}) = ord_{Z'}(g)` at an integral closed
subspace `Z ⊆ X` of δ-dimension `n - 1`;
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood.componentPushforwardCoeff_eq_ord_of_chart`
proves it on an étale chart of `X` through the generic point of `Z`, and what is done here is to
produce that chart and to recognise the right-hand side as a coefficient of `div_Y(g)`.

## Main results

* `EtaleComponentDivisorDataOfGood.componentPushforwardCoeff_eq_apply_closureImage`:
  the coefficient identity, with the chart discharged.
* `AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_eq_componentPushforwardCoeff`:
  **Stacks 0EQ2**, the displayed identity read coefficientwise.

## Implementation notes

**The chart.** `AlgebraicGeometry.Space.exists_affine_etale_chart_at_point` gives an affine étale
chart `W` of `X` through the generic point `ξ` of `Z`. The remaining properties are read off the
two sides: local Noetherianity of the chart scheme and of its local ring at `w` from goodness of
`X` over the base, reducedness from integrality of `Y` because `W` is also a chart of `Y` (`f`
being étale), and Krull dimension at most one of that local ring from `Z'` being a prime divisor
of `Y` — `AlgebraicGeometry.Space.PrimeDivisor.krullDimLE_chartStalk`, which asks nothing of
`X`. So no hypothesis on `X` beyond the source's own is used, and in particular `X` is not
assumed integral or reduced.

**The image of `Z`.** `Z'` is the integral closed subspace of `Y` on the closure of the image of
`|Z|` (Stacks 0EEG), which is a prime divisor of `Y` because its δ-dimension is that of `Z`: the
dimension function of Situation 0EDT does not change along the locally quasi-finite `f`
(Stacks 03XU), and the generic point of the image is the image of the generic point
(`AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint_closureImage_eq`).

**The restrictions `Z ∩ X'`.** They are produced by
`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq_of_ambientGenericPoint_mem`
and chosen with `Exists.choose`; the choice is harmless because the subspace of a component whose
image is `Z` is unique
(`AlgebraicGeometry.Space.IntegralClosedSubspace.injective_pushforward`).

**Notes in the base that this file makes stale.** The two `@[stacks 0EQ2]` registrations in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor` say "REDUCED for an X
with several irreducible components" and "WHAT IS STILL MISSING, for an X with several
components, is exactly the right-hand side of this equivalence"; the implementation note of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentDivisorPushforwardCoefficient` says that the
converse presentation of an integral closed subspace inside a component, "together with the
δ-dimension bookkeeping", "is not in this repository". All three are now false: the presentation
is `AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq` and the bookkeeping is
`AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_pushforward`, both already in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps`, and the identity those
notes call missing is
`AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_eq_componentPushforwardCoeff`
below. Those files are not edited here; the correction is recorded in this docstring.

## References

* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace EtaleComponentDivisorDataOfGood

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {f : X ⟶ Y} {hbase : f ≫ sY = sX} {hetale : IsEtale D.site D.base D.base_mem f}
    {hintY : IsIntegralSpace D.site D.base D.base_mem Y} {n : ℤ}
    {hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)}
    {g : rationalFunctions D.site D.base D.base_mem hY.1} {hg : IsUnit g}
    (data : EtaleComponentDivisorDataOfGood D sX hX sY hY f hbase hetale hintY n hnY g hg)

include data hbase in
/-- **The coefficient identity of Stacks 0EQ2.** At an integral closed subspace `Z ⊆ X` of
δ-dimension `n - 1`, the coefficient at `Z` of `∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})` is the
coefficient of `div_Y(g)` at the image `Z'` of `Z` in `Y` (Stacks 0EEG).

This is
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood.componentPushforwardCoeff_eq_ord_of_chart`
with its chart produced and its right-hand side read as a coefficient of `div_Y(g)`. -/
theorem componentPushforwardCoeff_eq_apply_closureImage
    (hfinY : TargetDivisorLocallyFinite D sY hY hintY g hg)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hdimZ : deltaDimension D sX Z = n - 1) :
    data.toEtaleComponentDivisorData.componentPushforwardCoeff Z =
      (targetPrincipalDivisorCycle D sY hY hintY g hg hfinY hnY).1
        (Z.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f) := by
  classical
  have hdecY := D.isDecentSpace_of_isGood sY hY
  set ξ := Z.ambientGenericPoint D.site D.base D.base_mem with hξdef
  set ZY := Z.closureImage D.site D.base D.base_mem hY.1
    hdecY f with hZYdef
  -- the generic point of the image of `Z` is the image of `ξ`
  have hgenZY : ZY.ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem X f ξ :=
    IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem hX.1
      hY.1 hdecY f Z
  -- the image has δ-dimension `n - 1`, so it is a prime divisor of `Y`
  have hdimZY : deltaDimension D sY ZY = n - 1 := by
    have h1 := deltaDimension_eq_of_isGenericPoint D sY hY.1 ZY
      (ZY.ambientGenericPoint D.site D.base D.base_mem)
      (ZY.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1)
    have h2 := D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 f sY
      (isLocallyQuasiFinite_of_isEtale D.site D.base D.base_mem hY.1 hetale) hY.2.2 ξ
    rw [hbase] at h2
    have h3 := deltaDimension_eq_of_isGenericPoint D sX hX.1 Z ξ
      (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1)
    rw [h1, hgenZY, ← h2, ← h3, hdimZ]
  have hcodZY : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 ZY)
      = 1 :=
    ((isPrimeDivisor_tfae_of_isIntegralSpace' D sY hY hintY hnY ZY).out 3 2).mp hdimZY
  set Z' := ZY.toPrimeDivisor D.site D.base D.base_mem hY.1 hcodZY with hZ'def
  -- the generic point of that prime divisor is the image of `ξ`
  have : T0Space (points D.site D.base D.base_mem Y) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1
      hdecY
  have hgenP : Z'.genericPoint D.site D.base D.base_mem Y =
      pointsMap D.site D.base D.base_mem X f ξ := by
    rw [← hgenZY]
    exact IsGenericPoint.eq (Z'.isGenericPoint_genericPoint D.site D.base D.base_mem Y)
      (ZY.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1)
  -- an affine étale chart of `X` through `ξ`
  obtain ⟨Wobj, b, hWaff, hbet, w0, hw0⟩ := exists_affine_etale_chart_at_point D.site D.base
    D.base_mem X hX.1 ξ
  set W : SmallEtale D.site D.base D.base_mem X := ⟨CostructuredArrow.mk b, hbet⟩ with hWdef
  have : IsAffine (chartScheme W) := hWaff
  have : IsAffine W.obj.left.left.1 := hWaff
  have hNW : IsLocallyNoetherian (chartScheme W) :=
    isLocallyNoetherian_chartScheme_of_isGood D sX hX W
  have : IsLocallyNoetherian W.obj.left.left.1 := hNW
  have hredY : IsReduced
      (chartScheme (etaleChartComp D.site D.base D.base_mem hetale W)) :=
    isReduced_chartScheme_of_isIntegralSpace hY.1 hintY _
  have : IsReduced W.obj.left.left.1 := hredY
  have : IsAffine (etaleChartComp D.site D.base D.base_mem hetale W).obj.left.left.1 := hWaff
  have : IsReduced (etaleChartComp D.site D.base D.base_mem hetale W).obj.left.left.1 := hredY
  have : IsLocallyNoetherian
      (etaleChartComp D.site D.base D.base_mem hetale W).obj.left.left.1 := hNW
  -- the point of the chart over `ξ`
  set w : chartScheme W := pointsEquivScheme D.site D.base D.base_mem Wobj w0 with hwdef
  have hw : chartSchemeToPoints D.site D.base D.base_mem X W w = ξ := by
    rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm D.site D.base D.base_mem X W w]
    exact (congrArg (pointsMap D.site D.base D.base_mem (yoneda.obj Wobj) b)
      ((pointsEquivScheme D.site D.base D.base_mem Wobj).symm_apply_apply w0)).trans hw0
  have hZ'chart : chartSchemeToPoints D.site D.base D.base_mem Y
      (etaleChartComp D.site D.base D.base_mem hetale W) w =
      Z'.genericPoint D.site D.base D.base_mem Y := by
    rw [chartSchemeToPoints_etaleChartComp D.site D.base D.base_mem hetale W w, hw, hgenP]
  have : IsNoetherianRing ((chartScheme W).presheaf.stalk w) :=
    isNoetherianRing_stalk_chartScheme_of_isGood D sX hX W w
  have : Ring.KrullDimLE 1 ((chartScheme W).presheaf.stalk w) :=
    Z'.krullDimLE_chartStalk D.site D.base D.base_mem hY.1 hdecY
      (etaleChartComp D.site D.base D.base_mem hetale W) w hZ'chart
  -- the subspace of each component through `ξ` whose image is `Z`
  have hex : ∀ V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      ξ ∈ subspacePointSet D.site D.base D.base_mem X V.1.subspace →
      ∃ Z'' : IntegralClosedSubspace D.site D.base D.base_mem V.1.subspace.toFunctor,
        IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          V.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) V.1.isClosedSubspace.2
          Z'' = Z := fun V hV =>
    IntegralClosedSubspace.exists_pushforward_eq_of_ambientGenericPoint_mem D.site D.base
      D.base_mem hX.1 (D.isDecentSpace_of_isGood sX hX) V.1 Z hV
  rw [data.componentPushforwardCoeff_eq_ord_of_chart Z hdimZ
    (fun V hV => (hex V hV).choose) (fun V hV => (hex V hV).choose_spec) W w hw Z' hZ'chart]
  -- the coefficient of `div_Y(g)` at the image
  let E := integralSpaceFractionEmbedding D sY hY hintY
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  have key := principalDivisorCycleCoefficients_toIntegralClosedSubspace D sY hY hintY.2.1
    E.emb g (fun Q => hg.map (E.emb Q)) Z'
  rw [IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor D.site D.base D.base_mem
    hY.1 ZY hcodZY] at key
  exact key.symm

end EtaleComponentDivisorDataOfGood

/-! ### The local finiteness of Stacks 0ENN, discharged -/

/-- **Stacks 0ENN on the integral target.** The prime divisors of `Y` along which `g ∈ R(Y)^*`
has nonzero order of vanishing, the order being taken at the canonical embeddings of
Stacks 0ENK, are locally finite in `|Y|`.

Nothing is assumed: `Y` is integral and, being good over the locally Noetherian base, has the
étale-local Noetherian property
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isGood`), which are
exactly the hypotheses of Stacks 0ENN in the form
`AlgebraicGeometry.Space.ordRationalFunction_mem_weilDivisor`. -/
theorem targetDivisorLocallyFinite_of_isGood (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g) :
    TargetDivisorLocallyFinite D sY hY hintY g hg :=
  ordRationalFunction_mem_weilDivisor D.site D.base D.base_mem hY.1 hintY
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) hg.unit

/-- **Stacks 0ENN on each irreducible component of `X`.** The prime divisors of an irreducible
component `X' ⊆ X` along which `g ∘ f|_{X'}` has nonzero order of vanishing are locally finite
in `|X'|`.

Nothing is assumed either: a component is integral, and it is good over the base because `X` is
and its inclusion is a closed immersion
(`AlgebraicGeometry.Space.isGood_integralClosedSubspace`), so it has the étale-local Noetherian
property; and `g ∘ f|_{X'}` is a unit of `R(X')` because it is the image of the unit `g` under
`AlgebraicGeometry.Space.rationalFunctionMap`, the dominance of `f|_{X'}` being
`AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`.
So this is Stacks 0ENN on `X'`, in the form
`AlgebraicGeometry.Space.ordRationalFunction_mem_weilDivisor`. -/
theorem componentDivisorLocallyFinite_of_isGood (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g) :
    ComponentDivisorLocallyFinite D sX hX sY hY hetale hintY g hg := fun W => by
  have hW := isGood_integralClosedSubspace D sX hX W.1
  exact ordRationalFunction_mem_weilDivisor D.site D.base D.base_mem hW.1 W.1.isIntegralSpace
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.1.subspace.ι ≫ sX) hW)
    (Units.map (rationalFunctionMap D.site D.base D.base_mem hW.1 hY.1 W.1.isIntegralSpace hintY
      (W.1.subspace.ι ≫ f)
      (pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace D sX hX sY hY hetale
        hintY W)).toMonoidHom hg.unit)

/-! ### Stacks 0EQ2 -/

/-- **Stacks 0EQ2, with the local finiteness of Stacks 0ENN taken.** In Situation 0EDT let
`f : X ⟶ Y` be an étale morphism of good algebraic spaces over `B`, let `Y` be integral with
`dim_δ(Y) = n` and let `g ∈ R(Y)^*`. Then, as cycles on `X`,

`f^*(div_Y(g)) = ∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`,

the sum being over the irreducible components `X'` of `X` (Remark 0EE8). The identity is read
coefficientwise, at every integral closed subspace of `X`, because the family of irreducible
components is only locally finite and the right-hand side is therefore not a sum in `Z_{n-1}(X)`.

Both sides are formed at the canonical embeddings of Stacks 0ENK, on `Y` for `g` and on each
component `X'` for `g ∘ f|_{X'}`, so that the two orders of vanishing are read at the same data
and are tied to one another through `AlgebraicGeometry.Space.rationalFunctionMap`.

Nothing about the components is assumed: the dominance of `f|_{X'}`, the source's first step, is
`AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`,
and `dim_δ(X') = n`, the source's second paragraph, is
`AlgebraicGeometry.Space.deltaDimensionClosed_univ_irreducibleComponentSubspace`. The only input
beyond the source's own hypotheses is the local finiteness of Stacks 0ENN, on `Y` and on each
component, which is what makes each principal divisor a cycle at all and which Stacks 0EQ1 takes
in the same shape.

This is the form taking that local finiteness; it is discharged in
`AlgebraicGeometry.Space.etalePullbackPrincipalDivisorCycle_apply_eq_componentPushforwardCoeff`. -/
theorem etalePullbackPrincipalDivisorCycle_apply_eq_componentPushforwardCoeff_of_locallyFinite
    (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g)
    (hfinY : TargetDivisorLocallyFinite D sY hY hintY g hg) {n : ℤ}
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (hfin : ComponentDivisorLocallyFinite D sX hX sY hY hetale hintY g hg)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg hfinY hnY).1 Z =
      (etaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g hg
        hfin).toEtaleComponentDivisorData.componentPushforwardCoeff Z :=
  (etalePullback_principalDivisorCycle_eq_sum_components_iff_eq_ord_closureImage D sX hX sY hY
      hbase hetale hintY g hg hfinY hnY hfin).2
    (fun T hT => (etaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g hg
      hfin).componentPushforwardCoeff_eq_apply_closureImage hfinY T hT) Z


/-- **Stacks 0EQ2.** In Situation 0EDT let `f : X ⟶ Y` be an étale morphism of good algebraic
spaces over `B`, let `Y` be integral with `dim_δ(Y) = n` and let `g ∈ R(Y)^*`. Then, as cycles on
`X`,

`f^*(div_Y(g)) = ∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`,

the sum being over the irreducible components `X'` of `X` (Remark 0EE8). The identity is read
coefficientwise, at every integral closed subspace of `X`, because the family of irreducible
components is only locally finite and the right-hand side is therefore not a sum in `Z_{n-1}(X)`.

Both sides are formed at the canonical embeddings of Stacks 0ENK, on `Y` for `g` and on each
component `X'` for `g ∘ f|_{X'}`, so that the two orders of vanishing are read at the same data
and are tied to one another through `AlgebraicGeometry.Space.rationalFunctionMap`.

Nothing beyond the source's own hypotheses goes in. The dominance of `f|_{X'}`, the source's
first step, is
`AlgebraicGeometry.Space.pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace`;
`dim_δ(X') = n`, the source's second paragraph, is
`AlgebraicGeometry.Space.deltaDimensionClosed_univ_irreducibleComponentSubspace`; and the local
finiteness of Stacks 0ENN, on `Y` and on each component, which is what makes each principal
divisor a cycle at all, is discharged by
`AlgebraicGeometry.Space.targetDivisorLocallyFinite_of_isGood` and
`AlgebraicGeometry.Space.componentDivisorLocallyFinite_of_isGood`. -/
@[stacks 0EQ2 "the displayed equality of cycles on X, read coefficientwise at every integral
  closed subspace, the sum being over the irreducible components of X (Remark 0EE8); it is read
  coefficientwise because that family is only locally finite, so the right-hand side is not a
  sum in Z_{n-1}(X). Both sides are formed at the canonical Stacks 0ENK embeddings of
  genericFractionEmbedding, on Y and on each component, so the two orders of vanishing are taken
  at the same data and are tied through rationalFunctionMap. UNCONDITIONAL: nothing beyond the
  source's own hypotheses goes in. The left-hand side is the flat pullback of Stacks 0EP8 at
  relative dimension 0 (etalePullbackCycleMap), an etale morphism being flat by Stacks 0467 and
  of relative dimension 0; the right-hand side is the sum of the pushforwards of Stacks 0EP1 of
  the principal divisors of Stacks 0EQ1 on the components. The source's first step, dominance of
  f restricted to a component, is PROVED
  (pointsMap_genericPoint_eq_genericPoint_irreducibleComponentSubspace); its second paragraph,
  dim_delta(X') = n for every component, is PROVED
  (deltaDimensionClosed_univ_irreducibleComponentSubspace); the local finiteness of Stacks 0ENN
  on Y and on each component, which makes the principal divisors cycles at all, is PROVED
  (targetDivisorLocallyFinite_of_isGood, componentDivisorLocallyFinite_of_isGood, out of
  ordRationalFunction_mem_weilDivisor, the repository's Stacks 0ENN); and the source's third to
  sixth paragraphs are componentPushforwardCoeff_eq_ord_of_chart, which computes both sides on
  one affine etale chart of X through the generic point of Z -- also a chart of Y because f is
  etale -- as sums of Ring.minimalPrimeOrd over the branches at the chart point: the coefficient
  of the left side is ord_{Z'}(g) by Lemma 0EPY
  (etalePullbackPrincipalDivisorCycle_apply_eq_apply_closureImage) and is the sum over ALL the
  branches (PrimeDivisor.ord_eq_finsum_minimalPrimeOrd_etaleChartComp, Stacks 0ENM), each term
  of the right side is the subsum over the branches lying on its component
  (ord_rationalFunctionMap_eq_finsum_branch_on_component), and the branches are partitioned over
  the components through the generic point of Z
  (finsum_minimalPrimes_eq_finsum_componentSubspace), which is the source's last step that
  {1,...,t} is the disjoint union of the J(X'); that replaces the square of Remark 0EPL,
  Lemma 02M1 and Lemma 02QG"]
theorem etalePullbackPrincipalDivisorCycle_apply_eq_componentPushforwardCoeff
    (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (hbase : f ≫ sY = sX) (hetale : IsEtale D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (g : rationalFunctions D.site D.base D.base_mem hY.1) (hg : IsUnit g) {n : ℤ}
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (etalePullbackPrincipalDivisorCycleOfGood D sX hX sY hY hbase hetale hintY g hg
        (targetDivisorLocallyFinite_of_isGood D sY hY hintY g hg) hnY).1 Z =
      (etaleComponentDivisorData D sX hX sY hY f hbase hetale hintY n hnY g hg
        (componentDivisorLocallyFinite_of_isGood D sX hX sY hY hetale hintY g
          hg)).toEtaleComponentDivisorData.componentPushforwardCoeff Z :=
  etalePullbackPrincipalDivisorCycle_apply_eq_componentPushforwardCoeff_of_locallyFinite D sX hX
    sY hY hbase hetale hintY g hg (targetDivisorLocallyFinite_of_isGood D sY hY hintY g hg) hnY
    (componentDivisorLocallyFinite_of_isGood D sX hX sY hY hetale hintY g hg) Z

end AlgebraicGeometry.Space

end
