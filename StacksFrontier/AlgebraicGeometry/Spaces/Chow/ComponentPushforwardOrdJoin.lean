module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BranchPartitionOverComponentSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentBranchOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentPushforwardOrdSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisorComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.StalkDimension

/-!
# The coefficient identity of Stacks 0EQ2, on one étale chart

The remaining content of Stacks 0EQ2 is the identity of integers

`∑_{X'} ord_{Z ∩ X'}(g ∘ f|_{X'}) = ord_{Z'}(g)`

at an integral closed subspace `Z ⊆ X` of δ-dimension `n - 1`, `Z'` being the image of `Z` in
`Y` and the sum running over the irreducible components `X'` of `X`. This file proves it on one
affine, reduced, locally Noetherian étale chart `W` of `X` through the generic point `ξ` of `Z`
— which, `f` being étale, is also a chart of `Y` through the generic point of `Z'`.

The proof joins three results:

* `AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_finsum_branch_on_component`:
  `ord_{Z ∩ X'}(g ∘ f|_{X'})` is the subsum of `Ring.minimalPrimeOrd` over the branches of
  `𝒪_{W, w}` lying on `X'`;
* `AlgebraicGeometry.Space.finsum_minimalPrimes_eq_finsum_componentSubspace`: the sum over all
  the branches of `𝒪_{W, w}` is the sum over the components through `ξ` of those subsums;
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_finsum_minimalPrimeOrd_etaleChartComp`: the sum
  over all the branches of `𝒪_{W, w}` is `ord_{Z'}(g)`, the chart being read as a chart of `Y`.

Together with
`EtaleComponentDivisorDataOfGood.componentPushforwardCoeff_eq_finsum_componentDivisorCycle` and
`EtaleComponentDivisorDataOfGood.componentDivisorCycle_apply_eq_ord` this computes both orders of
vanishing on one étale chart, in place of the square of henselian local rings of Remark 0EPL, the
length equality of Lemma 02M1 and the length decomposition of Lemma 02QG.

## Main results

* `EtaleComponentDivisorDataOfGood.componentDivisorCycle_apply_eq_finsum_branch_on_component`:
  one term of the sum, as the subsum over the branches lying on its component.
* `EtaleComponentDivisorDataOfGood.componentPushforwardCoeff_eq_ord_of_chart`: the coefficient
  identity.

## Implementation notes

**What the chart is asked to be, and why nothing more is needed.** `W` is an affine, reduced,
locally Noetherian étale chart of `X` whose chart scheme is affine, together with a point `w`
over the generic point of `Z`, Noetherian of Krull dimension at most one. Reducedness and the
Krull dimension can both be read off the `Y` side — `W` is also a chart of `Y`, `Y` is integral
and `Z'` is a prime divisor of `Y` — so no hypothesis is placed on `X` beyond the source's own.
The base-change charts `W ×_X X'` of the components need the same properties, and those are
derived here: affineness because `W ×_X X' → W` is a closed immersion hence an affine morphism,
reducedness because each component is integral
(`AlgebraicGeometry.Space.isReduced_chartScheme_of_isIntegralSpace`), local Noetherianity and
Noetherianity of the stalk because each component is good over the base
(`AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme_of_isGood`,
`AlgebraicGeometry.Space.isNoetherianRing_stalk_chartScheme_of_isGood`), and Krull dimension at
most one because `Z ∩ X'` is a prime divisor of the component
(`AlgebraicGeometry.Space.PrimeDivisor.krullDimLE_chartStalk`).

**The point of the base-change chart.** Each component `X'` through `ξ` needs a point `w'` of
`W ×_X X'` over `w`; it exists by
`AlgebraicGeometry.Space.exists_closedSubspaceBaseChangeChartProj_eq`, which is Stacks 03H4, and
the equality `W ×_X X' → W` sends it to `w` is what makes all the subsums subsums of *one* sum,
over the branches of `𝒪_{W, w}`.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
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

/-! ### One term of the sum, as a subsum over the branches -/

include data in
/-- **One term of the right-hand side of Stacks 0EQ2, as the subsum over the branches lying on
its component.** Let `W` be an affine, reduced, locally Noetherian étale chart of `X` with affine
chart scheme, let `w` be a point of it with Noetherian stalk of Krull dimension at most one lying
over the generic point of an integral closed subspace `Z ⊆ X`, and let `X'` be an irreducible
component of `X` through that generic point. If `Z` is the image of an integral closed subspace
`Z ∩ X'` of `X'` of δ-dimension `n - 1`, then the coefficient of `div_{X'}(g ∘ f|_{X'})` at
`Z ∩ X'` is

`∑_{𝔭 ⊂ 𝒪_{W, w} minimal, componentOfBranch 𝔭 = X'} ord_𝔭(ĝ)`,

`ĝ` being the reading of `g` in `Q(𝒪_{W, w})` on `W` read as a chart of `Y`. -/
theorem componentDivisorCycle_apply_eq_finsum_branch_on_component
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
    (hV : Z.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X V.1.subspace)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem V.1.subspace.toFunctor)
    (hZ' : IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      V.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) V.1.isClosedSubspace.2 Z' = Z)
    (hdimZ : deltaDimension D sX Z = n - 1)
    (W : SmallEtale D.site D.base D.base_mem X)
    [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1] [IsAffine (chartScheme W)]
    (w : chartScheme W)
    (hw : chartSchemeToPoints D.site D.base D.base_mem X W w =
      Z.ambientGenericPoint D.site D.base D.base_mem)
    [IsNoetherianRing ((chartScheme W).presheaf.stalk w)]
    [Ring.KrullDimLE 1 ((chartScheme W).presheaf.stalk w)] :
    (data.toEtaleComponentDivisorData.componentDivisorCycle V).1 Z' =
      ∑ᶠ p : {p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk w)) //
          ((componentOfBranch D.site D.base D.base_mem hX.1
              (D.isDecentSpace_of_isGood sX hX) W w
              (minimalPrimesEquivPrimeSpectrum _ p)).1 :
            irreducibleComponents (points D.site D.base D.base_mem X)).1 =
            subspacePointSet D.site D.base D.base_mem X V.1.subspace},
        Ring.minimalPrimeOrd p.1
          ((chartScheme W).totalFractionRingToStalkFractionRing w
            (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 W.obj.left
              (W.obj.hom ≫ f)
              (isEtale_comp D.site D.base D.base_mem
                ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem W.obj.hom).2
                  W.property) hetale)
              (g : rationalFunctions D.site D.base D.base_mem hY.1)))
          (IsUnit.map _ (IsUnit.map _ hg)) := by
  have hcod := data.codimension_eq_one_of_deltaDimension_pushforward_eq V Z' (hZ' ▸ hdimZ)
  rw [data.componentDivisorCycle_apply_eq_ord V Z' hcod]
  have hmem : chartSchemeToPoints D.site D.base D.base_mem X W w ∈
      subspacePointSet D.site D.base D.base_mem X V.1.subspace := hw ▸ hV
  set W' := closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 V.1.subspace
    V.1.isClosedSubspace W with hW'
  obtain ⟨w', hproj⟩ := exists_closedSubspaceBaseChangeChartProj_eq D.site D.base D.base_mem
    hX.1 V.1.subspace V.1.isClosedSubspace W w hmem
  subst hproj
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
    V.1.subspace V.1.isClosedSubspace W
  have hgood := isGood_integralClosedSubspace D sX hX V.1
  have : IsAffine (chartScheme W') :=
    isAffine_of_isAffineHom (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
      V.1.subspace V.1.isClosedSubspace W)
  have : IsAffine W'.obj.left.left.1 := ‹IsAffine (chartScheme W')›
  have : IsReduced (chartScheme W') :=
    isReduced_chartScheme_of_isIntegralSpace V.1.isClosedSubspace.1 V.1.isIntegralSpace _
  have : IsReduced W'.obj.left.left.1 := ‹IsReduced (chartScheme W')›
  have : IsLocallyNoetherian (chartScheme W') :=
    isLocallyNoetherian_chartScheme_of_isGood D (V.1.subspace.ι ≫ sX) hgood _
  have : IsLocallyNoetherian W'.obj.left.left.1 := ‹IsLocallyNoetherian (chartScheme W')›
  have : IsNoetherianRing ((chartScheme W').presheaf.stalk w') :=
    isNoetherianRing_stalk_chartScheme_of_isGood D (V.1.subspace.ι ≫ sX) hgood _ w'
  have : T0Space (points D.site D.base D.base_mem V.1.subspace.toFunctor) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem V.1.isClosedSubspace.1
      V.1.isIntegralSpace.2.1
  have hgenP : (Z'.toPrimeDivisor D.site D.base D.base_mem hgood.1 hcod).genericPoint D.site
        D.base D.base_mem V.1.subspace.toFunctor =
      Z'.ambientGenericPoint D.site D.base D.base_mem :=
    IsGenericPoint.eq
      ((Z'.toPrimeDivisor D.site D.base D.base_mem hgood.1 hcod).isGenericPoint_genericPoint
        D.site D.base D.base_mem V.1.subspace.toFunctor)
      (Z'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem
        V.1.isClosedSubspace.1)
  have hw' : chartSchemeToPoints D.site D.base D.base_mem V.1.subspace.toFunctor W' w' =
      (Z'.toPrimeDivisor D.site D.base D.base_mem hgood.1 hcod).genericPoint D.site D.base
        D.base_mem V.1.subspace.toFunctor := by
    rw [hgenP]
    refine (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
      V.1.isClosedSubspace.2).injective ?_
    rw [← chartSchemeToPoints_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1
      V.1.subspace V.1.isClosedSubspace W w', hw, ← hZ',
      IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem hX.1
        V.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) V.1.isClosedSubspace.2 Z']
  have : Ring.KrullDimLE 1 ((chartScheme W').presheaf.stalk w') :=
    (Z'.toPrimeDivisor D.site D.base D.base_mem hgood.1 hcod).krullDimLE_chartStalk
      D.site D.base D.base_mem V.1.isClosedSubspace.1 V.1.isIntegralSpace.2.1 W' w' hw'
  exact ord_rationalFunctionMap_eq_finsum_branch_on_component D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1 hintY hetale V.1.subspace V.1.isClosedSubspace
    V.2.2.2 V.1.isClosedSubspace.1 V.1.isIntegralSpace V.1.isIntegralSpace.2.1
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (V.1.subspace.ι ≫ sX) hgood)
    (data.dom V) _ W w' hw' hg.unit

/-! ### The partition of the branches at a named point -/

/-- Let `u` be a point of an étale chart `W` of a decent algebraic space `X` lying over the point
`x` of `|X|`, whose local ring has finitely many minimal primes. The sum over those minimal primes
of a function `F` is the sum, over the irreducible components of `X` through `x`, of the subsums
of `F` over the minimal primes whose component is that one. -/
theorem _root_.AlgebraicGeometry.Space.finsum_minimalPrimes_eq_finsum_componentSubspace_of_eq
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {M : Type*} [AddCommMonoid M]
    (W : SmallEtale B S hS X) (u : chartScheme W) (x : points B S hS X)
    (hx : chartSchemeToPoints B S hS X W u = x)
    (hfin : Finite ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)))
    (F : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)) → M) :
    ∑ᶠ p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)), F p =
      ∑ᶠ V : {V : IrreducibleComponentSubspace B S hS hX //
          x ∈ subspacePointSet B S hS X V.1.subspace},
        ∑ᶠ p : {p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)) //
            ((componentOfBranch B S hS hX hdec W u
                (minimalPrimesEquivPrimeSpectrum _ p)).1 :
              irreducibleComponents (points B S hS X)).1 =
              subspacePointSet B S hS X V.1.1.subspace},
          F p.1 := by
  subst hx
  exact finsum_minimalPrimes_eq_finsum_componentSubspace B S hS hX hdec W u hfin F

/-! ### The coefficient identity -/

include data in
/-- **The coefficient identity of Stacks 0EQ2, on one étale chart.** In Situation 0EDT let
`f : X ⟶ Y` be an étale morphism of good algebraic spaces over `B`, let `Y` be integral with
`dim_δ(Y) = n` and let `g ∈ R(Y)^*`. Let `Z ⊆ X` be an integral closed subspace of δ-dimension
`n - 1`, let `W` be an affine, reduced, locally Noetherian étale chart of `X` with affine chart
scheme and `w` a point of it over the generic point of `Z` whose local ring is Noetherian of
Krull dimension at most one, and let `Z'` be a prime divisor of `Y` whose generic point is the
image of `w` under `W` read as a chart of `Y`. Then

`∑_{X'} ord_{Z ∩ X'}(g ∘ f|_{X'}) = ord_{Z'}(g)`,

the sum running over the irreducible components `X'` of `X` — the left-hand side being the
coefficient at `Z` of `∑_{X'} (X' → X)_* div_{X'}(g ∘ f|_{X'})`, the right-hand side of
Stacks 0EQ2.

The family of restrictions `Z ∩ X'` is a datum; it exists by
`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq_of_ambientGenericPoint_mem`
and is unique by `AlgebraicGeometry.Space.IntegralClosedSubspace.injective_pushforward`. -/
theorem componentPushforwardCoeff_eq_ord_of_chart
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hdimZ : deltaDimension D sX Z = n - 1)
    (r : ∀ V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      Z.ambientGenericPoint D.site D.base D.base_mem ∈
        subspacePointSet D.site D.base D.base_mem X V.1.subspace →
      IntegralClosedSubspace D.site D.base D.base_mem V.1.subspace.toFunctor)
    (hr : ∀ (V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
      (hV : Z.ambientGenericPoint D.site D.base D.base_mem ∈
        subspacePointSet D.site D.base D.base_mem X V.1.subspace),
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
        V.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) V.1.isClosedSubspace.2
        (r V hV) = Z)
    (W : SmallEtale D.site D.base D.base_mem X)
    [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1] [IsAffine (chartScheme W)]
    (w : chartScheme W)
    (hw : chartSchemeToPoints D.site D.base D.base_mem X W w =
      Z.ambientGenericPoint D.site D.base D.base_mem)
    [IsNoetherianRing ((chartScheme W).presheaf.stalk w)]
    [Ring.KrullDimLE 1 ((chartScheme W).presheaf.stalk w)]
    (Z' : PrimeDivisor D.site D.base D.base_mem Y)
    (hZ' : chartSchemeToPoints D.site D.base D.base_mem Y
      (etaleChartComp D.site D.base D.base_mem hetale W) w =
      Z'.genericPoint D.site D.base D.base_mem Y) :
    data.toEtaleComponentDivisorData.componentPushforwardCoeff Z =
      (integralSpaceFractionEmbedding D sY hY hintY).ord hg.unit Z' := by
  have : IsAffine (etaleChartComp D.site D.base D.base_mem hetale W).obj.left.left.1 :=
    ‹IsAffine W.obj.left.left.1›
  have : IsReduced (etaleChartComp D.site D.base D.base_mem hetale W).obj.left.left.1 :=
    ‹IsReduced W.obj.left.left.1›
  have : IsLocallyNoetherian
      (etaleChartComp D.site D.base D.base_mem hetale W).obj.left.left.1 :=
    ‹IsLocallyNoetherian W.obj.left.left.1›
  have hfin : Finite ↥(minimalPrimes ((chartScheme W).presheaf.stalk w)) :=
    (minimalPrimes.finite_of_isNoetherianRing _).to_subtype
  have hY' := PrimeDivisor.ord_eq_finsum_minimalPrimeOrd_etaleChartComp D.site D.base D.base_mem
    hY.1 hintY hetale hintY.2.1
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY) Z' W w hZ' hg.unit
  have hpart := finsum_minimalPrimes_eq_finsum_componentSubspace_of_eq hX.1
    (D.isDecentSpace_of_isGood sX hX) W w _ hw hfin
    (fun p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk w)) =>
      Ring.minimalPrimeOrd p
        ((chartScheme W).totalFractionRingToStalkFractionRing w
          (rationalFunctionsToTotalFractionRing D.site D.base D.base_mem hY.1 W.obj.left
            (W.obj.hom ≫ f)
            (isEtale_comp D.site D.base D.base_mem
              ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem W.obj.hom).2
                W.property) hetale)
            (g : rationalFunctions D.site D.base D.base_mem hY.1)))
        (IsUnit.map _ (IsUnit.map _ hg)))
  refine Eq.trans ?_ (Eq.trans hpart.symm hY'.symm)
  rw [data.componentPushforwardCoeff_eq_finsum_componentDivisorCycle Z r hr]
  refine finsum_congr fun V => ?_
  exact data.componentDivisorCycle_apply_eq_finsum_branch_on_component Z V.1 V.2 (r V.1 V.2)
    (hr V.1 V.2) hdimZ W w hw

end EtaleComponentDivisorDataOfGood

end AlgebraicGeometry.Space

end
