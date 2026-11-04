module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SpecLocalStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorBaseChangeChartRatioUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorBaseChangeGermSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberThroughPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# The order of vanishing of a meromorphic section along a prime divisor, on any étale chart

Let `X` be a decent, locally Noetherian, integral algebraic space, `Z ⊂ X` a prime divisor with
generic point `ξ`, `ℒ` an invertible `𝒪_X`-module and `t` a regular meromorphic section of `ℒ`.
Let `V` be an affine étale chart of `X` over which `ℒ` is free on `e`, so that `t = c · e` over
`V` for the chart ratio `c = t / e ∈ 𝒦_X(V) = Q(Γ(V, 𝒪_V))`
(`AlgebraicGeometry.Space.chartRatio`), and let `v` be a point of the scheme of `V` over `ξ`.
This file proves that the order of vanishing `ord_{Z, ℒ}(t)` at the canonical ratio of
Stacks 0EPR is the order of vanishing of `c` at `v`, that is in the total ring of fractions of
`O = 𝒪_{V, v}`, and hence `∑_{𝔭 ⊂ O minimal} ord_{O/𝔭}(c)`.

## How it is proved

The canonical ratio is the image in `Q(𝒪^h_{X, ξ})` of the coefficient `a` of `t` against the
generator `s_ξ` chosen on `Spec A`, `A = 𝒪_{U, u}` the local ring of the chosen elementary étale
neighbourhood of `ξ`; so `ord_{Z, ℒ}(t) = ord_A(a)`, the map `A → 𝒪^h_{X, ξ}` being a
henselization. The two ratios `a` and `c` are compared over the charts `Q` of a covering sieve of
`V ×_X Spec A` (`PrimeDivisor.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio`): there
they differ by a unit. At a point `q` of such a chart over `v` and over the closed point of
`Spec A` both are read in `Frac(𝒪_{Q, q})`:

* along `A → 𝒪_{Q, q}`, the stalk map of the étale morphism `Q → Spec A`, which leaves `Ring.ord`
  unchanged (`AlgebraicGeometry.Scheme.Hom.ord_ringToStalk_of_etale`);
* along `𝒪_{V, v} → 𝒪_{Q, q}`, the stalk map of the flat morphism `Q → V`. That this map leaves
  `Ring.ord` unchanged, i.e. that `𝔪_v 𝒪_{Q, q} = 𝔪_q`, is the one geometric input proved here
  (`AlgebraicGeometry.Space.PrimeDivisor.mapsMaximalIdealOnto_genericStalkBaseChangeSchemeMap`):
  `Q → V` and `Q → Spec A → U` factor through the fibre product `P = U ×_X V`, whose projections
  are étale, and `Spec A → U` is surjective on stalks, so the maximal ideal of `𝒪_{Q, q}` is
  generated from that of `𝒪_{U, u}`, hence from that of `𝒪_{P, p}`, hence from that of `𝒪_{V, v}`.

The splitting over the minimal primes of `O` is the reduced case of Stacks 02QG,
`Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd`.

## Main definitions

All names below are in the namespace `AlgebraicGeometry.Space`.

* `chartPointMeromorphicMap`: the reading `𝒦_Y(W) → Q(𝒪_{W, w})` of a meromorphic function at a
  point of an affine chart.
* `PrimeDivisor.genericStalkMeromorphicToStalkFraction`: the reading
  `𝒦(Spec(𝒪_{U, u})) → Q(𝒪_{U, u})`.

## Main results

* `PrimeDivisor.mapsMaximalIdealOnto_genericStalkBaseChangeSchemeMap`:
  `𝔪_v 𝒪_{Q, q} = 𝔪_q` along the flat leg.
* `PrimeDivisor.map_chartPointMeromorphicMap_eq`: the germ square on an arbitrary, not
  necessarily integral, affine chart.
* `PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`:
  `ord_{Z, ℒ}(t) = ord_O(c)`.
* `PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_finsum_minimalPrimeOrd`:
  `ord_{Z, ℒ}(t) = ∑_{𝔭 ⊂ O minimal} ord_{O/𝔭}(c)`.
* `PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit`:
  the order vanishes when `c` is a unit of `O`.

## Implementation notes

The hypothesis that `c` is a unit of `Q(O)`, needed to state the right-hand side, holds for a
regular meromorphic section: `t / e` is then a nonzerodivisor of the total ring of fractions
`𝒦_X(V)`, hence a unit, and its image is a unit. It is carried as the hypothesis `hc`.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (hdec : IsDecentSpace B S hS X.1) (Z : PrimeDivisor B S hS X.1)

/-! ### The flat leg extends the maximal ideal -/

/-- The morphism of schemes from a chart of `Spec(𝒪_{U, u})` over the base change of a chart `V`
of `X` down to `Spec(𝒪_{U, u})`. -/
abbrev PrimeDivisor.genericStalkBaseChangeSpecMap (V : SmallEtale B S hS X.1)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) :
    chartScheme Q ⟶ Spec (Z.genericStalkRing B S hS X.2 hdec) :=
  chartSchemeMap (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS X.2 hdec V))

/-- The morphism from a chart of `Spec(𝒪_{U, u})` down to `Spec(𝒪_{U, u})` is étale, being the
morphism of schemes beneath a morphism of étale charts. -/
instance PrimeDivisor.etale_genericStalkBaseChangeSpecMap (V : SmallEtale B S hS X.1)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) :
    Etale (Z.genericStalkBaseChangeSpecMap B S hS hdec V ι) :=
  etale_toScheme_toOver_map B S hS _
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS X.2 hdec V))

/-- **The flat leg extends the maximal ideal.** Let `Q` be a chart of `Spec(𝒪_{U, u})` over the
base change of an étale chart `V` of `X`, and `q` a point of its scheme. Then the stalk map at
`q` of the morphism `Q → V` extends the maximal ideal of `𝒪_{V, g(q)}` to the maximal ideal of
`𝒪_{Q, q}`.

The morphisms `Q → V` and `Q → Spec(𝒪_{U, u}) → U` agree over `X`, so they factor through the
fibre product `P = U ×_X V` (`AlgebraicGeometry.Space.SmallEtale.prodObj`), whose two projections
are étale. The maximal ideal extends along `Q → Spec(𝒪_{U, u})`, being étale, and along
`Spec(𝒪_{U, u}) → U`, being surjective on stalks; hence along `Q → P`
(`AlgebraicGeometry.MapsMaximalIdealOnto.of_comp_left`), and so along `Q → P → V`. -/
theorem PrimeDivisor.mapsMaximalIdealOnto_genericStalkBaseChangeSchemeMap
    (V : SmallEtale B S hS X.1)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) (q : chartScheme Q) :
    MapsMaximalIdealOnto (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι) q := by
  let c₁ : (SmallEtale.toOver B S hS _).obj Q ⟶ (Z.genericEtaleChart B S hS X.2 hdec).obj.left :=
    (SmallEtale.toOver B S hS _).map
      (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)) ≫
      Z.genericStalkSpecToChart B S hS X.2 hdec
  let c₂ : (SmallEtale.toOver B S hS _).obj Q ⟶ V.obj.left :=
    (SmallEtale.toOver B S hS _).map ι ≫ (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V).g
  have h₁ : yoneda.map ((SmallEtale.toOver B S hS _).map
        (chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS X.2 hdec V))) =
      (Z.genericStalkBaseChangeChart B S hS X.2 hdec V).obj.hom :=
    (congrArg yoneda.map (toOver_map_chartToIdEtaleChart B S hS
      (Z.genericStalkBaseChangeChart B S hS X.2 hdec V))).trans (Functor.map_preimage _ _)
  have hi : yoneda.map c₁ ≫ (Z.genericEtaleChart B S hS X.2 hdec).obj.hom =
      yoneda.map c₂ ≫ V.obj.hom := by
    calc yoneda.map c₁ ≫ (Z.genericEtaleChart B S hS X.2 hdec).obj.hom
        = yoneda.map ((SmallEtale.toOver B S hS _).map ι) ≫
            (yoneda.map ((SmallEtale.toOver B S hS _).map
              (chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS X.2 hdec V))) ≫
              (Z.genericStalkMorphism B S hS X.2 hdec).hom) := by
          simp only [c₁, Functor.map_comp, Category.assoc]
          rfl
      _ = yoneda.map ((SmallEtale.toOver B S hS _).map ι) ≫
            ((Z.genericStalkBaseChangeChart B S hS X.2 hdec V).obj.hom ≫
              (Z.genericStalkMorphism B S hS X.2 hdec).hom) :=
          congrArg (fun m => yoneda.map ((SmallEtale.toOver B S hS _).map ι) ≫
            (m ≫ (Z.genericStalkMorphism B S hS X.2 hdec).hom)) h₁
      _ = yoneda.map ((SmallEtale.toOver B S hS _).map ι) ≫
            (yoneda.map (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V).g ≫ V.obj.hom) :=
          congrArg (fun m => yoneda.map ((SmallEtale.toOver B S hS _).map ι) ≫ m)
            (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V).comm
      _ = yoneda.map c₂ ≫ V.obj.hom :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ V.obj.hom) (yoneda.map_comp _ _).symm)
  let k : (SmallEtale.toOver B S hS _).obj Q ⟶
      (SmallEtale.toOver B S hS X.1).obj
        (SmallEtale.prodObj B S hS X.1 (Z.genericEtaleChart B S hS X.2 hdec) V) :=
    (Z.genericEtaleChart B S hS X.2 hdec).property.rep.lift' c₁ c₂ hi
  have e₁ : (BigFppfOver.toScheme B S hS).map k ≫ chartSchemeMap
      (SmallEtale.prodSnd B S hS X.1 (Z.genericEtaleChart B S hS X.2 hdec) V) =
      Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι :=
    (Functor.map_comp _ _ _).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map
      ((Z.genericEtaleChart B S hS X.2 hdec).property.rep.lift'_snd c₁ c₂ hi))
  have e₂ : (BigFppfOver.toScheme B S hS).map k ≫ chartSchemeMap
      (SmallEtale.prodFst B S hS X.1 (Z.genericEtaleChart B S hS X.2 hdec) V) =
      Z.genericStalkBaseChangeSpecMap B S hS hdec V ι ≫
        (BigFppfOver.toScheme B S hS).map (Z.genericStalkSpecToChart B S hS X.2 hdec) :=
    ((Functor.map_comp _ _ _).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map
      ((Z.genericEtaleChart B S hS X.2 hdec).property.rep.lift'_fst c₁ c₂ hi))).trans
      (Functor.map_comp _ _ _)
  have hσ : MapsMaximalIdealOnto (Z.genericStalkBaseChangeSpecMap B S hS hdec V ι) q :=
    @mapsMaximalIdealOnto_of_etale _ _ _
      (etale_toScheme_toOver_map B S hS _
        (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS X.2 hdec V))) q
  have hr : MapsMaximalIdealOnto
      ((BigFppfOver.toScheme B S hS).map (Z.genericStalkSpecToChart B S hS X.2 hdec))
      ((Z.genericStalkBaseChangeSpecMap B S hS hdec V ι).base q) := by
    refine MapsMaximalIdealOnto.congr
      (Z.toScheme_map_genericStalkSpecToChart B S hS X.2 hdec).symm ?_
    exact mapsMaximalIdealOnto_of_surjectiveOnStalks _ _
  have hk : MapsMaximalIdealOnto ((BigFppfOver.toScheme B S hS).map k) q :=
    MapsMaximalIdealOnto.of_comp_left ((hσ.comp hr).congr e₂.symm)
      (@mapsMaximalIdealOnto_of_etale _ _ _
        (etale_toScheme_toOver_map B S hS X.1
          (SmallEtale.prodFst B S hS X.1 (Z.genericEtaleChart B S hS X.2 hdec) V)) _)
  exact MapsMaximalIdealOnto.congr e₁ (hk.comp
    (@mapsMaximalIdealOnto_of_etale _ _ _
      (etale_toScheme_toOver_map B S hS X.1
        (SmallEtale.prodSnd B S hS X.1 (Z.genericEtaleChart B S hS X.2 hdec) V)) _))


/-! ### Reading a meromorphic function at a point of an affine chart -/

attribute [local instance] chartMeromorphicFunctionAlgebra

/-- **The reading of a meromorphic function at a point of an affine étale chart.** When `𝒦_Y(W)`
is the total ring of fractions of `𝒪_Y(W) = Γ(W, 𝒪_W)` (Stacks 0EN6, part (2)), a meromorphic
function on `W` is read in `Q(𝒪_{W, w})` along the germ at `w`, which carries nonzerodivisors to
nonzerodivisors, `W` being affine. -/
def chartPointMeromorphicMap (Y : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Y.1)
    (hW : IsAffine (chartScheme W))
    (hK : IsFractionRing ((structurePresheaf B S hS Y.1).obj (op W))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W)))
    (w : chartScheme W) :
    (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W) →+*
      FractionRing ((chartScheme W).presheaf.stalk w) :=
  haveI := hW
  haveI := hK
  IsLocalization.lift (M := ((structurePresheaf B S hS Y.1).obj (op W))⁰)
    (g := (algebraMap ((chartScheme W).presheaf.stalk w)
      (FractionRing ((chartScheme W).presheaf.stalk w))).comp
        ((chartScheme W).presheaf.germ ⊤ w trivial).hom)
    fun y => IsLocalization.map_units (M := ((chartScheme W).presheaf.stalk w)⁰) _
      ⟨_, (chartScheme W).nonZeroDivisors_le_comap_germ_top w y.2⟩

/-- On a regular function the reading at a point is the image of its germ. -/
theorem chartPointMeromorphicMap_algebraMap (Y : AlgebraicSpaces B S hS)
    (W : SmallEtale B S hS Y.1) (hW : IsAffine (chartScheme W))
    (hK : IsFractionRing ((structurePresheaf B S hS Y.1).obj (op W))
      ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W)))
    (w : chartScheme W) (s : (structurePresheaf B S hS Y.1).obj (op W)) :
    chartPointMeromorphicMap B S hS Y W hW hK w
        (algebraMap ((structurePresheaf B S hS Y.1).obj (op W))
          ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W)) s) =
      algebraMap ((chartScheme W).presheaf.stalk w)
        (FractionRing ((chartScheme W).presheaf.stalk w))
        (((chartScheme W).presheaf.germ ⊤ w trivial).hom s) :=
  have := hW
  have := hK
  IsLocalization.lift_eq _ _

/-- **The germ square at a point of a chart of `Spec(𝒪_{U, u})`, on an arbitrary affine chart.**
Let `V` be an affine étale chart of `X` and `Q` an affine chart of `Spec(𝒪_{U, u})` over the base
change of `V`, with the morphism `g : Q → V`. Reading a meromorphic function `c` of `V` at `g(q)`
and pushing it along the stalk map of `g` gives the same element of `Frac(𝒪_{Q, q})` as pulling
`c` back along `j : Spec(𝒪_{U, u}) ⟶ X`, restricting to `Q` and reading it at `q`.

This is `AlgebraicGeometry.Space.PrimeDivisor.lift_chartMeromorphicFunctionFieldEquiv_eq` with
the function field of `V` replaced by the total ring of fractions of `𝒪_{V, g(q)}`, so that `V`
need not be integral. Both sides are ring homomorphisms out of `𝒦_X(V) = Q(𝒪_X(V))`, and on a
regular function both are the germ at `q` of its pullback. -/
theorem PrimeDivisor.map_chartPointMeromorphicMap_eq
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (hQ : IsAffine (chartScheme Q))
    (hKQ : IsFractionRing
      ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q))
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
        (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q)))
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) (q : chartScheme Q)
    (c : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :
    haveI := (Z.flat_genericStalkBaseChangeSchemeMap B S hS hdec V ι)
    IsLocalization.map (T := ((chartScheme Q).presheaf.stalk q)⁰)
        (FractionRing ((chartScheme Q).presheaf.stalk q))
        ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).stalkMap q).hom
        (fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat _ q hx)
        (chartPointMeromorphicMap B S hS X V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV)
          ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q) c) =
      chartPointMeromorphicMap B S hS (Z.genericStalkSpace B S hS X.2 hdec) Q hQ hKQ q
        (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom
          (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
            (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) c)) := by
  have := (Z.flat_genericStalkBaseChangeSchemeMap B S hS hdec V ι)
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV
  set gs := Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι with hgs
  let ψ : FractionRing ((chartScheme V).presheaf.stalk (gs.base q)) →+*
      FractionRing ((chartScheme Q).presheaf.stalk q) :=
    IsLocalization.map (T := ((chartScheme Q).presheaf.stalk q)⁰)
        (FractionRing ((chartScheme Q).presheaf.stalk q)) (gs.stalkMap q).hom
        (fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat _ q hx)
  have key : ψ.comp
        (chartPointMeromorphicMap B S hS X V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) (gs.base q)) =
      (chartPointMeromorphicMap B S hS (Z.genericStalkSpace B S hS X.2 hdec) Q hQ hKQ q).comp
        (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom.comp
          (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
            (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V))) := by
    refine IsLocalization.ringHom_ext ((structurePresheaf B S hS X.1).obj (op V))⁰
      (RingHom.ext fun a => ?_)
    have hpull : chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
          (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V)
          (algebraMap ((structurePresheaf B S hS X.1).obj (op V))
            ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) a) =
        algebraMap ((structurePresheaf B S hS
              (Z.genericStalkSpace B S hS X.2 hdec).1).obj
            (op (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
              (op (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)))
          (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
            (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) a) :=
      RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS
        (Z.genericStalkMorphism B S hS X.2 hdec)
        (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
        (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V)) a
    have h1 := chartPointMeromorphicMap_algebraMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) (gs.base q) a
    have h2 := chartPointMeromorphicMap_algebraMap B S hS (Z.genericStalkSpace B S hS X.2 hdec)
      Q hQ hKQ q ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).map ι.op
        (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
          (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) a))
    have h3 := meromorphicFunctionSheaf_map_algebraMap B S hS
      (Z.genericStalkSpace B S hS X.2 hdec) ι (chartDiagramRestrict B S hS
        (Z.genericStalkMorphism B S hS X.2 hdec)
        (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) a)
    have chain := (congrArg (chartPointMeromorphicMap B S hS
        (Z.genericStalkSpace B S hS X.2 hdec) Q hQ hKQ q)
      ((congrArg (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
          (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom) hpull).trans h3)).trans h2
    have h4 : ψ (algebraMap ((chartScheme V).presheaf.stalk (gs.base q))
        (FractionRing ((chartScheme V).presheaf.stalk (gs.base q)))
          (((chartScheme V).presheaf.germ ⊤ (gs.base q) trivial).hom a)) =
        algebraMap ((chartScheme Q).presheaf.stalk q)
          (FractionRing ((chartScheme Q).presheaf.stalk q))
          ((gs.stalkMap q).hom (((chartScheme V).presheaf.germ ⊤ (gs.base q) trivial).hom a)) :=
      IsLocalization.map_eq _ _
    refine (congrArg ψ h1).trans (h4.trans (Eq.trans ?_ chain.symm))
    exact congrArg (algebraMap _ _) (Scheme.Hom.germ_stalkMap_apply gs ⊤ q trivial a)
  exact RingHom.congr_fun key c


/-! ### The coefficient at the generic point, read in `Q(𝒪_{U, u})` -/

variable (hInt : IsIntegralSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- **The meromorphic functions on `Spec(𝒪_{U, u})`, read in `Q(𝒪_{U, u})`.** They are the total
ring of fractions of `Γ(Spec(𝒪_{U, u}), 𝒪) = 𝒪_{U, u}` by Stacks 0EN6, part (2)
(`AlgebraicGeometry.Space.PrimeDivisor.isFractionRing_genericStalkMeromorphic`). -/
def PrimeDivisor.genericStalkMeromorphicToStalkFraction :
    ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
        (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS X.2 hdec))) →+*
      FractionRing (Z.genericStalkRing B S hS X.2 hdec) :=
  haveI := Z.isFractionRing_genericStalkMeromorphic B S hS X.2 hdec hInt hN
  IsLocalization.lift
    (M := (((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj
      (op (Z.genericStalkChart B S hS X.2 hdec))))⁰)
    (g := (algebraMap (Z.genericStalkRing B S hS X.2 hdec)
        (FractionRing (Z.genericStalkRing B S hS X.2 hdec))).comp
      (Scheme.ΓSpecIso (Z.genericStalkRing B S hS X.2 hdec)).hom.hom)
    fun y ↦ IsLocalization.map_units (FractionRing (Z.genericStalkRing B S hS X.2 hdec))
      ⟨_, Ring.map_mem_nonZeroDivisors_of_flatHom (RingHom.Flat.of_bijective
        (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.bijective) y.2⟩

/-- On a regular function the reading in `Q(𝒪_{U, u})` is the image of the function. -/
theorem PrimeDivisor.genericStalkMeromorphicToStalkFraction_algebraMap
    (y : (structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj
      (op (Z.genericStalkChart B S hS X.2 hdec))) :
    Z.genericStalkMeromorphicToStalkFraction B S hS hdec hInt hN
        (algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj
          (op (Z.genericStalkChart B S hS X.2 hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS X.2 hdec))) y) =
      algebraMap (Z.genericStalkRing B S hS X.2 hdec)
        (FractionRing (Z.genericStalkRing B S hS X.2 hdec))
        ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS X.2 hdec)).hom.hom y) :=
  have := Z.isFractionRing_genericStalkMeromorphic B S hS X.2 hdec hInt hN
  IsLocalization.lift_eq _ _

include hInt hN in
/-- **The order of vanishing of the canonical ratio is read in `Q(𝒪_{U, u})`.** The map
`Q(𝒪_{U, u}) → Q(𝒪^h_{X, ξ})` through which the ratio of Stacks 0EPR is defined is induced by a
henselization, which carries nonzerodivisors to nonzerodivisors and leaves `Ring.ord`
unchanged. -/
theorem PrimeDivisor.ord_genericStalkMeromorphicToGeneric
    [IsNoetherianRing (Z.genericStalkRing B S hS X.2 hdec)]
    [Ring.KrullDimLE 1 (Z.genericStalkRing B S hS X.2 hdec)]
    (a : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
      (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS X.2 hdec))) (ha : IsUnit a) :
    haveI := Z.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI := Z.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI := Z.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    Z.ord B S hS X.2 hdec (Z.genericStalkMeromorphicToGeneric B S hS X.2 hdec hInt hN a)
        (ha.map _) =
      Ring.ordTotalFracInt (Z.genericStalkRing B S hS X.2 hdec)
        (Z.genericStalkMeromorphicToStalkFraction B S hS hdec hInt hN a) (ha.map _) := by
  have := Z.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
  have := Z.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
  have := Z.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
  have : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS X.2 hdec) :=
    henselianLocalRing_isLocalRing B S hS X.1 X.2 (Z.genericPoint B S hS X.1) hdec
  have : Ring.KrullDimLE 1 ((Z.genericChart B S hS X.2 hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS X.2 hdec).point) :=
    ‹Ring.KrullDimLE 1 (Z.genericStalkRing B S hS X.2 hdec)›
  have : IsNoetherianRing ((Z.genericChart B S hS X.2 hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS X.2 hdec).point) :=
    ‹IsNoetherianRing (Z.genericStalkRing B S hS X.2 hdec)›
  have := Z.isFractionRing_genericStalkMeromorphic B S hS X.2 hdec hInt hN
  have hCof := ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X.1 X.2
    (Z.genericPoint B S hS X.1) ⟨Z.genericChart B S hS X.2 hdec⟩
  let φ' : Z.genericStalkRing B S hS X.2 hdec →+* ↥(Z.genericHenselianLocalRing B S hS X.2 hdec) :=
    stalkToHenselianLocalRing B S hS X.1 X.2 (Z.genericPoint B S hS X.1) hdec
      (Z.genericChart B S hS X.2 hdec)
  have hφ' : (Z.genericStalkRing B S hS X.2 hdec : Type u)⁰ ≤
      (↥(Z.genericHenselianLocalRing B S hS X.2 hdec))⁰.comap φ' :=
    fun _ hr => stalkToHenselianLocalRing_mem_nonZeroDivisors B S hS X.2 hdec Z hCof
      (Z.genericChart B S hS X.2 hdec) hr
  refine Ring.ordTotalFracInt_eq_of_map_eq
    (A' := Z.genericStalkRing B S hS X.2 hdec)
    (K' := FractionRing (Z.genericStalkRing B S hS X.2 hdec))
    (L := Z.genericTotalFractionRing B S hS X.2 hdec) (RingHom.id _) φ' le_rfl hφ'
    (fun _ => rfl) (ord_stalkToHenselianLocalRing B S hS X.2 hdec Z hCof _) _ _ ?_
  rw [IsLocalization.map_id]
  have key : Z.genericStalkMeromorphicToGeneric B S hS X.2 hdec hInt hN =
      (IsLocalization.map (M := (Z.genericStalkRing B S hS X.2 hdec : Type u)⁰)
        (S := FractionRing (Z.genericStalkRing B S hS X.2 hdec))
        (Z.genericTotalFractionRing B S hS X.2 hdec) φ' hφ').comp
        (Z.genericStalkMeromorphicToStalkFraction B S hS hdec hInt hN) := by
    refine IsLocalization.ringHom_ext
      (((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj
        (op (Z.genericStalkChart B S hS X.2 hdec))))⁰ (RingHom.ext fun y => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      Z.genericStalkMeromorphicToStalkFraction_algebraMap B S hS hdec hInt hN y,
      IsLocalization.map_eq]
    exact IsLocalization.lift_eq _ _
  exact RingHom.congr_fun key a

/-- **Restricting the coefficient to a chart over the base change and reading it there.** Let
`Q` be an affine chart of `Spec(𝒪_{U, u})` over the base change of `V`, with
`σ : Q → Spec(𝒪_{U, u})`. Reading a meromorphic function of `Spec(𝒪_{U, u})` in `Q(𝒪_{U, u})` and
pushing it along `𝒪_{U, u} → 𝒪_{Q, q}` (`AlgebraicGeometry.Scheme.Hom.ringToStalk`) gives its
restriction to `Q` read at `q`. -/
theorem PrimeDivisor.map_genericStalkMeromorphicToStalkFraction_eq (V : SmallEtale B S hS X.1)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (hQ : IsAffine (chartScheme Q))
    (hKQ : IsFractionRing
      ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q))
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
        (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q)))
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) (q : chartScheme Q)
    (hq : (Z.genericStalkBaseChangeSpecMap B S hS hdec V ι).base q =
      closedPoint (Z.genericStalkRing B S hS X.2 hdec))
    (a : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
      (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS X.2 hdec))) :
    IsLocalization.map (T := ((chartScheme Q).presheaf.stalk q)⁰)
        (FractionRing ((chartScheme Q).presheaf.stalk q))
        ((Z.genericStalkBaseChangeSpecMap B S hS hdec V ι).ringToStalk q)
        (fun _ hx => (Z.genericStalkBaseChangeSpecMap B S hS hdec V ι)
          |>.ringToStalk_mem_nonZeroDivisors_of_etale q hq hx)
        (Z.genericStalkMeromorphicToStalkFraction B S hS hdec hInt hN a) =
      chartPointMeromorphicMap B S hS (Z.genericStalkSpace B S hS X.2 hdec) Q hQ hKQ q
        (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map
          (ι ≫ chartToIdEtaleChart B S hS
            (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)).op).hom a) := by
  have := Z.isFractionRing_genericStalkMeromorphic B S hS X.2 hdec hInt hN
  set σ := Z.genericStalkBaseChangeSpecMap B S hS hdec V ι with hσ
  have hφ : (Z.genericStalkRing B S hS X.2 hdec : Type u)⁰ ≤
      ((chartScheme Q).presheaf.stalk q)⁰.comap (σ.ringToStalk q) :=
    fun _ hx => σ.ringToStalk_mem_nonZeroDivisors_of_etale q hq hx
  have key : (IsLocalization.map (M := (Z.genericStalkRing B S hS X.2 hdec : Type u)⁰)
        (S := FractionRing (Z.genericStalkRing B S hS X.2 hdec))
        (T := ((chartScheme Q).presheaf.stalk q)⁰)
        (FractionRing ((chartScheme Q).presheaf.stalk q)) (σ.ringToStalk q) hφ).comp
        (Z.genericStalkMeromorphicToStalkFraction B S hS hdec hInt hN) =
      (chartPointMeromorphicMap B S hS (Z.genericStalkSpace B S hS X.2 hdec) Q hQ hKQ q).comp
        ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map
          (ι ≫ chartToIdEtaleChart B S hS
            (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)).op).hom := by
    refine IsLocalization.ringHom_ext
      (((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj
        (op (Z.genericStalkChart B S hS X.2 hdec))))⁰ (RingHom.ext fun y => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply,
      Z.genericStalkMeromorphicToStalkFraction_algebraMap B S hS hdec hInt hN y,
      IsLocalization.map_eq, RingHom.comp_apply, RingHom.comp_apply,
      meromorphicFunctionSheaf_map_algebraMap B S hS (Z.genericStalkSpace B S hS X.2 hdec) _ y,
      chartPointMeromorphicMap_algebraMap]
    refine congrArg (algebraMap _ _) ?_
    show ((chartScheme Q).presheaf.germ ⊤ q trivial).hom (σ.appTop.hom
        ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS X.2 hdec)).inv.hom
          ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS X.2 hdec)).hom.hom y))) =
      ((chartScheme Q).presheaf.germ ⊤ q trivial).hom (σ.appTop.hom y)
    have hy : (Scheme.ΓSpecIso (Z.genericStalkRing B S hS X.2 hdec)).inv.hom
        ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS X.2 hdec)).hom.hom y) = y :=
      congrArg (fun f => CommRingCat.Hom.hom f y)
        (Scheme.ΓSpecIso (Z.genericStalkRing B S hS X.2 hdec)).hom_inv_id
    rw [hy]
  exact RingHom.congr_fun key a


/-! ### The comparison at a point of a chart over the base change -/

include hInt hN in
/-- **The two readings of a section have the same order of vanishing, compared at a point of a
chart over the base change.** Let `Q` be an affine chart of `Spec(𝒪_{U, u})` over the base change
of an affine étale chart `V` of `X`, and `q` a point of its scheme over the closed point of
`Spec(𝒪_{U, u})`, with image `y` in `V`. If over `Q` the restriction of a meromorphic function `a`
of `Spec(𝒪_{U, u})` is a unit regular function times the pullback of a meromorphic function `c`
of `V`, then `a` read in `Q(𝒪_{U, u})` and `c` read in `Q(𝒪_{V, y})` have the same order of
vanishing.

Both are read in `Frac(𝒪_{Q, q})`, along `𝒪_{U, u} → 𝒪_{Q, q}`, which leaves `Ring.ord` unchanged
because `Q → Spec(𝒪_{U, u})` is étale, and along `𝒪_{V, y} → 𝒪_{Q, q}`, which does because it is
flat and extends the maximal ideal
(`AlgebraicGeometry.Space.PrimeDivisor.mapsMaximalIdealOnto_genericStalkBaseChangeSchemeMap`);
there they differ by the unit, and `Ring.ordTotalFracInt_eq_of_map_eq_mul` concludes. -/
theorem PrimeDivisor.ordTotalFracInt_genericStalkMeromorphicToStalkFraction_eq
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    [IsNoetherianRing (Z.genericStalkRing B S hS X.2 hdec)]
    [Ring.KrullDimLE 1 (Z.genericStalkRing B S hS X.2 hdec)]
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (hQ : IsAffine (chartScheme Q))
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) (q : chartScheme Q)
    (hq : (Z.genericStalkBaseChangeSpecMap B S hS hdec V ι).base q =
      closedPoint (Z.genericStalkRing B S hS X.2 hdec))
    (y : chartScheme V) (hy : (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q = y)
    [IsNoetherianRing ((chartScheme V).presheaf.stalk y)]
    [Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk y)]
    (a : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
      (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS X.2 hdec)))
    (ha : IsUnit (Z.genericStalkMeromorphicToStalkFraction B S hS hdec hInt hN a))
    (c : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V))
    (hc : IsUnit (chartPointMeromorphicMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) y c))
    {w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q)}
    (hw : IsUnit w)
    (hrel : ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
          (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map
        (ι ≫ chartToIdEtaleChart B S hS
          (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)).op).hom a =
      algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q)) w *
        ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom
          (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
            (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) c)) :
    Ring.ordTotalFracInt (Z.genericStalkRing B S hS X.2 hdec)
        (Z.genericStalkMeromorphicToStalkFraction B S hS hdec hInt hN a) ha =
      Ring.ordTotalFracInt ((chartScheme V).presheaf.stalk y)
        (chartPointMeromorphicMap B S hS X V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) y c) hc := by
  subst hy
  have hKQ := Z.isFractionRing_genericStalkChartMeromorphic B S hS X.2 hdec hInt hN Q hQ
  have := (Z.flat_genericStalkBaseChangeSchemeMap B S hS hdec V ι)
  set σ := Z.genericStalkBaseChangeSpecMap B S hS hdec V ι with hσ
  set gs := Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι with hgs
  have hφ : (Z.genericStalkRing B S hS X.2 hdec : Type u)⁰ ≤
      ((chartScheme Q).presheaf.stalk q)⁰.comap (σ.ringToStalk q) :=
    fun _ hx => σ.ringToStalk_mem_nonZeroDivisors_of_etale q hq hx
  have hφ' : ((chartScheme V).presheaf.stalk (gs.base q))⁰ ≤
      ((chartScheme Q).presheaf.stalk q)⁰.comap (gs.stalkMap q).hom :=
    fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat _ q hx
  have hmax := Z.mapsMaximalIdealOnto_genericStalkBaseChangeSchemeMap B S hS hdec V ι q
  refine Ring.ordTotalFracInt_eq_of_map_eq_mul
    (C := (chartScheme Q).presheaf.stalk q)
    (K := FractionRing (Z.genericStalkRing B S hS X.2 hdec))
    (K' := FractionRing ((chartScheme V).presheaf.stalk (gs.base q)))
    (L := FractionRing ((chartScheme Q).presheaf.stalk q))
    (σ.ringToStalk q) (gs.stalkMap q).hom hφ hφ'
    (σ.ord_ringToStalk_of_etale q hq) (ord_stalkMap_of_flat_of_mapsMaximalIdealOnto gs hmax)
    ha hc (hw.map ((chartScheme Q).presheaf.germ ⊤ q trivial).hom) ?_
  have hA := Z.map_genericStalkMeromorphicToStalkFraction_eq B S hS hdec hInt hN V hQ hKQ ι q hq a
  have hV' := Z.map_chartPointMeromorphicMap_eq B S hS hdec hwa hfin V hV hQ hKQ ι q c
  refine hA.trans ?_
  rw [hrel, map_mul, chartPointMeromorphicMap_algebraMap]
  exact congrArg (_ * ·) hV'.symm

/-! ### The order of vanishing of a section on an arbitrary affine étale chart -/

include hInt hN in
/-- **The order of vanishing of a meromorphic section along a prime divisor, on any affine étale
chart trivializing the module.** Let `X` be a decent, locally Noetherian, integral algebraic
space satisfying the two hypotheses of Stacks 0EN6, `Z ⊂ X` a prime divisor, `ℒ` an invertible
`𝒪_X`-module and `t` a regular meromorphic section of `ℒ`. Let `V` be an affine étale chart of
`X` over which `ℒ` is free on the compatible family `e`, so that over `V` the section is
`t = c · e` with `c = t / e ∈ 𝒦_X(V)` its chart ratio
(`AlgebraicGeometry.Space.eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio`), and let `v` be a
point of the scheme of `V` over the generic point of `Z`. Then the order of vanishing
`ord_{Z, ℒ}(t)` at the canonical ratio of Stacks 0EPR is the order of vanishing of `c` read in the
total ring of fractions of `𝒪_{V, v}`.

The chart need be neither integral nor an elementary étale neighbourhood of the generic point;
the two dimension and finiteness instances on `𝒪_{V, v}` are
`AlgebraicGeometry.Space.PrimeDivisor.krullDimLE_chartStalk` and the local Noetherianness of the
chart. -/
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (v : chartScheme V) (hv : chartSchemeToPoints B S hS X.1 V v = Z.genericPoint B S hS X.1)
    [IsNoetherianRing ((chartScheme V).presheaf.stalk v)]
    [Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v)]
    (hc : IsUnit (chartPointMeromorphicMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v
        (chartRatio B S hS X.1 X.2 L V e hecompat hebij t))) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    orderOfVanishingSection.{u, u} B S hS X.2 hdec Z L t
        (Z.canonicalLocalRatio B S hS X.2 hdec L hL hInt hN) =
      Ring.ordTotalFracInt ((chartScheme V).presheaf.stalk v)
        (chartPointMeromorphicMap B S hS X V hV
          (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v
            (chartRatio B S hS X.1 X.2 L V e hecompat hebij t)) hc := by
  have := Z.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
  have := Z.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
  have := Z.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
  have := Z.isLocallyNoetherian_genericChart B S hS X.2 hdec hN
  have : IsNoetherianRing (Z.genericStalkRing B S hS X.2 hdec) :=
    inferInstanceAs (IsNoetherianRing ((Z.genericChart B S hS X.2 hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS X.2 hdec).point))
  have : Ring.KrullDimLE 1 (Z.genericStalkRing B S hS X.2 hdec) :=
    Z.krullDimLE_chartStalk B S hS X.2 hdec (Z.genericEtaleChart B S hS X.2 hdec)
      (Z.genericChart B S hS X.2 hdec).point
      (Z.chartSchemeToPoints_genericEtaleChart_point B S hS X.2 hdec)
  have hu := Z.isUnit_canonicalGenericRatio B S hS X.2 hdec L hL hInt hN t ht
  have hcoe := Z.coe_canonicalLocalRatio B S hS X.2 hdec L hL hInt hN t ht
  have ha := Z.isUnit_genericStalkCoefficient B S hS X.2 hdec L hL hInt hN t ht
  refine (Z.ord_congr B S hS X.2 hdec _ hu hcoe).trans ?_
  refine (Z.ord_genericStalkMeromorphicToGeneric B S hS hdec hInt hN
    (Z.genericStalkCoefficient B S hS X.2 hdec L hL t) ha).trans ?_
  obtain ⟨T, hT, hTrel⟩ := Z.exists_sieve_genericStalkCoefficient_eq_mul_chartRatio B S hS X.2
    hdec L hL t V e hecompat hebij
  obtain ⟨p, hp₁, hp₂⟩ := Z.exists_points_genericStalkBaseChangeChart B S hS X.2 hdec V v hv
  obtain ⟨Q, ι, hι, hQaff, q, hq⟩ := SmallEtale.exists_affine_mem_range_of_mem_topology B S hS
    (Z.genericStalkSpace B S hS X.2 hdec).1 hT p
  obtain ⟨w, hweq⟩ := hTrel ι hι
  have hqv : (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q = v :=
    (congrArg ((BigFppfOver.toScheme B S hS).map
      (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V).g).base hq).trans hp₂
  have hqc : (Z.genericStalkBaseChangeSpecMap B S hS hdec V ι).base q =
      closedPoint (Z.genericStalkRing B S hS X.2 hdec) := by
    refine Eq.trans ?_ hp₁
    rw [← hq]
    rfl
  exact Z.ordTotalFracInt_genericStalkMeromorphicToStalkFraction_eq B S hS hdec hInt hN hwa hfin
    V hV hQaff ι q hqc v hqv _ _ _ hc w.isUnit hweq


include hInt hN in
/-- **The order of vanishing of a meromorphic section along a prime divisor, as a sum over the
branches of a trivializing chart.** In the situation of
`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`, with
`O = 𝒪_{V, v}`, a reduced Noetherian local ring of dimension one,

`ord_{Z, ℒ}(t) = ∑_{𝔭 ⊂ O minimal} ord_{O/𝔭}(c)`,

where `c = t / e` is read in `Q(O)` and then in the fraction field of `O/𝔭`
(`Ring.minimalPrimeOrd`). This is the reduced case of Stacks 02QG,
`Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd`. -/
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_finsum_minimalPrimeOrd
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (v : chartScheme V) (hv : chartSchemeToPoints B S hS X.1 V v = Z.genericPoint B S hS X.1)
    [IsNoetherianRing ((chartScheme V).presheaf.stalk v)]
    [Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v)]
    (hc : IsUnit (chartPointMeromorphicMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v
        (chartRatio B S hS X.1 X.2 L V e hecompat hebij t))) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    orderOfVanishingSection.{u, u} B S hS X.2 hdec Z L t
        (Z.canonicalLocalRatio B S hS X.2 hdec L hL hInt hN) =
      ∑ᶠ p : minimalPrimes ((chartScheme V).presheaf.stalk v),
        Ring.minimalPrimeOrd p
          (chartPointMeromorphicMap B S hS X V hV
            (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v
              (chartRatio B S hS X.1 X.2 L V e hecompat hebij t)) hc := by
  have : IsReduced (chartScheme V) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y) X.2).mp hInt.1
      V.obj.left V.obj.hom V.property
  rw [Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt B S hS hdec hInt hN hwa
    hfin L hL t ht V hV e hecompat hebij v hv hc]
  exact Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd
    (O := (chartScheme V).presheaf.stalk v) (K := FractionRing ((chartScheme V).presheaf.stalk v))
    (Z.ringKrullDim_chartStalk B S hS X.2 hdec V v hv) _ _

include hInt hN in
/-- **A section which is a unit times the generator at a point has order of vanishing zero.** In
the situation of `PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`, if
the chart ratio `c = t / e`, read in `Q(𝒪_{V, v})`, is the image of a unit of `𝒪_{V, v}`, then
`ord_{Z, ℒ}(t) = 0`. -/
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_zero_of_isUnit
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (v : chartScheme V) (hv : chartSchemeToPoints B S hS X.1 V v = Z.genericPoint B S hS X.1)
    [IsNoetherianRing ((chartScheme V).presheaf.stalk v)]
    [Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v)]
    {r : (chartScheme V).presheaf.stalk v} (hr : IsUnit r)
    (hcr : chartPointMeromorphicMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v
        (chartRatio B S hS X.1 X.2 L V e hecompat hebij t) =
      algebraMap ((chartScheme V).presheaf.stalk v)
        (FractionRing ((chartScheme V).presheaf.stalk v)) r) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    orderOfVanishingSection.{u, u} B S hS X.2 hdec Z L t
        (Z.canonicalLocalRatio B S hS X.2 hdec L hL hInt hN) = 0 := by
  have hu : IsUnit (algebraMap ((chartScheme V).presheaf.stalk v)
      (FractionRing ((chartScheme V).presheaf.stalk v)) r) := hr.map _
  rw [Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt B S hS hdec hInt hN hwa
    hfin L hL t ht V hV e hecompat hebij v hv (hcr ▸ hu),
    Ring.ordTotalFracInt_congr _ (hcr ▸ hu) hu hcr]
  exact Ring.ordTotalFracInt_algebraMap_of_isUnit hr hu

end AlgebraicGeometry.Space

end
