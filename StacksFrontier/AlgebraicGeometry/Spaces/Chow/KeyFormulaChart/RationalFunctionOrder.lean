module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.EtaleStalkOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NormalIntegralElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# The order of vanishing of a rational function along a prime divisor, on any étale chart

Let `X` be a decent, locally Noetherian, integral algebraic space, `Z ⊂ X` a prime divisor with
generic point `ξ`, `V` an affine étale chart of `X` and `v` a point of the scheme of `V` lying
over `ξ`. The local ring `O = 𝒪_{V, v}` is a reduced Noetherian local ring of dimension one,
not necessarily a domain. This file proves that for an invertible rational function `f` of `X`

`ord_Z(f) = ∑_{𝔭 ⊂ O minimal} ord_{O/𝔭}(f)`,

where `f` is read in `Q(Γ(V, 𝒪_V))` (the first half of Stacks 0ENK,
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing`), then in `Q(O)` and then in the
fraction field of `O/𝔭`.

## How it is proved

The order of vanishing `ord_Z` of Definition 0ENL is computed on the henselian local ring
`𝒪^h_{X, ξ}`, through the chosen affine elementary étale neighbourhood `(U, u)` of `ξ`. Three
comparisons join it to `O`.

* `𝒪_{U, u} → 𝒪^h_{X, ξ}` is a henselization, so leaves `Ring.ord` unchanged
  (`AlgebraicGeometry.Space.ord_stalkToHenselianLocalRing`).
* Any two affine étale charts with points over the same point of `|X|` are refined by a common
  affine étale chart `W` with a point `w` over both
  (`AlgebraicGeometry.Space.exists_affine_common_chart_point`, from Stacks 03H4). Both legs are
  étale morphisms of schemes, so both stalk maps into `𝒪_{W, w}` leave `Ring.ord` unchanged
  (`AlgebraicGeometry.ord_stalkMap_of_etale`), and the two readings of a rational function agree
  in `Q(𝒪_{W, w})` by the chart independence of Stacks 0ENK
  (`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_comp_eq`). This is
  `AlgebraicGeometry.Space.ordTotalFracInt_chartPointRationalFunctionMap_eq`: **the order of
  vanishing of a rational function at a point of an affine étale chart depends only on the point
  of `|X|` below it.** No strict henselization is needed: the common refinement is an étale
  scheme chart, not the colimit of all of them.
* The splitting over the minimal primes of `O` is
  `Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd`, the reduced case of Stacks 02QG.

## Main definitions

* `AlgebraicGeometry.Scheme.totalFractionRingToStalkFractionRing`: `Q(Γ(T, 𝒪_T)) → Q(𝒪_{T, t})`
  for an affine scheme `T`.
* `AlgebraicGeometry.Space.chartPointRationalFunctionMap`: the reading `R(X) → Q(𝒪_{V, v})` of a
  rational function at a point of an affine étale chart.

## Main results

* `AlgebraicGeometry.Space.exists_affine_common_chart_point`
* `AlgebraicGeometry.Space.ordTotalFracInt_chartPointRationalFunctionMap_eq`
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap`:
  `ord_Z(f) = ord_O(f)`, Stacks 0ENM at an arbitrary affine étale chart with the chart not
  required to be integral.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_finsum_minimalPrimeOrd`: the formula above.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- The map `Q(Γ(T, 𝒪_T)) → Q(𝒪_{T, t})` induced by the germ at a point of an affine scheme,
which carries nonzerodivisors to nonzerodivisors, being a localization. -/
def Scheme.totalFractionRingToStalkFractionRing (T : Scheme.{u}) [IsAffine T] (t : T) :
    FractionRing Γ(T, ⊤) →+* FractionRing (T.presheaf.stalk t) :=
  IsLocalization.map _ (T.presheaf.germ ⊤ t trivial).hom (T.nonZeroDivisors_le_comap_germ_top t)

/-- The map `Q(Γ(T, 𝒪_T)) → Q(𝒪_{T, t})` sends the image of a global function to the image of
its germ. -/
theorem Scheme.totalFractionRingToStalkFractionRing_algebraMap (T : Scheme.{u}) [IsAffine T]
    (t : T) (a : Γ(T, ⊤)) :
    T.totalFractionRingToStalkFractionRing t (algebraMap _ _ a) =
      algebraMap _ _ ((T.presheaf.germ ⊤ t trivial).hom a) :=
  IsLocalization.map_eq ..

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### A common affine refinement through a point -/

/-- **Two étale charts with points over one point of `|X|` have a common affine refinement
through a point over both.** The fibre product of the two charts is a chart with a point over
the pair, by Stacks 03H4 (`AlgebraicGeometry.Space.exists_common_chart`), and an affine open of
its scheme around that point is again a chart. -/
theorem exists_affine_common_chart_point (U V : SmallEtale B S hS X) (u : chartScheme U)
    (v : chartScheme V)
    (huv : chartSchemeToPoints B S hS X U u = chartSchemeToPoints B S hS X V v) :
    ∃ (W : SmallEtale B S hS X) (a : W ⟶ U) (b : W ⟶ V) (w : chartScheme W),
      IsAffine (chartScheme W) ∧ (chartSchemeMap a).base w = u ∧
        (chartSchemeMap b).base w = v := by
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm,
    chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm] at huv
  obtain ⟨W, a, b, r, hra, hrb⟩ := exists_common_chart B S hS X U V _ _ huv
  obtain ⟨_, ⟨O, hO, rfl⟩, hwO, -⟩ :=
    (chartScheme W).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsToScheme B S hS W.obj.left r)) isOpen_univ
  have hι := toScheme_map_toOver_map_openChartInclusion B S hS X W O
  have key : ∀ (T : SmallEtale B S hS X) (c : W ⟶ T) (t : chartScheme T),
      pointsMap B S hS (yoneda.obj W.obj.left) (yoneda.map c.hom.left) r =
        (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj T)).symm t →
      (chartSchemeMap (openChartInclusion B S hS X W O ≫ c)).base ⟨_, hwO⟩ = t := by
    intro T c t h
    have h' := congrArg (pointsToScheme B S hS T.obj.left) h
    rw [pointsToScheme_pointsMap_yoneda] at h'
    have hc : chartSchemeMap (openChartInclusion B S hS X W O ≫ c) =
        Scheme.Opens.ι O ≫ chartSchemeMap c := by
      rw [chartSchemeMap, Functor.map_comp, Functor.map_comp, hι]; rfl
    rw [hc]
    exact h'.trans ((pointsEquivScheme B S hS _).apply_symm_apply t)
  exact ⟨openChart B S hS X W O, openChartInclusion B S hS X W O ≫ a,
    openChartInclusion B S hS X W O ≫ b, ⟨_, hwO⟩, hO, key U a u hra, key V b v hrb⟩


/-! ### The reading of a rational function at a point of an affine étale chart -/

variable (hX : IsAlgebraicSpace B S hS X)

/-- The pullback of rational functions to an étale chart does not depend on the proof that the
chart is étale, and may be computed with any spelling of the chart morphism. -/
theorem rationalFunctionsToTotalFractionRing_congr_chart (U : BigFppfOver B S hS)
    [IsAffine U.left.1] [IsReduced U.left.1] [IsLocallyNoetherian U.left.1]
    {c c' : yoneda.obj U ⟶ X} (h : c = c') (hc : IsEtale B S hS c) (hc' : IsEtale B S hS c') :
    rationalFunctionsToTotalFractionRing B S hS hX U c hc =
      rationalFunctionsToTotalFractionRing B S hS hX U c' hc' := by
  subst h
  rfl

/-- **The reading of a rational function at a point of an affine étale chart.** A rational
function of `X` is read in `Q(Γ(V, 𝒪_V))` by the first half of Stacks 0ENK
(`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing`) and then in `Q(𝒪_{V, v})` along
the germ at `v`. -/
def chartPointRationalFunctionMap (V : SmallEtale B S hS X) [IsAffine V.obj.left.left.1]
    [IsReduced V.obj.left.left.1] [IsLocallyNoetherian V.obj.left.left.1]
    (v : V.obj.left.left.1) :
    rationalFunctions B S hS hX →+* FractionRing (V.obj.left.left.1.presheaf.stalk v) :=
  (V.obj.left.left.1.totalFractionRingToStalkFractionRing v).comp
    (rationalFunctionsToTotalFractionRing B S hS hX V.obj.left V.obj.hom
      ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property))

/-- **The order of vanishing of a rational function at a point of an affine étale chart is
unchanged along a morphism of affine charts.** Let `g : W ⟶ V` be a morphism of affine étale
charts of `X` and `w` a point of the scheme of `W`. Then the reading of a unit `f` of `R(X)` at
`w` and its reading at the image of `w` have the same order of vanishing.

The stalk map of `g` at `w` is the stalk map of an étale morphism of schemes, so leaves
`Ring.ord` unchanged (`AlgebraicGeometry.ord_stalkMap_of_etale`), and it carries the reading at
the image of `w` to the reading at `w`, by the chart independence of Stacks 0ENK
(`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_comp_eq`) and the compatibility
of germs with stalk maps. -/
theorem ordTotalFracInt_chartPointRationalFunctionMap_map {V W : SmallEtale B S hS X}
    [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1]
    [IsAffine W.obj.left.left.1] [IsReduced W.obj.left.left.1]
    [IsLocallyNoetherian W.obj.left.left.1]
    (g : W ⟶ V) (w : W.obj.left.left.1)
    [Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk ((chartSchemeMap g).base w))]
    [Ring.KrullDimLE 1 (W.obj.left.left.1.presheaf.stalk w)]
    (f : rationalFunctions B S hS hX) (hf : IsUnit f) :
    Ring.ordTotalFracInt (V.obj.left.left.1.presheaf.stalk ((chartSchemeMap g).base w))
        (chartPointRationalFunctionMap B S hS hX V ((chartSchemeMap g).base w) f)
        (hf.map _) =
      Ring.ordTotalFracInt (W.obj.left.left.1.presheaf.stalk w)
        (chartPointRationalFunctionMap B S hS hX W w f) (hf.map _) := by
  set gs : W.obj.left.left.1 ⟶ V.obj.left.left.1 := chartSchemeMap g with hgs
  have het : Etale gs := etale_toScheme_toOver_map B S hS X g
  have hφ₀ : (V.obj.left.left.1.presheaf.stalk (gs.base w))⁰ ≤
      (W.obj.left.left.1.presheaf.stalk w)⁰.comap (gs.stalkMap w).hom :=
    fun _ hx => stalkMap_mem_nonZeroDivisors_of_flat gs w hx
  refine Ring.ordTotalFracInt_eq_of_map_eq (C := W.obj.left.left.1.presheaf.stalk w)
    (K := FractionRing (V.obj.left.left.1.presheaf.stalk (gs.base w)))
    (K' := FractionRing (W.obj.left.left.1.presheaf.stalk w))
    (L := FractionRing (W.obj.left.left.1.presheaf.stalk w))
    (gs.stalkMap w).hom (RingHom.id _) hφ₀ le_rfl
    (ord_stalkMap_of_etale gs w) (fun _ => rfl) _ _ ?_
  rw [IsLocalization.map_id]
  have hW : W.obj.hom = yoneda.map g.hom.left ≫ V.obj.hom := (CostructuredArrow.w g.hom).symm
  have hcV : IsEtale B S hS V.obj.hom := (isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2
    V.property
  have hcW : IsEtale B S hS W.obj.hom := (isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).2
    W.property
  have hc' : IsEtale B S hS (yoneda.map g.hom.left ≫ V.obj.hom) := hW ▸ hcW
  have key := rationalFunctionsToTotalFractionRing_comp_eq B S hS hX (U := V.obj.left)
    (V := W.obj.left) g.hom.left hcV hc'
    ((IsLocalization.map (T := (W.obj.left.left.1.presheaf.stalk w)⁰)
      (FractionRing (W.obj.left.left.1.presheaf.stalk w)) (gs.stalkMap w).hom hφ₀).comp
      (V.obj.left.left.1.totalFractionRingToStalkFractionRing (gs.base w)))
    (W.obj.left.left.1.totalFractionRingToStalkFractionRing w) (fun a => ?_) f
  · have hρ := DFunLike.congr_fun (rationalFunctionsToTotalFractionRing_congr_chart B S hS hX
      W.obj.left hW.symm hc' hcW) f
    exact key.symm.trans (congrArg _ hρ)
  · rw [RingHom.comp_apply, Scheme.totalFractionRingToStalkFractionRing_algebraMap,
      IsLocalization.map_eq, Scheme.totalFractionRingToStalkFractionRing_algebraMap]
    exact congrArg (algebraMap _ _) (Scheme.Hom.germ_stalkMap_apply gs ⊤ w trivial a)

/-- **The order of vanishing of a rational function at a point of an affine étale chart depends
only on the point of `|X|` below it.** If `u ∈ U` and `v ∈ V` lie over the same point of `X`,
the readings of a unit of `R(X)` at `u` and at `v` have the same order of vanishing.

Both are compared at a point of a common affine refinement
(`AlgebraicGeometry.Space.exists_affine_common_chart_point`) by
`AlgebraicGeometry.Space.ordTotalFracInt_chartPointRationalFunctionMap_map`. The dimension
hypothesis on the local rings of the refinement is supplied by `hdim`, which asks it at every
point over the given point of `|X|`. -/
theorem ordTotalFracInt_chartPointRationalFunctionMap_eq (U V : SmallEtale B S hS X)
    [IsAffine U.obj.left.left.1] [IsReduced U.obj.left.left.1]
    [IsLocallyNoetherian U.obj.left.left.1]
    [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1]
    (hred : ∀ W : SmallEtale B S hS X, IsReduced W.obj.left.left.1)
    (hnoeth : ∀ W : SmallEtale B S hS X, IsLocallyNoetherian W.obj.left.left.1)
    (u : U.obj.left.left.1) (v : V.obj.left.left.1)
    (hdim : ∀ (W : SmallEtale B S hS X) (w : W.obj.left.left.1),
      chartSchemeToPoints B S hS X W w = chartSchemeToPoints B S hS X V v →
        Ring.KrullDimLE 1 (W.obj.left.left.1.presheaf.stalk w))
    (huv : chartSchemeToPoints B S hS X U u = chartSchemeToPoints B S hS X V v)
    [Ring.KrullDimLE 1 (U.obj.left.left.1.presheaf.stalk u)]
    [Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)]
    (f : rationalFunctions B S hS hX) (hf : IsUnit f) :
    Ring.ordTotalFracInt (U.obj.left.left.1.presheaf.stalk u)
        (chartPointRationalFunctionMap B S hS hX U u f) (hf.map _) =
      Ring.ordTotalFracInt (V.obj.left.left.1.presheaf.stalk v)
        (chartPointRationalFunctionMap B S hS hX V v f) (hf.map _) := by
  obtain ⟨W, a, b, w, hWaff, hwa, hwb⟩ := exists_affine_common_chart_point B S hS U V u v huv
  have : IsAffine W.obj.left.left.1 := hWaff
  have := hred W
  have := hnoeth W
  have hwv : chartSchemeToPoints B S hS X W w = chartSchemeToPoints B S hS X V v := by
    rw [← hwb]
    exact (chartSchemeToPoints_map B S hS X b w).symm
  have := hdim W w hwv
  subst hwa hwb
  exact (ordTotalFracInt_chartPointRationalFunctionMap_map B S hS hX a w f hf).trans
    (ordTotalFracInt_chartPointRationalFunctionMap_map B S hS hX b w f hf).symm


/-! ### Points over the generic point of a prime divisor -/

variable (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

include hX hdec in
/-- **The local ring of an étale chart at a point over the generic point of a prime divisor has
dimension one.** The dimension of the local ring of `|X|` at the generic point is one, and it is
the dimension of the local ring of any étale chart at any point above it
(`AlgebraicGeometry.Space.coheight_eq_one_of_chartPoint_genericPoint`). -/
theorem PrimeDivisor.ringKrullDim_chartStalk (V : SmallEtale B S hS X) (v : V.obj.left.left.1)
    (hv : chartSchemeToPoints B S hS X V v = Z.genericPoint B S hS X) :
    ringKrullDim (V.obj.left.left.1.presheaf.stalk v) = 1 := by
  have hcp := chartPoint_chartSchemeToPoints B S hS ⟨X, hX⟩ V v
  rw [hv] at hcp
  rw [ringKrullDim_stalk_eq_coheight,
    coheight_eq_one_of_chartPoint_genericPoint B S hS hX hdec Z V.obj.left V.obj.hom V.property v
      hcp]
  rfl

include hX hdec in
/-- The local ring of an étale chart at a point over the generic point of a prime divisor has
Krull dimension at most one. -/
theorem PrimeDivisor.krullDimLE_chartStalk (V : SmallEtale B S hS X) (v : V.obj.left.left.1)
    (hv : chartSchemeToPoints B S hS X V v = Z.genericPoint B S hS X) :
    Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v) :=
  Ring.krullDimLE_iff.mpr (by
    rw [Z.ringKrullDim_chartStalk B S hS hX hdec V v hv]
    exact_mod_cast le_rfl)

/-- The distinguished point of the chosen affine elementary étale neighbourhood of the generic
point of a prime divisor lies over the generic point. -/
theorem PrimeDivisor.chartSchemeToPoints_genericEtaleChart_point :
    chartSchemeToPoints B S hS X (Z.genericEtaleChart B S hS hX hdec)
        (Z.genericChart B S hS hX hdec).point =
      Z.genericPoint B S hS X := by
  refine (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X _ _).trans ?_
  have h : (pointsEquivScheme B S hS (Z.genericChart B S hS hX hdec).scheme).symm
      (Z.genericChart B S hS hX hdec).point =
      presheafPoint B S hS _ (Z.genericChart B S hS hX hdec).point
        (Z.genericChart B S hS hX hdec).residueField_contained :=
    (Equiv.symm_apply_eq _).2 (pointsToScheme_presheafPoint B S hS _ _ _).symm
  refine Eq.trans ?_ (Z.genericChart B S hS hX hdec).map_point
  exact congrArg (pointsMap B S hS (yoneda.obj (Z.genericChart B S hS hX hdec).scheme)
    (Z.genericChart B S hS hX hdec).toSpace) h

/-! ### The comparison with the henselian local ring -/

/-- **The order of vanishing along a prime divisor is the order of vanishing at the
distinguished point of the chosen elementary étale neighbourhood.** The embedding of Stacks 0ENK
is the reading on `U` pushed along `𝒪_{U, u} → 𝒪^h_{X, ξ}`, a henselization, which carries
nonzerodivisors to nonzerodivisors and leaves `Ring.ord` unchanged
(`AlgebraicGeometry.Space.ord_stalkToHenselianLocalRing`). The point is given as any `u` equal
to the distinguished one, so that a consumer holding it in another spelling need not transport
a stalk. -/
theorem PrimeDivisor.ord_eq_ordTotalFracInt_genericEtaleChart (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    [IsAffine (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1]
    [IsReduced (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1]
    [IsLocallyNoetherian (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1]
    (u : (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1)
    (hu : u = (Z.genericChart B S hS hX hdec).point)
    [Ring.KrullDimLE 1 ((Z.genericEtaleChart B S hS hX hdec).obj.left.left.1.presheaf.stalk u)]
    (f : (rationalFunctions B S hS hX)ˣ) :
    (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z =
      Ring.ordTotalFracInt ((Z.genericEtaleChart B S hS hX hdec).obj.left.left.1.presheaf.stalk u)
        (chartPointRationalFunctionMap B S hS hX (Z.genericEtaleChart B S hS hX hdec) u
          (f : rationalFunctions B S hS hX)) (f.isUnit.map _) := by
  subst hu
  have : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  have := Z.nontrivial_genericHenselianLocalRing B S hS hX hdec hInt hN
  have := Z.isNoetherianRing_genericHenselianLocalRing B S hS hX hdec hInt hN
  have := Z.krullDimLE_genericHenselianLocalRing B S hS hX hdec hInt hN
  set U := Z.genericChart B S hS hX hdec with hU
  have : IsReduced U.scheme.left.1 :=
    ‹IsReduced (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1›
  have : IsLocallyNoetherian U.scheme.left.1 :=
    ‹IsLocallyNoetherian (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1›
  have : Ring.KrullDimLE 1 (U.scheme.left.1.presheaf.stalk U.point) :=
    ‹Ring.KrullDimLE 1 ((Z.genericEtaleChart B S hS hX hdec).obj.left.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)›
  set ρ := rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace U.etale_toSpace
    with hρ
  have hemb : (genericFractionEmbedding B S hS hX hdec hInt hN).emb Z
      (f : rationalFunctions B S hS hX) =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U
        (ρ (f : rationalFunctions B S hS hX)) := rfl
  have hφ' : (↥(U.scheme.left.1.presheaf.stalk U.point))⁰ ≤
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰.comap
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U) :=
    fun _ hr => stalkToHenselianLocalRing_mem_nonZeroDivisors B S hS hX hdec Z U hr
  have hN' : Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U =
      (IsLocalization.map (Z.genericTotalFractionRing B S hS hX hdec)
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U) hφ').comp
        (U.scheme.left.1.totalFractionRingToStalkFractionRing U.point) := by
    refine IsLocalization.ringHom_ext (Γ(U.scheme.left.1, ⊤))⁰ (RingHom.ext fun a => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      Scheme.totalFractionRingToStalkFractionRing_algebraMap, IsLocalization.map_eq]
    exact IsLocalization.map_eq _ _
  have hunit := f.isUnit.map ((genericFractionEmbedding B S hS hX hdec hInt hN).emb Z)
  calc (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z
      = Z.ord B S hS hX hdec ((genericFractionEmbedding B S hS hX hdec hInt hN).emb Z
          (f : rationalFunctions B S hS hX)) hunit := rfl
    _ = Z.ord B S hS hX hdec (Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U
          (ρ (f : rationalFunctions B S hS hX))) (hemb ▸ hunit) :=
        Z.ord_congr B S hS hX hdec _ _ hemb
    _ = _ := by
      have : IsNoetherianRing ((Z.genericEtaleChart B S hS hX hdec).obj.left.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point) :=
        (inferInstance : IsNoetherianRing (U.scheme.left.1.presheaf.stalk U.point))
      have : Nontrivial ((Z.genericEtaleChart B S hS hX hdec).obj.left.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point) :=
        (inferInstance : Nontrivial (U.scheme.left.1.presheaf.stalk U.point))
      refine Ring.ordTotalFracInt_eq_of_map_eq
        (A' := (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point)
        (K' := FractionRing ((Z.genericEtaleChart B S hS hX hdec).obj.left.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point))
        (L := Z.genericTotalFractionRing B S hS hX hdec) (RingHom.id _)
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U) le_rfl hφ'
        (fun _ => rfl) (ord_stalkToHenselianLocalRing B S hS hX hdec Z U) _ _ ?_
      rw [IsLocalization.map_id, hN']
      rfl

/-! ### The order of vanishing on an arbitrary affine étale chart -/

/-- **Stacks 0ENM at an arbitrary affine étale chart.** Let `Z` be a prime divisor of a decent,
locally Noetherian, integral algebraic space `X`, let `V` be an affine étale chart of `X` and
`v` a point of its scheme over the generic point of `Z`. Then the order of vanishing along `Z` of
an invertible rational function `f` is the order of vanishing at `v` of the reading of `f` in
the total ring of fractions of `𝒪_{V, v}`.

Unlike `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_scheme_ord_of_chart` the chart need not be
an elementary étale neighbourhood, nor integral: `𝒪_{V, v}` is a reduced one-dimensional local
ring, possibly with several minimal primes, and its order of vanishing is the one on its total
ring of fractions. The proof compares the chart with the chosen elementary étale neighbourhood
of the generic point at a common affine refinement
(`AlgebraicGeometry.Space.ordTotalFracInt_chartPointRationalFunctionMap_eq`) and the
neighbourhood with the henselian local ring
(`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ordTotalFracInt_genericEtaleChart`).

The dimension hypothesis on `𝒪_{V, v}`, needed to state the right-hand side, is
`AlgebraicGeometry.Space.PrimeDivisor.krullDimLE_chartStalk`. -/
@[stacks 0ENM "at an arbitrary affine étale chart, not necessarily integral, through a point
  over the generic point of the prime divisor: the order of vanishing is the one of the total
  ring of fractions of the local ring of the chart at the point"]
theorem PrimeDivisor.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (V : SmallEtale B S hS X) [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1] (v : V.obj.left.left.1)
    (hv : chartSchemeToPoints B S hS X V v = Z.genericPoint B S hS X)
    [Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)]
    (f : (rationalFunctions B S hS hX)ˣ) :
    (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z =
      Ring.ordTotalFracInt (V.obj.left.left.1.presheaf.stalk v)
        (chartPointRationalFunctionMap B S hS hX V v (f : rationalFunctions B S hS hX))
        (f.isUnit.map _) := by
  have hred : ∀ W : SmallEtale B S hS X, IsReduced W.obj.left.left.1 := fun W =>
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsReduced Y) hX).mp hInt.1
      W.obj.left W.obj.hom W.property
  have hnoeth : ∀ W : SmallEtale B S hS X, IsLocallyNoetherian W.obj.left.left.1 := fun W =>
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y)
      hX).mp hN W.obj.left W.obj.hom W.property
  have : IsAffine (Z.genericEtaleChart B S hS hX hdec).obj.left.left.1 :=
    Z.isAffine_genericChart B S hS hX hdec
  have := hred (Z.genericEtaleChart B S hS hX hdec)
  have := hnoeth (Z.genericEtaleChart B S hS hX hdec)
  have hu := Z.chartSchemeToPoints_genericEtaleChart_point B S hS hX hdec
  have := Z.krullDimLE_chartStalk B S hS hX hdec _ _ hu
  rw [Z.ord_eq_ordTotalFracInt_genericEtaleChart B S hS hX hdec hInt hN _ rfl f]
  exact ordTotalFracInt_chartPointRationalFunctionMap_eq B S hS hX _ V hred hnoeth _ v
    (fun W w hw => Z.krullDimLE_chartStalk B S hS hX hdec W w (hw.trans hv)) (hu.trans hv.symm)
    _ f.isUnit

/-- **The order of vanishing of a rational function along a prime divisor, as a sum over the
branches of an étale chart.** Let `Z` be a prime divisor of a decent, locally Noetherian,
integral algebraic space `X`, let `V` be an affine étale chart of `X` and `v` a point of its
scheme over the generic point of `Z`, and let `O = 𝒪_{V, v}`, a reduced Noetherian local ring
of dimension one. Then for an invertible rational function `f` of `X`

`ord_Z(f) = ∑_{𝔭 ⊂ O minimal} ord_{O/𝔭}(f)`,

where `f` is read in `Q(Γ(V, 𝒪_V))`, then in `Q(O)` and then in the fraction field of `O/𝔭`
(`Ring.minimalPrimeOrd`).

This is `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap`
followed by the reduced case of Stacks 02QG, `Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd`. -/
theorem PrimeDivisor.ord_eq_finsum_minimalPrimeOrd (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (V : SmallEtale B S hS X) [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1] (v : V.obj.left.left.1)
    (hv : chartSchemeToPoints B S hS X V v = Z.genericPoint B S hS X)
    [Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)]
    (f : (rationalFunctions B S hS hX)ˣ) :
    (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z =
      ∑ᶠ p : minimalPrimes (V.obj.left.left.1.presheaf.stalk v),
        Ring.minimalPrimeOrd p
          (chartPointRationalFunctionMap B S hS hX V v (f : rationalFunctions B S hS hX))
          (f.isUnit.map _) := by
  rw [Z.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap B S hS hX hdec hInt hN V v hv f]
  exact Ring.ordTotalFracInt_eq_finsum_minimalPrimeOrd
    (Z.ringKrullDim_chartStalk B S hS hX hdec V v hv) _ _


/-- **A rational function which is a unit at a point over the generic point has order of
vanishing zero.** If the reading of an invertible rational function `f` at a point `v` of an
affine étale chart over the generic point of `Z` is the image of a unit of `𝒪_{V, v}`, then
`ord_Z(f) = 0`. -/
theorem PrimeDivisor.ord_eq_zero_of_chartPointRationalFunctionMap_eq_algebraMap
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (V : SmallEtale B S hS X) [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1] (v : V.obj.left.left.1)
    (hv : chartSchemeToPoints B S hS X V v = Z.genericPoint B S hS X)
    (f : (rationalFunctions B S hS hX)ˣ) {r : V.obj.left.left.1.presheaf.stalk v}
    (hr : IsUnit r)
    (hfr : chartPointRationalFunctionMap B S hS hX V v (f : rationalFunctions B S hS hX) =
      algebraMap (V.obj.left.left.1.presheaf.stalk v)
        (FractionRing (V.obj.left.left.1.presheaf.stalk v)) r) :
    (genericFractionEmbedding B S hS hX hdec hInt hN).ord f Z = 0 := by
  have := Z.krullDimLE_chartStalk B S hS hX hdec V v hv
  have hu : IsUnit (algebraMap (V.obj.left.left.1.presheaf.stalk v)
      (FractionRing (V.obj.left.left.1.presheaf.stalk v)) r) := hr.map _
  rw [Z.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap B S hS hX hdec hInt hN V v hv f,
    Ring.ordTotalFracInt_congr _ _ hu hfr]
  exact Ring.ordTotalFracInt_algebraMap_of_isUnit hr hu

end Space

end AlgebraicGeometry

end
