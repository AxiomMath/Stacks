module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafModuleMap
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# The order of vanishing of a meromorphic section along isomorphisms

Let `X` be a decent, locally Noetherian, integral algebraic space, `Z ⊂ X` a prime divisor with
generic point `ξ`, `ℒ` an invertible `𝒪_X`-module and `t` a regular meromorphic section of `ℒ`.
The order of vanishing `ord_{Z, ℒ}(t)` of Stacks 0EPR is taken at the canonical ratio `t / s_ξ`
against a generator `s_ξ` of `ℒ` chosen at `ξ`. This file proves that it is unchanged by the two
operations which identify one presentation of `(X, ℒ, t)` with another:

* an isomorphism of modules `α : ℒ ≅ ℒ'`: `ord_{Z, ℒ'}(α(t)) = ord_{Z, ℒ}(t)`;
* an isomorphism of algebraic spaces `φ : X ≅ X'`, for a regular meromorphic section `t'` of an
  invertible `𝒪_{X'}`-module `ℒ'` and prime divisors `Z ⊂ X`, `Z' ⊂ X'` with `φ(ξ_Z) = ξ_{Z'}`:
  `ord_{Z, φ^*ℒ'}(φ^*t') = ord_{Z', ℒ'}(t')`, the pullback `φ^*t'` being that of Stacks 0ENC.

In both cases the two canonical ratios are read against generators chosen independently, so they
need not correspond to each other; their orders do. Each order is computed on any affine étale
chart `V` through a point `v` over the generic point over which the module is free, as the order
in `Q(𝒪_{V, v})` of the ratio of the section against the free generator
(`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`).
For a module isomorphism one chart serves both modules, `ℒ'` being free on `α(e)` when `ℒ` is free
on `e`, and the two ratios agree. For an isomorphism of spaces an affine chart `Q` of `X` over
which `φ^*ℒ'` is free on the pullback of a free generator of `ℒ'` is, through `φ`, a chart of `X'`
with the same scheme; over the commuting square of charts whose vertical map is the identity of
`Q` the pullback of `t'` is the pullback of its ratio, and the two readings of that ratio in
`Q(𝒪_{Q, q})` agree.

## Main results

All in the namespace `AlgebraicGeometry.Space`.

* `exists_affine_chart_free_of_point`: through every point of `|X|` there
  is an affine étale chart over which an invertible module is free.
* `PrimeDivisor.exists_orderOfVanishingSection_eq_ordTotalFracInt_chartRatio`:
  the computation of the order on such a chart, with its side conditions discharged.
* `PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_sectionsMap_of_iso`:
  invariance under an isomorphism of modules.
* `pullbacksMeromorphicSections_of_iso`: pullbacks of meromorphic functions
  are defined along an isomorphism of algebraic spaces.
* `PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_pullbackMeromorphicSection_of_iso`:
  invariance under pullback along an isomorphism of algebraic spaces.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology chartMeromorphicFunctionAlgebra chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Through every point of an algebraic space there is an affine étale chart on which an
invertible module is free.** For a point `x` of `|X|` there is an étale chart `V` of `X` with
affine scheme, a point `v` of that scheme over `x`, and a compatible family of free generators of
`ℒ` over the charts over `V`. -/
theorem exists_affine_chart_free_of_point (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L)
    (x : points B S hS X.1) :
    ∃ (V : SmallEtale B S hS X.1) (_ : IsAffine (chartScheme V)) (v : chartScheme V)
      (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
      (_ : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
        (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
      (_ : ∀ (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ V),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W₁ ↦ r • e W₁ k),
      chartSchemeToPoints B S hS X.1 V v = x := by
  obtain ⟨C, hC⟩ := exists_isSurjective_chart B S hS X
  obtain ⟨c, hc⟩ := surjective_chartSchemeToPoints B S hS X.1 C hC x
  obtain ⟨W, κ, hW, w, e, hcompat, hfree, hw⟩ :=
    exists_affine_chart_free_of_chart B S hS X L hL C c
  refine ⟨W, hW, w, e, hcompat, hfree, ?_⟩
  rw [← chartSchemeToPoints_map B S hS X.1 κ w, hw, hc]

/-- The weakly associated points of an integral algebraic space have local ring dimension zero. -/
private theorem localRingDimension_eq_zero_of_isIntegralSpace {X : AlgebraicSpaces B S hS}
    (hInt : IsIntegralSpace B S hS X.1) :
    ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0 :=
  fun _ hz ↦ by
    rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS _
      hInt.hasEtaleLocalProperty_isReduced] at hz

section Module

variable {X : AlgebraicSpaces B S hS} (hdec : IsDecentSpace B S hS X.1)
    (Z : PrimeDivisor B S hS X.1) (hInt : IsIntegralSpace B S hS X.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **The order of vanishing of a meromorphic section is computed on any free affine chart.**
A packaging of
`PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt`
in which the side conditions on the chart are discharged: the chart is locally Noetherian, its
local ring at a point over the generic point of `Z` has dimension one, and the ratio of a regular
section is a unit. -/
theorem PrimeDivisor.exists_orderOfVanishingSection_eq_ordTotalFracInt_chartRatio
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (v : chartScheme V) (hv : chartSchemeToPoints B S hS X.1 V v = Z.genericPoint B S hS X.1)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t) :
    ∃ (_ : IsNoetherianRing ((chartScheme V).presheaf.stalk v))
      (_ : Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v))
      (hc : IsUnit (chartPointMeromorphicMap B S hS X V hV
        (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v
          (chartRatio B S hS X.1 X.2 L V e hecompat hebij t))),
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
  have : IsLocallyNoetherian (chartScheme V) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun Y : Scheme.{u} => IsLocallyNoetherian Y)
      X.2).mp hN V.obj.left V.obj.hom V.property
  have : IsNoetherianRing ((chartScheme V).presheaf.stalk v) := inferInstance
  have : Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v) :=
    Z.krullDimLE_chartStalk B S hS X.2 hdec V v hv
  have hc := (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS X hwa hfin L V hV e
    hecompat hebij t ht).map (chartPointMeromorphicMap B S hS X V hV
      (isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV) v)
  exact ⟨inferInstance, inferInstance, hc,
    Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt B S hS hdec hInt hN hwa
      hfin L hL t ht V hV e hecompat hebij v hv hc⟩

include hInt hN in
/-- **The order of vanishing is invariant under an isomorphism of modules.** Let `α : ℒ ≅ ℒ'` be
an isomorphism of invertible `𝒪_X`-modules and `t` a regular meromorphic section of `ℒ`. Then the
order of vanishing along `Z` of the image `α(t)` of `t` under the induced isomorphism
`𝒦_X(ℒ) ≅ 𝒦_X(ℒ')`, at the canonical ratio of `ℒ'`, is the order of vanishing of `t` at the
canonical ratio of `ℒ`.

Both are computed on one affine chart through a point over the generic point of `Z` over which
`ℒ` is free on `e`; there `ℒ'` is free on `α(e)` and the two chart ratios agree. -/
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_sectionsMap_of_iso
    (L L' : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule (B := B) X L)
    (hL' : IsInvertibleModule (B := B) X L') (α : L ≅ L')
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    orderOfVanishingSection.{u, u} B S hS X.2 hdec Z L'
        (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS X.1 X.2 α.hom) t)
        (Z.canonicalLocalRatio B S hS X.2 hdec L' hL' hInt hN) =
      orderOfVanishingSection.{u, u} B S hS X.2 hdec Z L t
        (Z.canonicalLocalRatio B S hS X.2 hdec L hL hInt hN) := by
  have hwa := localRingDimension_eq_zero_of_isIntegralSpace B S hS hInt
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X.1 X.2 hN
  obtain ⟨V, hV, v, e, hecompat, hebij, hv⟩ :=
    exists_affine_chart_free_of_point B S hS X L hL (Z.genericPoint B S hS X.1)
  let a : ∀ W : SmallEtale B S hS X.1, L.val.obj (op W) → L'.val.obj (op W) :=
    fun W ↦ (α.hom.val.app (op W)).hom
  have ha : ∀ W : SmallEtale B S hS X.1, Function.Bijective (a W) := fun W ↦
    ⟨fun x y h ↦ by
      have hx := congrArg (fun φ : L ⟶ L ↦ (φ.val.app (op W)).hom x) α.hom_inv_id
      have hy := congrArg (fun φ : L ⟶ L ↦ (φ.val.app (op W)).hom y) α.hom_inv_id
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
        LinearMap.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.hom_id,
        LinearMap.id_coe, id_eq] at hx hy
      rw [← hx, ← hy]
      exact congrArg _ h,
    fun y ↦ ⟨(α.inv.val.app (op W)).hom y, by
      have hy := congrArg (fun φ : L' ⟶ L' ↦ (φ.val.app (op W)).hom y) α.inv_hom_id
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
        LinearMap.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.hom_id,
        LinearMap.id_coe, id_eq] at hy
      exact hy⟩⟩
  let e' : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L'.val.obj (op W) := fun W k ↦ a W (e W k)
  have hecompat' : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L'.val.map g.op).hom (e' W k) = e' W' (g ≫ k) := by
    intro W W' k g
    show (L'.val.map g.op).hom ((α.hom.val.app (op W)).hom (e W k)) =
      (α.hom.val.app (op W')).hom (e W' (g ≫ k))
    rw [← hecompat W W' k g]
    exact (PresheafOfModules.naturality_apply α.hom.val g.op (e W k)).symm
  have hebij' : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e' W k := by
    intro W k
    have hfun : (fun r : chartRing B S hS X.1 X.2 W ↦ r • e' W k) =
        a W ∘ fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k := by
      funext r
      exact ((α.hom.val.app (op W)).hom.map_smul r (e W k)).symm
    rw [hfun]
    exact (ha W).comp (hebij W k)
  have ht' := isRegularMeromorphicSection_sectionsMap_of_iso B S hS X.1 X.2 α t ht
  have hratio : chartRatio B S hS X.1 X.2 L' V e' hecompat' hebij'
        (SheafOfModules.sectionsMap (meromorphicSectionSheafMap B S hS X.1 X.2 α.hom) t) =
      chartRatio B S hS X.1 X.2 L V e hecompat hebij t := by
    refine chartRatio_eq_of_eval_eq B S hS X.1 X.2 L' V e' hecompat' hebij' _ _ ?_
    rw [eval_sectionsMap_meromorphicSectionSheafMap,
      eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X.1 X.2 L V e hecompat hebij t]
    exact (meromorphicSectionSheafMap_toMeromorphicSectionSheaf B S hS X.1 X.2 α.hom V _).trans
      (congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2 L' V)
        (meromorphicSectionModuleMap_tmul B S hS X.1 X.2 α.hom V _ _))
  obtain ⟨_, _, hc, hord⟩ := Z.exists_orderOfVanishingSection_eq_ordTotalFracInt_chartRatio B S hS
    hdec hInt hN hwa hfin L hL V hV e hecompat hebij v hv t ht
  obtain ⟨_, _, hc', hord'⟩ := Z.exists_orderOfVanishingSection_eq_ordTotalFracInt_chartRatio
    B S hS hdec hInt hN hwa hfin L' hL' V hV e' hecompat' hebij' v hv _ ht'
  refine hord'.trans (Eq.trans ?_ hord.symm)
  congr 1
  exact congrArg _ hratio

end Module

/-! ### Along an isomorphism of algebraic spaces -/

section Iso

variable {X X' : AlgebraicSpaces B S hS} (φ : X ≅ X')

/-- Pullbacks of meromorphic functions are defined along an isomorphism of algebraic spaces,
which is étale, hence flat. -/
theorem pullbacksMeromorphicSections_of_iso :
    PullbacksMeromorphicSections B S hS φ.hom.hom :=
  pullbacksMeromorphicSections_of_flat B S hS _
    (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS φ.hom.hom))

variable (hdec : IsDecentSpace B S hS X.1) (hdec' : IsDecentSpace B S hS X'.1)
    (hInt : IsIntegralSpace B S hS X.1) (hInt' : IsIntegralSpace B S hS X'.1)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hN' : HasEtaleLocalProperty B S hS X'.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN hInt' hN' in
/-- **The order of vanishing is invariant under pullback along an isomorphism of algebraic
spaces.** Let `φ : X ≅ X'` be an isomorphism of decent, locally Noetherian, integral algebraic
spaces, `ℒ'` an invertible `𝒪_{X'}`-module and `t'` a regular meromorphic section of `ℒ'`. Let
`Z ⊂ X` and `Z' ⊂ X'` be prime divisors with `φ(ξ_Z) = ξ_{Z'}`. Then the order of vanishing
along `Z` of the pullback `φ^*t'` (Stacks 0ENC), a meromorphic section of `φ^*ℒ'`, is the order
of vanishing of `t'` along `Z'`, both at the canonical ratios of Stacks 0EPR.

Both orders are computed on one affine scheme: an affine chart `Q` of `X` through a point `q`
over `ξ_Z`, over which `φ^*ℒ'` is free on the pullback of a free generator of `ℒ'` over a chart
`V'` of `X'`, and `Q` itself viewed as a chart of `X'` through `φ`. The commuting square of
charts whose vertical map is the identity of `Q` computes the pullback of `t'` over `Q` as the
pullback of its ratio against the generator, and the two readings of that ratio in
`Q(𝒪_{Q, q})` agree. -/
theorem PrimeDivisor.orderOfVanishingSection_canonicalLocalRatio_pullbackMeromorphicSection_of_iso
    (M' : Modules.{u, u} B S hS X'.1 X'.2) (hM' : IsInvertibleModule (B := B) X' M')
    (t' : MeromorphicSection.{u, u} B S hS X'.1 X'.2 M')
    (ht' : IsRegularMeromorphicSection.{u, u} B S hS X'.1 X'.2 M' t')
    (Z : PrimeDivisor B S hS X.1) (Z' : PrimeDivisor B S hS X'.1)
    (hZ : pointsMap B S hS X.1 φ.hom.hom (Z.genericPoint B S hS X.1) =
      Z'.genericPoint B S hS X'.1) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X'.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X'.2 hdec') := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X'.2 hdec' hInt' hN'
    haveI : ∀ W : PrimeDivisor B S hS X'.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X'.2 hdec') := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X'.2 hdec' hInt' hN'
    haveI : ∀ W : PrimeDivisor B S hS X'.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X'.2 hdec') := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X'.2 hdec' hInt' hN'
    orderOfVanishingSection.{u, u} B S hS X.2 hdec Z ((modulePullback B S hS φ.hom).obj M')
        (pullbackMeromorphicSection B S hS φ.hom M' (pullbacksMeromorphicSections_of_iso B S hS φ)
          t')
        (Z.canonicalLocalRatio B S hS X.2 hdec ((modulePullback B S hS φ.hom).obj M')
          (modulePullbackInvertible φ.hom M' hM') hInt hN) =
      orderOfVanishingSection.{u, u} B S hS X'.2 hdec' Z' M' t'
        (Z'.canonicalLocalRatio B S hS X'.2 hdec' M' hM' hInt' hN') := by
  have hwa := localRingDimension_eq_zero_of_isIntegralSpace B S hS hInt
  have hwa' := localRingDimension_eq_zero_of_isIntegralSpace B S hS hInt'
  have hfin := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X.1 X.2 hN
  have hfin' := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X'.1 X'.2 hN'
  have hf := pullbacksMeromorphicSections_of_iso B S hS φ
  -- a free affine chart `V'` of `X'` through a point over `ξ_{Z'}`
  obtain ⟨V', -, v', e', hc', hb', hv'⟩ :=
    exists_affine_chart_free_of_point B S hS X' M' hM' (Z'.genericPoint B S hS X'.1)
  -- the same scheme as a chart of `X`, and the square over `φ`
  let U : SmallEtale B S hS X.1 :=
    (smallEtalePostcomp B S hS φ.inv (isEtale_of_isIso B S hS φ.inv.hom)).obj V'
  let d : ChartDiagram B S hS X.1 X'.1 φ.hom.hom :=
    ⟨U, V', 𝟙 _, by
      show (V'.1.hom ≫ φ.inv.hom) ≫ φ.hom.hom = yoneda.map (𝟙 _) ≫ V'.1.hom
      rw [Category.assoc, ObjectProperty.isoInv_hom_id_hom, Category.comp_id,
        CategoryTheory.Functor.map_id,
        Category.id_comp]⟩
  -- the pulled-back generator is free over a covering sieve of `U`
  obtain ⟨T, hT, hTbij⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS φ.hom M'
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM') d e' hc' hb'
  obtain ⟨Q, ι, hι, hQ, q, hq⟩ :=
    SmallEtale.exists_affine_mem_range_of_mem_topology B S hS X.1 hT v'
  -- the generator of `φ^*ℒ'` over the charts over `Q`
  let eQ : (W : SmallEtale B S hS X.1) → (W ⟶ Q) →
      ((modulePullback B S hS φ.hom).obj M').val.obj (op W) :=
    fun W k ↦ modulePullbackChartSectionRestrict B S hS φ.hom M' d (e' V' (𝟙 V')) (k ≫ ι)
  have hcQ : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ Q) (g : W' ⟶ W),
      (((modulePullback B S hS φ.hom).obj M').val.map g.op).hom (eQ W k) = eQ W' (g ≫ k) := by
    intro W W' k g
    refine (modulePullbackChartSectionRestrict_map B S hS φ.hom M' d _ (k ≫ ι) g).trans ?_
    exact congrArg _ (Category.assoc g k ι).symm
  have hbQ : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ Q),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • eQ W k :=
    fun W k ↦ hTbij ι hι W k
  -- `Q` as a chart of `X'`, over `V'`
  let Q' : SmallEtale B S hS X'.1 :=
    (smallEtalePostcomp B S hS φ.hom (isEtale_of_isIso B S hS φ.hom.hom)).obj Q
  let j : Q' ⟶ V' := ObjectProperty.homMk (CostructuredArrow.homMk
    ((SmallEtale.toOver B S hS X.1).map ι) (by
      show yoneda.map ((SmallEtale.toOver B S hS X.1).map ι) ≫ V'.1.hom = Q.1.hom ≫ φ.hom.hom
      have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map ι) ≫ U.1.hom = Q.1.hom :=
        ((SmallEtale.inclusion B S hS X.1).map ι).w
      rw [← hw]
      show _ = yoneda.map _ ≫ (V'.1.hom ≫ φ.inv.hom) ≫ φ.hom.hom
      rw [Category.assoc, ObjectProperty.isoInv_hom_id_hom, Category.comp_id]
      rfl))
  let eQ' : (W : SmallEtale B S hS X'.1) → (W ⟶ Q') → M'.val.obj (op W) :=
    fun W k ↦ e' W (k ≫ j)
  have hcQ' : ∀ (W W' : SmallEtale B S hS X'.1) (k : W ⟶ Q') (g : W' ⟶ W),
      (M'.val.map g.op).hom (eQ' W k) = eQ' W' (g ≫ k) := fun W W' k g ↦
    (hc' W W' (k ≫ j) g).trans (congrArg (e' W') (Category.assoc g k j).symm)
  have hbQ' : ∀ (W : SmallEtale B S hS X'.1) (k : W ⟶ Q'),
      Function.Bijective fun r : chartRing B S hS X'.1 X'.2 W ↦ r • eQ' W k :=
    fun W k ↦ hb' W (k ≫ j)
  -- the square over `φ` whose vertical map is the identity of `Q`
  let d₂ : ChartDiagram B S hS X.1 X'.1 φ.hom.hom :=
    ⟨Q, Q', 𝟙 _, by
      show Q.1.hom ≫ φ.hom.hom = yoneda.map (𝟙 _) ≫ (Q.1.hom ≫ φ.hom.hom)
      rw [CategoryTheory.Functor.map_id, Category.id_comp]⟩
  -- the points
  have hptU : chartSchemeToPoints B S hS X.1 U v' = Z.genericPoint B S hS X.1 := by
    have h := chartSchemeToPoints_map_chartDiagram B S hS d v'
    change chartSchemeToPoints B S hS X'.1 V' ((BigFppfOver.toScheme B S hS).map (𝟙 _) v') = _
      at h
    have hid : (BigFppfOver.toScheme B S hS).map
        (𝟙 ((SmallEtale.toOver B S hS X'.1).obj V')) v' = v' := by simp
    rw [hid, hv', ← hZ] at h
    exact ((bijective_pointsMap_of_isIso B S hS φ.hom.hom).1 h).symm
  have hvQ : chartSchemeToPoints B S hS X.1 Q q = Z.genericPoint B S hS X.1 := by
    rw [← chartSchemeToPoints_map B S hS X.1 ι q, hq, hptU]
  have hvQ' : chartSchemeToPoints B S hS X'.1 Q' q = Z'.genericPoint B S hS X'.1 := by
    rw [← chartSchemeToPoints_map B S hS X'.1 j q, ← hv']
    exact congrArg (chartSchemeToPoints B S hS X'.1 V') hq
  -- the generator of `φ^*ℒ'` over `Q` is the pullback of the generator of `ℒ'` over `Q'`
  have hgen : (modulePullbackChartFMap B S hS φ.hom M').app d₂ (eQ' Q' (𝟙 Q')) = eQ Q (𝟙 Q) := by
    have h₁ : eQ' Q' (𝟙 Q') = (M'.val.map j.op).hom (e' V' (𝟙 V')) :=
      (congrArg (e' Q') (by simp)).trans (hc' V' Q' (𝟙 V') j).symm
    rw [h₁]
    exact (modulePullbackChartFMap B S hS φ.hom M').naturality d d₂ (𝟙 Q ≫ ι) j
      (by simp [d, d₂]; rfl) (e' V' (𝟙 V'))
  -- the two chart ratios
  have ht := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS φ.hom hf M'
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM') t' ht'
  have hratio : chartRatio B S hS X.1 X.2 ((modulePullback B S hS φ.hom).obj M') Q eQ hcQ hbQ
        (pullbackMeromorphicSection B S hS φ.hom M' hf t') =
      chartMeromorphicPullbackHom B S hS φ.hom hf d₂
        (chartRatio B S hS X'.1 X'.2 M' Q' eQ' hcQ' hbQ' t') := by
    refine chartRatio_eq_of_eval_eq B S hS X.1 X.2 _ Q eQ hcQ hbQ _ _ ?_
    refine (pullbackMeromorphicSection_eval_chartDiagram B S hS φ.hom M' hf t' d₂ _
      (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X'.1 X'.2 M' Q' eQ' hcQ' hbQ'
        t')).trans ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2 _ Q) ?_
    refine (chartPullbackMeromorphicSectionsSheaf_tmul B S hS φ.hom M' hf d₂ _ _).trans ?_
    rw [hgen]
    rfl
  -- the two readings at `q` agree
  have hK := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin Q hQ
  have hK' := isFractionRing_meromorphicFunctionSheaf_obj B S hS X' hwa' hfin' Q' hQ
  let pb : (meromorphicFunctionSheaf B S hS X'.1 X'.2).obj.obj (op Q') →+*
      (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op Q) :=
    chartMeromorphicPullbackHom B S hS φ.hom hf d₂
  have hread : (chartPointMeromorphicMap B S hS X Q hQ hK q).comp pb =
      chartPointMeromorphicMap B S hS X' Q' hQ hK' q := by
    refine IsLocalization.ringHom_ext
      (nonZeroDivisors ((structurePresheaf B S hS X'.1).obj (op Q'))) ?_
    refine RingHom.ext fun r ↦ ?_
    have h₁ : pb (algebraMap _ _ r) =
        algebraMap ((structurePresheaf B S hS X.1).obj (op Q))
          ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op Q))
          (chartDiagramRestrict B S hS φ.hom d₂ r) :=
      RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS φ.hom hf d₂) r
    have h₂ : chartDiagramRestrict B S hS φ.hom d₂ r = r := by
      show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝟙 _)).op).hom r = r
      simp only [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
      rfl
    show chartPointMeromorphicMap B S hS X Q hQ hK q (pb (algebraMap _ _ r)) =
      chartPointMeromorphicMap B S hS X' Q' hQ hK' q (algebraMap _ _ r)
    rw [h₁, h₂]
    exact (chartPointMeromorphicMap_algebraMap B S hS X Q hQ hK q r).trans
      (chartPointMeromorphicMap_algebraMap B S hS X' Q' hQ hK' q r).symm
  -- both orders are the order of the same element of `Q(𝒪_{Q, q})`
  obtain ⟨_, _, hc, hord⟩ := Z.exists_orderOfVanishingSection_eq_ordTotalFracInt_chartRatio B S hS
    hdec hInt hN hwa hfin ((modulePullback B S hS φ.hom).obj M')
    (modulePullbackInvertible φ.hom M' hM') Q hQ eQ hcQ hbQ q hvQ _ ht
  obtain ⟨_, _, hc', hord'⟩ := Z'.exists_orderOfVanishingSection_eq_ordTotalFracInt_chartRatio
    B S hS hdec' hInt' hN' hwa' hfin' M' hM' Q' hQ eQ' hcQ' hbQ' q hvQ' t' ht'
  refine hord.trans (Eq.trans ?_ hord'.symm)
  congr 1
  rw [hratio]
  exact RingHom.congr_fun hread _

end Iso

end AlgebraicGeometry.Space

end
