module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoChartOrderTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGeneratorSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentGenericFreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneratorMultiple

/-!
# Free generators of an inverse image over a chart, from free generators over the postcomposed
chart

Let `f : X ⟶ Y` be étale, let `𝒩` be an invertible `𝒪_Y`-module and let `V` be an étale chart of
`X` over whose postcomposition `(smallEtalePostcomp f).obj V` the module `𝒩` is free on a
compatible family `eM`.  This file produces the matched compatible family of free generators of
`f^*𝒩` over `V` that
`AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq` asks
of its caller, together with the compatibility at the identity chart that the same theorem's
hypothesis `heq` records.

## Main definitions

* `AlgebraicGeometry.Space.postcompChartPullbackGenerator`: the family, namely the inverse image
  of `eM` along `AlgebraicGeometry.Space.etaleSmallPostcompChartDiagram` restricted along the chart
  morphism.

## Main results

* `AlgebraicGeometry.Space.postcompChartPullbackGenerator_compat`: it is compatible with
  restriction.
* `AlgebraicGeometry.Space.postcompChartPullbackGenerator_self`: its value at the identity chart
  morphism is the inverse image of the value of `eM` at the identity chart, which is the
  hypothesis `heq` of the transport theorem.
* `AlgebraicGeometry.Space.bijective_smul_postcompChartPullbackGenerator`: it freely generates
  `f^*𝒩` over every chart over `V`.

## Implementation notes

Nothing here needs the chart form of Stacks 03LW — the bijectivity of the chart component of the
unit of Stacks 03D7 — which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoChartOrderTransport` record as
unavailable.  What is used is only the *forward* statement that the inverse image of a free
generator freely generates the inverse image, locally on a covering sieve
(`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`), descended to
the chart itself by `AlgebraicGeometry.Space.bijective_smul_of_sieve`.  Since the family is
*defined* as an inverse image, the matching hypothesis `heq` is not an assumption at all: it is
the restriction map at the identity, which is the identity.

This is the pattern of
`AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartGenerator` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.BaseChangeChartGenerator`, carried out at
`AlgebraicGeometry.Space.etaleSmallPostcompChartDiagram` instead of at the base-change square.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : SmallEtale B S hS X.1)
    (eM : (W : SmallEtale B S hS Y.1) →
      (W ⟶ (smallEtalePostcomp B S hS f hf).obj V) → M.val.obj (op W))

/-- The compatible family of free generators of `f^*𝒩` over the charts over `V` attached to a
compatible family `eM` of free generators of `𝒩` over the postcomposed chart: the inverse image
of `eM` at the identity chart along
`AlgebraicGeometry.Space.etaleSmallPostcompChartDiagram`, restricted along the chart morphism. -/
def postcompChartPullbackGenerator (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ V) :
    ((modulePullback B S hS f).obj M).val.obj (op W₁) :=
  modulePullbackChartSectionRestrict B S hS f M (etaleSmallPostcompChartDiagram B S hS f hf V)
    (eM ((smallEtalePostcomp B S hS f hf).obj V)
      (𝟙 ((smallEtalePostcomp B S hS f hf).obj V))) k

/-- The family is compatible with restriction, because restricting an inverse image twice
composes the two chart morphisms. -/
theorem postcompChartPullbackGenerator_compat (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ V)
    (g : W₂ ⟶ W₁) :
    (((modulePullback B S hS f).obj M).val.map g.op).hom
        (postcompChartPullbackGenerator B S hS f hf M V eM W₁ k) =
      postcompChartPullbackGenerator B S hS f hf M V eM W₂ (g ≫ k) :=
  modulePullbackChartSectionRestrict_map B S hS f M
    (etaleSmallPostcompChartDiagram B S hS f hf V) _ k g

/-- **The matching condition at the identity chart.**  The value of the family at the identity
chart morphism is the inverse image of the value of `eM` at the identity chart, which is the
hypothesis `heq` of
`AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq`. -/
theorem postcompChartPullbackGenerator_self :
    postcompChartPullbackGenerator B S hS f hf M V eM V (𝟙 V) =
      (modulePullbackChartFMap B S hS f M).app (etaleSmallPostcompChartDiagram B S hS f hf V)
        (eM ((smallEtalePostcomp B S hS f hf).obj V)
          (𝟙 ((smallEtalePostcomp B S hS f hf).obj V))) := by
  refine Eq.trans (modulePullbackChartSectionRestrict_eq B S hS f M
    (etaleSmallPostcompChartDiagram B S hS f hf V) _ (𝟙 V)) ?_
  exact CategoryTheory.congr_fun
    (((modulePullback B S hS f).obj M).val.presheaf.map_id (op V)) _

include hf in
/-- **The family freely generates `f^*𝒩` over every chart over `V`.**  The inverse image of a
free generator freely generates the inverse image on a covering sieve of the chart
(`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`), and freeness
descends from a covering sieve to the chart itself
(`AlgebraicGeometry.Space.bijective_smul_of_sieve`).  No bijectivity of the chart component of
the unit of Stacks 03D7 is used. -/
theorem bijective_smul_postcompChartPullbackGenerator
    (hM : IsInvertibleModule (B := B) Y M)
    (hMcompat : ∀ (W W' : SmallEtale B S hS Y.1)
      (k : W ⟶ (smallEtalePostcomp B S hS f hf).obj V) (g : W' ⟶ W),
      (M.val.map g.op).hom (eM W k) = eM W' (g ≫ k))
    (hMfree : ∀ (W : SmallEtale B S hS Y.1)
      (k : W ⟶ (smallEtalePostcomp B S hS f hf).obj V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k)
    (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ V) :
    Function.Bijective fun r : chartRing B S hS X.1 X.2 W₁ ↦
      r • postcompChartPullbackGenerator B S hS f hf M V eM W₁ k := by
  obtain ⟨T, hT, hloc⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS f M
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM)
    (etaleSmallPostcompChartDiagram B S hS f hf V) eM hMcompat hMfree
  refine bijective_smul_of_sieve B S hS X ((modulePullback B S hS f).obj M) W₁ _
    (T.pullback k) ((SmallEtale.topology B S hS X.1).pullback_stable k hT) fun W₂ j hj => ?_
  have hEq : (chartRestrictLinear ((modulePullback B S hS f).obj M) j)
        (postcompChartPullbackGenerator B S hS f hf M V eM W₁ k) =
      modulePullbackChartSectionRestrict B S hS f M (etaleSmallPostcompChartDiagram B S hS f hf V)
        (eM ((smallEtalePostcomp B S hS f hf).obj V)
          (𝟙 ((smallEtalePostcomp B S hS f hf).obj V))) (𝟙 W₂ ≫ (j ≫ k)) := by
    rw [Category.id_comp]
    exact postcompChartPullbackGenerator_compat B S hS f hf M V eM W₁ W₂ k j
  rw [hEq]
  exact hloc (j ≫ k) hj W₂ (𝟙 W₂)

/-! ### The order of vanishing across an isomorphism, with no chart data asked of the caller -/

section Transport

/-- The transport of the order of vanishing across an isomorphism, with the chart of `X` and the
chart of `Y` presented separately together with the identification of the second as the
postcomposition of the first.  This is
`AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq` with
the family of free generators of `e^*𝒩` supplied by
`AlgebraicGeometry.Space.postcompChartPullbackGenerator`, so that only the data on the `Y` side
is asked for. -/
theorem orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq_of_postcompChart
    (hXdec : IsDecentSpace B S hS X.1) (hYdec : IsDecentSpace B S hS Y.1)
    (Z : PrimeDivisor B S hS X.1) (e : X ≅ Y)
    (hXint : IsIntegralSpace B S hS X.1) (hYint : IsIntegralSpace B S hS Y.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hYN : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : IsInvertibleModule (B := B) Y M)
    (τ : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (hτ : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 M τ)
    (V : SmallEtale B S hS X.1) (W' : SmallEtale B S hS Y.1)
    (hVW : (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V = W')
    (hW' : IsAffine (chartScheme W'))
    (eM : (W : SmallEtale B S hS Y.1) → (W ⟶ W') → M.val.obj (op W))
    (hMcompat : ∀ (W W'' : SmallEtale B S hS Y.1) (k : W ⟶ W') (g : W'' ⟶ W),
      (M.val.map g.op).hom (eM W k) = eM W'' (g ≫ k))
    (hMfree : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ W'),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k)
    (v : chartScheme V)
    (hv : chartSchemeToPoints B S hS X.1 V v = Z.genericPoint B S hS X.1) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    orderOfVanishingSection.{u, u} B S hS Y.2 hYdec
          (Z.pushforwardOfIso B S hS X.2 Y.2 hYdec ((ObjectProperty.ι _).mapIso e)) M τ
          ((Z.pushforwardOfIso B S hS X.2 Y.2 hYdec
            ((ObjectProperty.ι _).mapIso e)).canonicalLocalRatio B S hS Y.2 hYdec M hM
              hYint hYN) =
      orderOfVanishingSection.{u, u} B S hS X.2 hXdec Z
        ((modulePullback B S hS e.hom).obj M)
        (pullbackMeromorphicSection B S hS e.hom M
          (pullbacksMeromorphicSections_of_flat B S hS e.hom.hom
            (isFlat_of_isEtale B S hS (isEtale_hom_of_isIso B S hS e.hom))) τ)
        (Z.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS e.hom).obj M)
          (modulePullbackInvertible e.hom M hM) hXint hXN) := by
  subst hVW
  have : IsLocallyNoetherian (chartScheme V) := isLocallyNoetherian_chartScheme B S hS X hXN V
  have : IsNoetherianRing ((chartScheme V).presheaf.stalk v) := inferInstance
  have : Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v) :=
    Z.krullDimLE_chartStalk B S hS X.2 hXdec V v hv
  exact orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq B S hS hXdec hYdec Z e
    hXint hYint hXN hYN M hM τ hτ V hW' hW' eM hMcompat hMfree
    (postcompChartPullbackGenerator B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom) M V eM)
    (postcompChartPullbackGenerator_compat B S hS e.hom
      (isEtale_hom_of_isIso B S hS e.hom) M V eM)
    (bijective_smul_postcompChartPullbackGenerator B S hS e.hom
      (isEtale_hom_of_isIso B S hS e.hom) M V eM hM hMcompat hMfree)
    (postcompChartPullbackGenerator_self B S hS e.hom
      (isEtale_hom_of_isIso B S hS e.hom) M V eM) v hv

/-- Postcomposing with an isomorphism and with its inverse returns the chart it started from:
postcomposition changes nothing but the structure morphism, and the two structure morphisms
differ by the composite of the isomorphism with its inverse. -/
theorem smallEtalePostcomp_obj_smallEtalePostcomp_obj_inv (e : X ≅ Y)
    (W : SmallEtale B S hS Y.1) :
    (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj
        ((smallEtalePostcomp B S hS e.symm.hom
          (isEtale_hom_of_isIso B S hS e.symm.hom)).obj W) = W := by
  have hid : e.symm.hom.hom ≫ e.hom.hom = 𝟙 Y.1 :=
    ((ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F).mapIso e).inv_hom_id
  have h : ((smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj
        ((smallEtalePostcomp B S hS e.symm.hom
          (isEtale_hom_of_isIso B S hS e.symm.hom)).obj W)).1.hom = W.1.hom :=
    (Category.assoc W.1.hom e.symm.hom.hom e.hom.hom).trans
      ((congrArg (W.1.hom ≫ ·) hid).trans (Category.comp_id _))
  exact ObjectProperty.FullSubcategory.ext ((CostructuredArrow.eq_mk _).trans
    ((congrArg CostructuredArrow.mk h).trans (CostructuredArrow.eq_mk W.1).symm))

/-- **The order of vanishing of a regular meromorphic section along a prime divisor is carried by
an isomorphism of spaces, with nothing asked of the caller.**  Let `e : X ≅ Y` be an isomorphism
of decent, locally Noetherian, integral algebraic spaces over `S`, let `Z` be a prime divisor of
`X`, let `𝒩` be an invertible `𝒪_Y`-module and `τ` a regular meromorphic section of it.  Then

`ord_{e(Z), 𝒩}(τ) = ord_{Z, e^*𝒩}(e^*τ)`

at the canonical ratios of Stacks 0EPR on both sides.

This is
`AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq` with
its chart data discharged.  The chart is produced on `Y`, where the module lives, by
`AlgebraicGeometry.Space.exists_affine_chart_isUnit_chartRatio` at the generic point of the
image of `Z`; it is carried back to a chart of `X` by postcomposition with `e⁻¹`, which returns
it on the nose (`AlgebraicGeometry.Space.smallEtalePostcomp_obj_smallEtalePostcomp_obj_inv`);
and the matched family of free generators of `e^*𝒩` is
`AlgebraicGeometry.Space.postcompChartPullbackGenerator`, the inverse image of the family on
`Y`.  The two ring-theoretic instances on the stalk of the chart scheme at the chosen point are
`AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme` and
`AlgebraicGeometry.Space.PrimeDivisor.krullDimLE_chartStalk`. -/
theorem orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq_unconditional
    (hXdec : IsDecentSpace B S hS X.1) (hYdec : IsDecentSpace B S hS Y.1)
    (Z : PrimeDivisor B S hS X.1) (e : X ≅ Y)
    (hXint : IsIntegralSpace B S hS X.1) (hYint : IsIntegralSpace B S hS Y.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hYN : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : IsInvertibleModule (B := B) Y M)
    (τ : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)
    (hτ : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 M τ) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    haveI : ∀ W : PrimeDivisor B S hS Y.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS Y.2 hYdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS Y.2 hYdec hYint hYN
    orderOfVanishingSection.{u, u} B S hS Y.2 hYdec
          (Z.pushforwardOfIso B S hS X.2 Y.2 hYdec ((ObjectProperty.ι _).mapIso e)) M τ
          ((Z.pushforwardOfIso B S hS X.2 Y.2 hYdec
            ((ObjectProperty.ι _).mapIso e)).canonicalLocalRatio B S hS Y.2 hYdec M hM
              hYint hYN) =
      orderOfVanishingSection.{u, u} B S hS X.2 hXdec Z
        ((modulePullback B S hS e.hom).obj M)
        (pullbackMeromorphicSection B S hS e.hom M
          (pullbacksMeromorphicSections_of_flat B S hS e.hom.hom
            (isFlat_of_isEtale B S hS (isEtale_hom_of_isIso B S hS e.hom))) τ)
        (Z.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS e.hom).obj M)
          (modulePullbackInvertible e.hom M hM) hXint hXN) := by
  have hwaY := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Y.2 hYint
  have hfinY := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y.1 Y.2 hYN
  obtain ⟨W', hW', w, eM, hcM, hfM, -, -, -, hw, -⟩ :=
    exists_affine_chart_isUnit_chartRatio B S hS Y hwaY hfinY M M hM hM τ hτ τ hτ
      ((Z.pushforwardOfIso B S hS X.2 Y.2 hYdec
        ((ObjectProperty.ι _).mapIso e)).genericPoint B S hS Y.1)
  obtain ⟨V, rfl⟩ : ∃ V : SmallEtale B S hS X.1,
      (smallEtalePostcomp B S hS e.hom (isEtale_hom_of_isIso B S hS e.hom)).obj V = W' :=
    ⟨_, smallEtalePostcomp_obj_smallEtalePostcomp_obj_inv B S hS e W'⟩
  have hinj : Function.Injective
      (pointsMap B S hS X.1 ((ObjectProperty.ι _).mapIso e).hom) := by
    have h := pointsMap_comp B S hS X.1 ((ObjectProperty.ι _).mapIso e).hom
      ((ObjectProperty.ι _).mapIso e).inv
    rw [Iso.hom_inv_id, pointsMap_id] at h
    exact Function.LeftInverse.injective (g :=
      pointsMap B S hS Y.1 ((ObjectProperty.ι _).mapIso e).inv) fun x => (congrFun h x).symm
  have hv : chartSchemeToPoints B S hS X.1 V w = Z.genericPoint B S hS X.1 := by
    refine hinj ?_
    refine Eq.trans ?_ (Z.genericPoint_pushforwardOfIso B S hS X.2 Y.2 hYdec
      ((ObjectProperty.ι _).mapIso e))
    exact (chartSchemeToPoints_smallEtalePostcomp B S hS e.hom
      (isEtale_hom_of_isIso B S hS e.hom) V w).symm.trans hw
  exact orderOfVanishingSection_canonicalLocalRatio_pushforwardOfIso_eq_of_postcompChart B S hS
    hXdec hYdec Z e hXint hYint hXN hYN M hM τ hτ V _ rfl hW' eM hcM hfM w hv

end Transport

end AlgebraicGeometry.Space

end
