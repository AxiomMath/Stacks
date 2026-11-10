module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionChartOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorChart

/-!
# Pulled-back sections have order zero over the generic point

Let `f : X ⟶ Y` be a morphism of algebraic spaces along which meromorphic sections pull back,
with `X` decent, locally Noetherian and integral and `Y` integral and locally Noetherian, let `ℒ`
be an invertible `𝒪_Y`-module and `s` a regular meromorphic section of `ℒ`, and let `Z ⊆ X` be a
prime divisor whose generic point lies over the generic point of `Y`. Then

`ord_{Z, f^*ℒ}(f^*s) = 0`.

## Main results

* `orderOfVanishingSection_pullbackMeromorphicSection_eq_zero_of_genericPoint`: the order of a
  pulled-back regular meromorphic section along a prime divisor over the generic point is zero.
* `properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop`: for
  `g : W ⟶ W'` with `dim_δ(W) = dim_δ(W') + 1`, the pushforward `g_* div_{g^*ℳ}(g^*t)` is zero.

All names are in the namespace `AlgebraicGeometry.Space`.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicFunctionAlgebra

section GenericPoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}
    (hXdec : IsDecentSpace B S hS X.1) (hXint : IsIntegralSpace B S hS X.1)
    (hXN : HasEtaleLocalProperty B S hS X.1 (fun W : Scheme.{u} ↦ IsLocallyNoetherian W))
    (hYint : IsIntegralSpace B S hS Y.1)
    (hYN : HasEtaleLocalProperty B S hS Y.1 (fun W : Scheme.{u} ↦ IsLocallyNoetherian W))

include hXdec hXint hXN hYN in
/-- **A pulled-back meromorphic section has order zero along a prime divisor over the generic
point.** Let `f : X ⟶ Y` be a morphism of algebraic spaces along which meromorphic sections pull
back, with `X` decent, locally Noetherian and integral and `Y` integral and locally Noetherian,
let `ℒ` be an invertible `𝒪_Y`-module with a regular meromorphic section `s`, and let `Z ⊆ X` be
a prime divisor whose generic point is carried to the generic point of `Y`. Then
`ord_{Z, f^*ℒ}(f^*s) = 0`, the order being read at the canonical ratio of Stacks 0EPR. -/
theorem orderOfVanishingSection_pullbackMeromorphicSection_eq_zero_of_genericPoint (f : X ⟶ Y)
    (hfm : PullbacksMeromorphicSections B S hS f.hom) (Z : PrimeDivisor B S hS X.1)
    (hZ : pointsMap B S hS X.1 f.hom (Z.genericPoint B S hS X.1) =
      genericPoint B S hS Y.2 hYint)
    (L : Modules.{u, u} B S hS Y.1 Y.2) (hL : IsInvertibleModule Y L)
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L s) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hXdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hXdec hXint hXN
    orderOfVanishingSection.{u, u} B S hS X.2 hXdec Z
        ((modulePullback B S hS f).obj L) (pullbackMeromorphicSection B S hS f L hfm s)
        (Z.canonicalLocalRatio B S hS X.2 hXdec ((modulePullback B S hS f).obj L)
          (modulePullbackInvertible f L hL) hXint hXN) = 0 := by
  have hwaY := localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isIntegralSpace
    B S hS Y.2 hYint
  have hfinY := hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y.1 Y.2 hYN
  obtain ⟨d, u, hU, hV, hu, e, hecompat, hefree⟩ :=
    exists_affine_chartDiagram_generator_through B S hS f L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) (Z.genericPoint B S hS X.1)
  set g := (BigFppfOver.toScheme B S hS).map d.g with hgdef
  set v := g.base u with hvdef
  have hv : chartSchemeToPoints B S hS Y.1 d.V v = genericPoint B S hS Y.2 hYint := by
    rw [hvdef, hgdef, chartSchemeToPoints_map_chartDiagram B S hS d u, hu, hZ]
  have hvgen : v ∈ genericPoints (chartScheme d.V) :=
    (chartSchemeToPoints_eq_genericPoint_iff B S hS Y.2 hYint d.V v).1 hv
  have : _root_.IsReduced ((chartScheme d.V).presheaf.stalk v) :=
    isReduced_stalk_chartScheme_of_isIntegralSpace Y.2 hYint d.V v
  have : Ring.KrullDimLE 0 ((chartScheme d.V).presheaf.stalk v) :=
    Ring.krullDimLE_iff.mpr (by
      rw [(ringKrullDim_stalk_eq_zero_iff_mem_genericPoints (chartScheme d.V) v).2 hvgen]
      exact_mod_cast le_rfl)
  have hfield : IsField ((chartScheme d.V).presheaf.stalk v) :=
    Ring.KrullDimLE.isField_of_isReduced
  have : IsDomain ((chartScheme d.V).presheaf.stalk v) := hfield.isDomain
  have hunit : ∀ x : (chartScheme d.V).presheaf.stalk v, x ≠ 0 → IsUnit x := fun x hx => by
    obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
    exact IsUnit.of_mul_eq_one y hy
  have hφ : ((chartScheme d.V).presheaf.stalk v)⁰ ≤
      ((chartScheme d.U).presheaf.stalk u)⁰.comap (g.stalkMap u).hom := fun x hx =>
    ((hunit x (nonZeroDivisors.ne_zero hx)).map (g.stalkMap u).hom).mem_nonZeroDivisors
  have : IsLocallyNoetherian (chartScheme d.U) :=
    isLocallyNoetherian_chartScheme B S hS (X := X) hXN d.U
  have : Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u) :=
    Z.krullDimLE_chartStalk B S hS X.2 hXdec d.U u hu
  obtain ⟨hc, hord⟩ := orderOfVanishingSection_pullbackMeromorphicSection_eq_ordTotalFracInt_map
    B S hS hXdec hXint hXN f hfm hwaY hfinY Z L hL s hs d hU hV e hecompat hefree u hu hφ
  refine hord.trans ?_
  set cv := chartPointMeromorphicMap B S hS Y d.V hV
    (isFractionRing_meromorphicFunctionSheaf_obj B S hS Y hwaY hfinY d.V hV) v
    (chartRatio B S hS Y.1 Y.2 L d.V e hecompat hefree s) with hcvdef
  have hcvu : IsUnit cv := (isUnit_chartRatio_of_isRegularMeromorphicSection B S hS Y hwaY hfinY
    L d.V hV e hecompat hefree s hs).map _
  obtain ⟨w, hw⟩ := (IsFractionRing.surjective_iff_isField
    (R := (chartScheme d.V).presheaf.stalk v)
    (K := FractionRing ((chartScheme d.V).presheaf.stalk v))).2 hfield cv
  have hwu : IsUnit w := by
    refine hunit w fun hw0 => hcvu.ne_zero ?_
    rw [← hw, hw0, map_zero]
  have hmap : IsLocalization.map (T := ((chartScheme d.U).presheaf.stalk u)⁰)
      (FractionRing ((chartScheme d.U).presheaf.stalk u)) (g.stalkMap u).hom hφ cv =
      algebraMap _ (FractionRing ((chartScheme d.U).presheaf.stalk u)) ((g.stalkMap u).hom w) := by
    rw [← hw]
    exact IsLocalization.map_eq _ _
  have hwu' := hwu.map (g.stalkMap u).hom
  rw [Ring.ordTotalFracInt_congr _ hc (hmap ▸ hc) hmap]
  exact Ring.ordTotalFracInt_algebraMap_of_isUnit hwu' _

end GenericPoint

/-! ### The pushforward of the divisor of a pulled-back section when the dimension drops -/

section DimensionDrop

variable (D : BaseSpaceDimensionSituation.{u})
    {W W' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sW : W ⟶ D.space) (hW : D.IsGood sW) (hWint : IsIntegralSpace D.site D.base D.base_mem W)
    (sW' : W' ⟶ D.space) (hW' : D.IsGood sW')
    (hW'int : IsIntegralSpace D.site D.base D.base_mem W')
    (g : (⟨W, hW.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨W', hW'.1⟩)
    (hg : g.hom ≫ sW' = sW)

include hWint in
/-- **The divisor of a pulled-back section pushes forward to zero when the dimension drops.**
Let `g : W ⟶ W'` be a quasi-compact morphism over the base of good integral algebraic spaces,
along which meromorphic sections pull back, with `dim_δ(W) = k + 1` and `dim_δ(W') = k`. Let `ℳ`
be an invertible `𝒪_{W'}`-module and `t` a regular meromorphic section of `ℳ`. Then

`g_* div_{g^*ℳ}(g^*t) = 0`   in `Z_k(W')`,

the Weil divisor of Stacks 0EQE being taken at the canonical choices. -/
theorem properCyclePushforward_canonicalDivisorCycleAt_pullback_eq_zero_of_deltaValue_drop
    (hgqc : IsQuasiCompact D.site D.base D.base_mem g.hom)
    (hfm : PullbacksMeromorphicSections D.site D.base D.base_mem g.hom) (k : ℤ)
    (hk : deltaDimensionClosed D sW hW Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (hW'd : D.deltaValue sW' (genericPoint D.site D.base D.base_mem hW'.1 hW'int) = k)
    (M : Modules.{u, u} D.site D.base D.base_mem W' hW'.1)
    (hM : IsInvertibleModule (⟨W', hW'.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem W' hW'.1 M)
    (ht : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W' hW'.1 M t)
    (hgt : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem W hW.1
      ((modulePullback D.site D.base D.base_mem g).obj M)
      (pullbackMeromorphicSection D.site D.base D.base_mem g M hfm t)) :
    properCyclePushforward D sW hW sW' hW' hg hgqc k
        (canonicalDivisorCycleAt D sW hW hWint ((modulePullback D.site D.base D.base_mem g).obj M)
          (modulePullbackInvertible g M hM)
          (pullbackMeromorphicSection D.site D.base D.base_mem g M hfm t) hgt hk) = 0 := by
  classical
  have hdec : IsDecentSpace D.site D.base D.base_mem W := D.isDecentSpace_of_isGood sW hW
  have hdec' : IsDecentSpace D.site D.base D.base_mem W' := D.isDecentSpace_of_isGood sW' hW'
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sW hW
  have hN' := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sW' hW'
  set ξ' := genericPoint D.site D.base D.base_mem hW'.1 hW'int with hξ'
  set c := canonicalDivisorCycleAt D sW hW hWint ((modulePullback D.site D.base D.base_mem g).obj M)
    (modulePullbackInvertible g M hM)
    (pullbackMeromorphicSection D.site D.base D.base_mem g M hfm t) hgt hk with hcdef
  refine Subtype.ext (funext fun Z' => ?_)
  rw [properPushforward_apply]
  change (∑ᶠ Z, (c : IntegralClosedSubspace D.site D.base D.base_mem W → ℤ) Z *
    properCycleMult D sW hW sW' hW' g.hom Z Z') = 0
  refine finsum_eq_zero_of_forall_eq_zero fun Z => ?_
  by_contra hZ
  have hcZ := left_ne_zero_of_mul hZ
  obtain ⟨himg, hdeg⟩ := (properCycleMult_ne_zero_iff D sW hW sW' hW' g.hom Z Z').1
    (right_ne_zero_of_mul hZ)
  have hδeq := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sW hW sW' hW' g.hom hdeg
  have hδZ : deltaDimension D sW Z = k := c.2.2 Z hcZ
  have hζ : Z'.ambientGenericPoint D.site D.base D.base_mem =
      pointsMap D.site D.base D.base_mem W g.hom
        (Z.ambientGenericPoint D.site D.base D.base_mem) := by
    rw [← himg]
    exact IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem
      hW.1 hW'.1 _ g.hom Z
  have hδζ : D.deltaValue sW' (pointsMap D.site D.base D.base_mem W g.hom
      (Z.ambientGenericPoint D.site D.base D.base_mem)) = k := by
    rw [← hζ]
    change deltaDimension D sW' Z' = k
    rw [← himg, hδeq, hδZ]
  have _ : T0Space (points D.site D.base D.base_mem W') :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hW'.1 hdec'
  have _ : T0Space (points D.site D.base D.base_mem W) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hW.1 hdec
  have := fun W₀ : PrimeDivisor D.site D.base D.base_mem W =>
    W₀.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hW.1 hdec hWint hN
  have := fun W₀ : PrimeDivisor D.site D.base D.base_mem W =>
    W₀.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hW.1 hdec hWint hN
  have := fun W₀ : PrimeDivisor D.site D.base D.base_mem W =>
    W₀.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hW.1 hdec hWint hN
  have hqz : pointsMap D.site D.base D.base_mem W g.hom
      (Z.ambientGenericPoint D.site D.base D.base_mem) = ξ' := by
    by_contra hne
    have hspec : ξ' ⤳ pointsMap D.site D.base D.base_mem W g.hom
        (Z.ambientGenericPoint D.site D.base D.base_mem) :=
      (isGenericPoint_genericPoint D.site D.base D.base_mem hW'.1 hW'int).specializes
        (Set.mem_univ _)
    have hlt := (deltaDimensionFunction D sW' hW').strictAnti_specializes hspec (Ne.symm hne)
    rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply, hδζ, hW'd] at hlt
    exact lt_irrefl _ hlt
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hW.1 Z) = 1 := by
    by_contra hcod
    exact hcZ (divisorCycleCoefficients_of_codimension_ne_one D sW hW hdec _ _ _ hcod)
  set Z'' := Z.toPrimeDivisor D.site D.base D.base_mem hW.1 hcod with hZ''
  have hgenZ'' : Z''.genericPoint D.site D.base D.base_mem W =
      Z.ambientGenericPoint D.site D.base D.base_mem :=
    (Z''.isGenericPoint_genericPoint D.site D.base D.base_mem W).eq
      (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hW.1)
  have hord := orderOfVanishingSection_pullbackMeromorphicSection_eq_zero_of_genericPoint
    D.site D.base D.base_mem (X := ⟨W, hW.1⟩) (Y := ⟨W', hW'.1⟩) hdec hWint hN hW'int hN' g hfm
    Z'' (by rw [hgenZ'']; exact hqz) M hM t ht
  refine hcZ ?_
  change divisorCycleCoefficients D sW hW hdec _ _ _ Z = 0
  rw [divisorCycleCoefficients_of_codimension_eq_one D sW hW hdec _ _ _ hcod]
  exact hord

end DimensionDrop

end AlgebraicGeometry.Space

end
