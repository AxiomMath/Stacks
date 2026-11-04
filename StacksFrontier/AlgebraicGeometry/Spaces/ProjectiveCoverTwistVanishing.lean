module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageVanishingOnCoveringChart
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.TwistVanishingOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist

/-!
# Vanishing of the higher direct images of high twists along a cover by a scheme

Let `p : h_{Z'} ⟶ Y` be a proper morphism from the algebraic space represented by a scheme `Z'` to
an absolutely separated algebraic space `Y`, and let `ℒ` be an ample invertible module on `Z'`.
This file proves that for every sufficiently large `d` the higher direct images of
`(ℒ^{⊗ d})ᵃ` along `p` vanish, given an affine étale chart `U` of `Y` covering the final object of
its small étale site with locally Noetherian scheme.

This is the vanishing of [Stacks, Tag 08AQ] at the Chow cover of the proof of [Stacks, Tag 08AR]:
over `U` the base change `C = Z' ×_Y U` is a scheme, proper over `U`, mapping to `Z'` by an affine
morphism because `Y` is separated ([Stacks, Tag 08GB] part (4)); so the pullback of `ℒ` is ample on
`C` ([Stacks, Tag 0892]), the high twists of it have no higher cohomology on `C` (clause (4) of
[Stacks, Tag 0B5T]), and that cohomology is the cohomology of the restriction of `(ℒ^{⊗ d})ᵃ` to
`C` on the small étale site, by the comparison
`AlgebraicGeometry.Space.representedZariskiCohomologyIso`. The vanishing over the single chart `U`
suffices, by `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_coveringChart`.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_toScheme_map_of_isAffineHom` and
  `AlgebraicGeometry.Space.isProper_toScheme_map_of_isProper`: affineness and properness of a
  morphism between represented algebraic spaces are those of the morphism of schemes.
* `AlgebraicGeometry.Space.exists_isZero_rightDerived_modulePushforward_representedModuleOf`: the
  vanishing above.

## References

* [Stacks Project, Tag 08AQ](https://stacks.math.columbia.edu/tag/08AQ)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An affine morphism between represented algebraic spaces is an affine morphism of schemes. -/
theorem isAffineHom_toScheme_map_of_isAffineHom {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (h : IsAffineHom B S hS (yoneda.map g)) :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ g).1
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V) h).2

/-- A proper morphism between represented algebraic spaces is a proper morphism of schemes. -/
theorem isProper_toScheme_map_of_isProper {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (h : IsProper B S hS (yoneda.map g)) :
    _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map g) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ g).1
    ((presheaf_isProper_iff B S hS (yoneda.map g) (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) (Functor.relativelyRepresentable.map _ g)).1 h)

/-- **The higher direct images of the high twists of an ample module along a proper morphism
from a scheme vanish.**  Let `p : h_{Z'} ⟶ Y` be proper, `Y` absolutely separated, `U` an affine
étale chart of `Y` covering the final object of the small étale site, with locally Noetherian
scheme, and `ℒ` an ample invertible module on the scheme `Z'₀` underlying `Z'`.  Then there is a
`d₀` with `R^q p_* (ℒ^{⊗ d})ᵃ = 0` for every `d ≥ d₀` and `q > 0`. -/
theorem exists_isZero_rightDerived_modulePushforward_representedModuleOf
    (hZ : B.Contains (⊤_ Scheme.{u})) {Y : AlgebraicSpaces B S hS}
    (hY : IsAbsolutelySeparated B S hS hZ Y.1) {Z' : BigFppfOver B S hS}
    (p : schemeSpace Z' ⟶ Y) (hpp : IsProper B S hS p.hom)
    (U : SmallEtale B S hS Y.1) (hUaff : IsAffineChart B S hS Y.1 U)
    [hUln : _root_.AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj U))]
    (hU : (SmallEtale.topology B S hS Y.1).CoversTop (fun _ : Unit => U))
    (L : ((BigFppfOver.toScheme B S hS).obj Z').Modules)
    [IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj Z') L]
    (hL : IsAmple ((BigFppfOver.toScheme B S hS).obj Z') L) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ q : ℕ, 0 < q →
      have := hasInjectiveResolutions_modules B S hS (schemeSpace Z').1 (schemeSpace Z').2
      IsZero (((modulePushforward B S hS p).rightDerived q).obj
        (representedModuleOf B S hS Z'
          (tensorPowModule ((BigFppfOver.toScheme B S hS).obj Z') L (d : ℤ)))) := by
  have hp : yoneda.relativelyRepresentable p.hom :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 p.hom
  set C : SmallEtale B S hS (yoneda.obj Z') := (smallBaseChange B S hS p hp).obj U
  set T := (SmallEtale.toOver B S hS (yoneda.obj Z')).obj C
  have hUaffine : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj U)) := hUaff
  -- the chart map `C₀ ⟶ Z'₀` is affine
  have haffU : IsAffineHom B S hS U.obj.hom :=
    isAffineHom_of_isAffineSpace_source_of_isAbsolutelySeparated B S hS hZ U.obj.hom
      (isAffineSpace_yoneda B S hS _ hUaff) hY
  have haffC : IsAffineHom B S hS (yoneda.map (representedEtaleChartToObject B S hS C)) := by
    have e : yoneda.map (representedEtaleChartToObject B S hS C) = hp.fst U.obj.hom :=
      yoneda_map_representedEtaleChartToObject B S hS C
    rw [e]
    exact isAffineHom_of_isPullback' B S hS (hp.isPullback U.obj.hom).flip haffU
  have haff₀ : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (representedEtaleChartToObject B S hS C)) :=
    isAffineHom_toScheme_map_of_isAffineHom B S hS _ haffC
  -- the chart scheme `C₀` is proper over `U₀`
  have hpropC : IsProper B S hS (yoneda.map (hp.snd U.obj.hom)) :=
    isProper_of_isPullback B S hS (isAlgebraicSpace_yoneda B S hS _) (schemeSpace Z').2
      (isAlgebraicSpace_yoneda B S hS _) Y.2 (hp.isPullback U.obj.hom) hpp
  have hprop₀ : _root_.AlgebraicGeometry.IsProper
      ((BigFppfOver.toScheme B S hS).map (hp.snd U.obj.hom)) :=
    isProper_toScheme_map_of_isProper B S hS _ hpropC
  open Stacks.AlgebraicGeometry.ProperAmpleCohomology in
  obtain ⟨d₀, hd₀⟩ :=
    @exists_isZero_rightDerived_pullback_tensorPowModule
      _ _ _ ((BigFppfOver.toScheme B S hS).map (representedEtaleChartToObject B S hS C)) haff₀
      ((BigFppfOver.toScheme B S hS).map (hp.snd U.obj.hom)) hprop₀ hUaffine hUln L _ hL
  refine ⟨d₀, fun d hd q hq => ?_⟩
  have := hasInjectiveResolutions_modules B S hS (schemeSpace Z').1 (schemeSpace Z').2
  set G := tensorPowModule ((BigFppfOver.toScheme B S hS).obj Z') L (d : ℤ)
  have hG : G.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule G
  have hM := isQuasicoherentOnSite_representedModuleOf B S hS Z' G hG
  refine isZero_rightDerived_modulePushforward_of_coveringChart B S hS p hp hpp.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hpp.1) U hUaff hU _ (hM := hM) q ?_
  have hN := isQuasicoherentOnSite_etaleModulePullback B S hS
    (chartToSpace B S hS (schemeSpace Z') C) (isEtale_chartToSpace B S hS (schemeSpace Z') C)
    _ hM
  refine isZero_rightDerived_globalSections_represented_of_isZero B S hS T _ hN q ?_
  exact (hd₀ d q hd hq).of_iso
    (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      ((BigFppfOver.toScheme B S hS).obj T)).rightDerived q).mapIso
        (representedZariskiDirectImageChartIso B S hS Z' G hG C))

end AlgebraicGeometry.Space

end
