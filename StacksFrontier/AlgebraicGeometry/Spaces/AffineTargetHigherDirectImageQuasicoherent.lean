module

public import StacksFrontier.Algebra.Homology.WeakSerreRightDerivedOfAcyclicComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReductionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph

/-!
# The affine-base case of Stacks 0720

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over a
scheme `S` contained in a big fppf site `B`, with `Y` an *affine* algebraic space, and let `F` be
a quasi-coherent `𝒪_X`-module on the small étale site of `X`.  This file proves that the higher
direct image `R^n f_*F` is quasi-coherent for every `n`.  This is the second step of the source's
proof of Stacks 0720; the first step, the reduction to an affine base, is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart'`.

The source's relative Leray spectral sequence of an affine étale cover `g : U ⟶ X` is replaced by
the dimension shifting of
`Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_of_exists_mono_map`, along a surjective
étale chart `g : U ⟶ X` with `U` affine (Stacks 03H6): every quasi-coherent `M` embeds in
`g_*g^*M` with quasi-coherent cokernel, `g_*` preserves injectives, and the higher direct images
along `g ≫ f` vanish (Stacks 073H).  The remaining input, quasi-coherence of the `R^q g_*`, is
the same induction run once more, on the base change of `g` to an affine étale chart of `X`: a
separated morphism with quasi-compact source to an affine target, whose affine surjective étale
charts are affine morphisms by Stacks 08GB, part (2).

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineHom`:
  **the higher direct images along an affine morphism preserve quasi-coherence**, in every degree.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace`:
  the same for a morphism between affine algebraic spaces.
* `AlgebraicGeometry.Space.mono_etaleModulePullbackAdjunction_unit_app`: the unit of étale
  restriction along a surjective étale chart is a monomorphism.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_surjective_etale_chart`: the
  dimension-shifting induction, for an arbitrary surjective étale chart `g` of the source along
  which the higher direct images preserve quasi-coherence and whose composite with `f` has no
  higher direct images.
* `Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated_of_isAffineSpace`:
  the case of a separated morphism with quasi-compact source and affine target.
* `AlgebraicGeometry.Space.exists_surjective_etale_chart_of_isAffineSpace`: over an affine
  target, a separated and quasi-compact surjective étale chart `g` of `X` with `g ≫ f` affine.
* `Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_target`:
  **the affine-base case of Stacks 0720.**

## Implementation notes

*No `@[stacks]` attribute is carried.*  Stacks 0720 is claimed on
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward'`, which is this
file's main result composed with the reduction to an affine base; Stacks 073H is claimed on
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite` and
Stacks 07U8 on `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom`;
everything below is one of those with a hypothesis supplied, so a second claim would double-count
the tag.

*The degree* runs over all of `ℕ` in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`.  *The module universe* is the universe `u` of the schemes,
because `AlgebraicGeometry.Space.modulePushforward` exists only there.  *The local instances.*
`SheafOfModules.instAbelian` is raised in priority because instance search for
`CategoryTheory.Abelian` on the modules at module universe `u` otherwise commits to the
module-universe-`max u v r w` instances in the import closure and then fails on the universe
constraint; `hasInjectiveResolutions_modules` and `enoughInjectives_modules` are made local
instances for the same reason.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The affine morphisms -/

/-- **The higher direct images along an affine morphism of algebraic spaces preserve
quasi-coherence**, in every degree. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  obtain _ | n := n
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforward B S hS f).rightDerivedZeroIsoSelf.app F).symm
      (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_of_relativelyRepresentable B S hS f
        (relativelyRepresentable_of_isAffineHom B S hS f haff) haff F hF)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B S hS f haff F hF (n + 1)
        n.succ_pos)

/-- **The higher direct images along a morphism between affine algebraic spaces preserve
quasi-coherence**, in every degree. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hX : IsAffineSpace B S hS X.1)
    (hY : IsAffineSpace B S hS Y.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineHom B S hS f
    (isAffineHom_of_isAffineSpace B S hS f.hom hX hY) F hF n

/-! ### The embedding into the direct image of an étale chart -/

variable {X Y : AlgebraicSpaces B S hS}

/-- The unit `M ⟶ g_*(g^*M)` of étale restriction along a *surjective* étale chart `g` is a
monomorphism. -/
theorem mono_etaleModulePullbackAdjunction_unit_app (U : BigFppfOver B S hS)
    (g : schemeSpace U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hgs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    Mono ((etaleModulePullbackAdjunction B S hS g hg).unit.app M) :=
  have := faithful_etaleModulePullback.{u, u} B S hS U g hg hgs
  (etaleModulePullbackAdjunction B S hS g hg).unit_mono_of_L_faithful M

/-! ### The dimension-shifting induction -/

/-- **The higher direct images along `f` preserve quasi-coherence as soon as they do along a
surjective étale chart `g : U ⟶ X` of the source and the composite `g ≫ f` has quasi-coherent
direct image and no higher direct images.** -/
theorem isQuasicoherentOnSite_rightDerived_of_surjective_etale_chart (f : X ⟶ Y)
    (U : BigFppfOver B S hS) (g : schemeSpace U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hgs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g.hom)
    (hgq : ∀ H : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2,
      H.IsQuasicoherentOnSite → ∀ q,
        have := hasInjectiveResolutions_modules B S hS (schemeSpace U).1 (schemeSpace U).2
        (((modulePushforward B S hS g).rightDerived q).obj H).IsQuasicoherentOnSite)
    (hfgq : ∀ H : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2,
      H.IsQuasicoherentOnSite →
        ((modulePushforward B S hS (g ≫ f)).obj H).IsQuasicoherentOnSite)
    (hfg : ∀ H : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2,
      H.IsQuasicoherentOnSite → ∀ q, 0 < q →
        have := hasInjectiveResolutions_modules B S hS (schemeSpace U).1 (schemeSpace U).2
        IsZero (((modulePushforward B S hS (g ≫ f)).rightDerived q).obj H))
    (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := hasInjectiveResolutions_modules B S hS (schemeSpace U).1 (schemeSpace U).2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS X.1 X.2
  have := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS Y.1 Y.2
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have : (modulePushforward B S hS g).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleModulePullbackAdjunction B S hS g hg)
  let e := modulePushforwardCompIso B S hS g f
  exact Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_of_exists_mono_map
    (modulePushforward B S hS f) (modulePushforward B S hS g)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O))
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    hgq (fun H hH => SheafOfModules.IsQuasicoherentOnSite.of_iso (e.app H).symm (hfgq H hH))
    (fun H hH q hq => IsZero.of_iso (hfg H hH q hq)
      ((ModuleSheafCohomology.rightDerivedIso e q).app H))
    (fun M hM => ⟨_, (etaleModulePullbackAdjunction B S hS g hg).unit.app M,
      mono_etaleModulePullbackAdjunction_unit_app B S hS U g hg hgs M,
      isQuasicoherentOnSite_etaleModulePullback B S hS g hg M hM,
      ObjectProperty.prop_cokernel _ _ hM
        (SheafOfModules.IsQuasicoherentOnSite.of_iso
          ((modulePushforward B S hS g).rightDerivedZeroIsoSelf.app _)
          (hgq _ (isQuasicoherentOnSite_etaleModulePullback B S hS g hg M hM) 0))⟩)
    n F hF

/-! ### The separated case over an affine target -/

/-- **Stacks 0720 for a separated morphism with quasi-compact source to an affine target**: for
such an `f` and a quasi-coherent `𝒪_X`-module `F`, `R^n f_*F` is quasi-coherent for every `n`. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated_of_isAffineSpace
    (f : X ⟶ Y) (hY : IsAffineSpace B S hS Y.1) (hX : IsQuasiCompactSpace B S hS X.1)
    (hf : IsSeparated B S hS f.hom) (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  obtain ⟨U, g, hU, hgs, hg⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  let g' : schemeSpace U ⟶ X := ObjectProperty.homMk g
  have hfg : IsAffineHom B S hS (g' ≫ f).hom :=
    isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U hU) hY
  have hga : IsAffineHom B S hS g'.hom :=
    isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS g f.hom hfg hf
  exact isQuasicoherentOnSite_rightDerived_of_surjective_etale_chart B S hS f U g' hg hgs
    (fun H hH q => isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineHom B S hS g'
      hga H hH q)
    (fun H hH => isQuasicoherentOnSite_modulePushforward_of_isAffineHom_of_relativelyRepresentable
      B S hS (g' ≫ f) (relativelyRepresentable_of_isAffineHom B S hS (g' ≫ f) hfg) hfg H hH)
    (fun H hH q hq => isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B S hS
      (g' ≫ f) hfg H hH q hq) n F hF

/-! ### The affine-base case -/

/-- **An affine surjective étale chart of the source, over an affine target.**  If `f : X ⟶ Y` is
quasi-compact and quasi-separated and `Y` is affine, then `X` has a surjective étale chart
`g : U ⟶ X` by an object of the site such that `g` is separated and quasi-compact and `g ≫ f` is
affine. -/
theorem exists_surjective_etale_chart_of_isAffineSpace (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    ∃ (U : BigFppfOver B S hS) (g : schemeSpace U ⟶ X),
      IsEtale B S hS g.hom ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g.hom ∧
      IsSeparated B S hS g.hom ∧ IsQuasiCompact B S hS g.hom ∧
      IsAffineHom B S hS (g ≫ f).hom := by
  obtain ⟨U, g, hU, hgs, hg⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS Y.2 hY.isQuasiCompactSpace hfqc)
  let g' : schemeSpace U ⟶ X := ObjectProperty.homMk g
  have hfg : IsAffineHom B S hS (g' ≫ f).hom :=
    isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U hU) hY
  exact ⟨U, g', hg, hgs, isSeparated_of_isEtale_of_isAffine B S hS X.2 U hU g hg,
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS g f.hom (isAlgebraicSpace_yoneda B S hS U)
      Y.2 (isQuasiCompact_of_isAffineHom' B S hS _ (isAlgebraicSpace_yoneda B S hS U) Y.2 hfg)
      hfqs, hfg⟩

/-- **The affine-base case of Stacks 0720.**  Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S` whose target `Y` is an affine algebraic
space, and let `F` be a quasi-coherent `𝒪_X`-module.  Then `R^n f_*F` is quasi-coherent for every
`n`. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_target (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  obtain ⟨U, g, hg, hgs, hgsep, hgqc, hfg⟩ :=
    exists_surjective_etale_chart_of_isAffineSpace B S hS f hY hfqc hfqs
  refine isQuasicoherentOnSite_rightDerived_of_surjective_etale_chart B S hS f U g hg hgs
    (fun H hH q => ?_)
    (fun H hH => isQuasicoherentOnSite_modulePushforward_of_isAffineHom_of_relativelyRepresentable
      B S hS (g ≫ f) (relativelyRepresentable_of_isAffineHom B S hS (g ≫ f) hfg) hfg H hH)
    (fun H hH q hq => isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B S hS
      (g ≫ f) hfg H hH q hq) n F hF
  have := hH
  exact isQuasicoherentOnSite_rightDerived_of_forall_affine_chart' B S hS g hgqc
    (isQuasiSeparated_of_isSeparated B S hS hgsep) H q
    fun V hV _ _ hqcs =>
      isQuasicoherentOnSite_rightDerived_modulePushforward_of_isSeparated_of_isAffineSpace B S hS
        _ (isAffineSpace_yoneda B S hS _ hV) hqcs
        (isSeparated_of_isPullback B S hS (isPullback_chartBaseChangeProjection B S hS g V).flip
          hgsep) q _
        (isQuasicoherentOnSite_etaleModulePullback B S hS (chartBaseChangeInclusion B S hS g V)
          (isEtale_chartBaseChangeInclusion B S hS g V) H hH)

end AlgebraicGeometry.Space

end
