module

public import StacksFrontier.Algebra.Homology.WeakSerreRightDerivedOfAcyclicComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineTargetHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReductionGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreInstance

/-!
# Higher direct images of quasi-coherent modules are quasi-coherent

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  If `f` is quasi-compact and quasi-separated then every higher direct image `R^i f_*`
carries a quasi-coherent `𝒪_X`-module to a quasi-coherent `𝒪_Y`-module.  This is Stacks 0720; its
degree-zero case is Stacks 03M9.

The proof follows the source.  Quasi-coherence is tested on the affine étale charts `V` of `Y`,
over which `R^i f_*F` restricts to `R^i f'_*(F|_U)` for the base change `f' : U = V ×_Y X ⟶ V`;
this is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart_general`.  So
`Y` may be taken affine.  Then `X` is quasi-compact and has a surjective étale chart `g : U ⟶ X`
by an affine scheme `U`; `g ≫ f` is affine, so `(g ≫ f)_*` preserves quasi-coherence
(Stacks 07U8) and has no higher direct images on quasi-coherent modules (Stacks 073H).  Granted
that every `R^q g_*` preserves quasi-coherence, an induction on the degree shows the same for
`R^i f_*`: every quasi-coherent `F` embeds into `g_*g^*F` with quasi-coherent cokernel, and the
source's Leray spectral sequence for `f ∘ g` is replaced by the homological algebra of
`Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_of_exists_mono_map`, applied in the weak
Serre subcategory of quasi-coherent modules (Stacks 03M1).

That `R^q g_*` preserves quasi-coherence is the case "representable, separated and quasi-compact"
of the source, there deduced from the theory for schemes.  Here it is proved by the same
induction once more: `g` is separated, being étale with affine source, so its base change to an
affine étale chart of `X` is a separated morphism with quasi-compact source to an affine target,
and for such a morphism an affine surjective étale chart of its source is an affine morphism by
Stacks 08GB, so that the higher direct images along both the chart and its composite vanish and
the induction applies with `R^q` of an affine morphism in place of `R^q g_*`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_obj_of_surjective_etale_chart`: the
  induction above, for any surjective étale chart `g` of the source with `R^q g_*` preserving
  quasi-coherence and `g ≫ f` having no higher direct images.
* `Space.isQuasicoherentOnSite_rightDerived_modulePushforward_obj_of_isAffineHom`:
  the higher direct images along an affine morphism preserve quasi-coherence.
* `Space.isQuasicoherentOnSite_rightDerived_modulePushforward_obj_of_isSeparated_of_isAffineSpace`:
  the case of a separated morphism with quasi-compact source to an affine target.
* `Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_of_qcqs`:
  the case of an affine target.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_qcqs`:
  Stacks 0720.  Its degree-zero case, Stacks 03M9, is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`.

## Implementation notes

*The degree* runs over all of `ℕ` in the injective-resolution convention
`CategoryTheory.Functor.rightDerived`, the convention the source's proof is written in.  *The
module universe* is the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePushforward` exists only there.  *The local instances*: instance
search for `Abelian` on the modules at module universe `u` otherwise commits to the
module-universe-`max u v r w` instances in the import closure and then fails on the universe
constraint, so `SheafOfModules.instAbelian` is given priority, and the injective resolutions and
enough injectives of the modules on the small étale site are made local instances.

## References

* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable {X Y : AlgebraicSpaces B S hS}

/-! ### Higher direct images through a surjective étale chart -/

/-- **Higher direct images along `f` preserve quasi-coherence if they do along a surjective
étale chart `g : U ⟶ X` and along `g ≫ f`, the latter having no higher direct images.**

This is the argument of the proof of Stacks 0720 over an affine base, without the spectral
sequence: `F ↪ g_*g^*F` with quasi-coherent cokernel, `g_*` preserves injectives (`g` being
étale, its left adjoint `g^*` is exact), `f_* ∘ g_* = (g ≫ f)_*`, and the quasi-coherent modules
form a weak Serre subcategory (Stacks 03M1); the homological algebra is
`Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_of_exists_mono_map`. -/
theorem isQuasicoherentOnSite_rightDerived_obj_of_surjective_etale_chart (f : X ⟶ Y)
    (U : BigFppfOver B S hS) (g : schemeSpace U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hgs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g.hom)
    (hgq : ∀ H : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2,
      H.IsQuasicoherentOnSite → ∀ q,
        (((modulePushforward B S hS g).rightDerived q).obj H).IsQuasicoherentOnSite)
    (hfgq : ∀ H : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2,
      H.IsQuasicoherentOnSite →
        ((modulePushforward B S hS (g ≫ f)).obj H).IsQuasicoherentOnSite)
    (hfg : ∀ H : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2,
      H.IsQuasicoherentOnSite → ∀ q, 0 < q →
        IsZero (((modulePushforward B S hS (g ≫ f)).rightDerived q).obj H))
    (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := quasicoherentSheaves_isWeakSerreClass_of_isAlgebraicSpace B S hS X.1 X.2
  have := quasicoherentSheaves_isWeakSerreClass_of_isAlgebraicSpace B S hS Y.1 Y.2
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have : (modulePushforward B S hS g).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleModulePullbackAdjunction B S hS g hg)
  let e := modulePushforwardCompIso B S hS g f
  exact Stacks.Cohomology.RightDerivedCoEdge.prop_rightDerived_of_exists_mono_map
    (modulePushforward B S hS f) (modulePushforward B S hS g)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace U).1 (schemeSpace U).2).O)))
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)))
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
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

/-! ### The affine-base case of Stacks 0720 -/

/-- **Higher direct images along an affine morphism preserve quasi-coherence**: `f_*F` is
quasi-coherent by Stacks 07U8 and `R^nf_*F = 0` for `n > 0` by Stacks 073H. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_obj_of_isAffineHom (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  have := quasicoherentSheaves_isWeakSerreClass_of_isAlgebraicSpace B S hS Y.1 Y.2
  obtain _ | n := n
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePushforward B S hS f).rightDerivedZeroIsoSelf.app F).symm
      (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf F hF)
  · exact ObjectProperty.prop_of_isZero _
      (isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite B S hS f hf F
        hF (n + 1) n.succ_pos)

/-- The chart criterion when `g ≫ f` is affine, so its higher direct images are those of an
affine morphism. -/
private theorem isQuasicoherentOnSite_rightDerived_obj_of_affine_comp (f : X ⟶ Y)
    (U : BigFppfOver B S hS) (g : schemeSpace U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hgs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g.hom) (hfg : IsAffineHom B S hS (g ≫ f).hom)
    (hgq : ∀ H : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2,
      H.IsQuasicoherentOnSite → ∀ q,
        (((modulePushforward B S hS g).rightDerived q).obj H).IsQuasicoherentOnSite)
    (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_obj_of_surjective_etale_chart B S hS f U g hg hgs hgq
    (fun H hH => isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS
      (g ≫ f) hfg H hH)
    (fun H hH q hq => isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite
      B S hS (g ≫ f) hfg H hH q hq) n F hF

/-- **Stacks 0720 for a separated morphism with quasi-compact source to an affine target.**
A surjective étale chart `g : U ⟶ X` by an affine scheme (Stacks 03H6) is affine over `X` by
Stacks 08GB, part (2), and `g ≫ f` is affine, `U` and `Y` being affine; so the higher direct
images along `g` and `g ≫ f` are those of affine morphisms. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_obj_of_isSeparated_of_isAffineSpace
    (f : X ⟶ Y) (hY : IsAffineSpace B S hS Y.1) (hX : IsQuasiCompactSpace B S hS X.1)
    (hf : IsSeparated B S hS f.hom) (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  obtain ⟨U, g, hU, hgs, hg⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  let g' : schemeSpace U ⟶ X := ObjectProperty.homMk g
  have hfg : IsAffineHom B S hS (g' ≫ f).hom :=
    isAffineHom_of_isAffineSpace B S hS _ (isAffineSpace_yoneda B S hS U hU) hY
  have hga : IsAffineHom B S hS g'.hom :=
    isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS g f.hom hfg hf
  exact isQuasicoherentOnSite_rightDerived_obj_of_affine_comp B S hS f U g' hg hgs hfg
    (fun H hH q => isQuasicoherentOnSite_rightDerived_modulePushforward_obj_of_isAffineHom B S hS g'
      hga q H hH) n F hF

/-- **Stacks 0720 over an affine target.**  Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S` with `Y` affine, and let `F` be a
quasi-coherent `𝒪_X`-module.  Then `R^nf_*F` is quasi-coherent for every `n`.

For the chart `g : U ⟶ X` of
`AlgebraicGeometry.Space.exists_surjective_etale_chart_of_isAffineSpace`, the higher direct images
along `g` are quasi-coherent: tested on the affine étale charts `V` of `X`
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart_general`)
they are those of the base change `V ×_X U ⟶ V`, a separated morphism with quasi-compact source
to an affine target.  Those along `g ≫ f` vanish in positive degrees by Stacks 073H, `g ≫ f`
being affine. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_of_qcqs (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (n : ℕ) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    (((modulePushforward B S hS f).rightDerived n).obj F).IsQuasicoherentOnSite := by
  obtain ⟨U, g, hg, hgs, hgsep, hgqc, hfg⟩ :=
    exists_surjective_etale_chart_of_isAffineSpace B S hS f hY hfqc hfqs
  refine isQuasicoherentOnSite_rightDerived_obj_of_affine_comp B S hS f U g hg hgs hfg
    (fun H hH q => ?_) n F hF
  have := hH
  exact isQuasicoherentOnSite_rightDerived_of_forall_affine_chart_general B S hS g hgqc
    (isQuasiSeparated_of_isSeparated B S hS hgsep) H q fun V hV _ _ hqcs =>
      isQuasicoherentOnSite_rightDerived_modulePushforward_obj_of_isSeparated_of_isAffineSpace
        B S hS _ (isAffineSpace_yoneda B S hS _ hV) hqcs
        (isSeparated_of_isPullback B S hS (isPullback_chartBaseChangeProjection B S hS g V).flip
          hgsep) q _
        (isQuasicoherentOnSite_etaleModulePullback B S hS (chartBaseChangeInclusion B S hS g V)
          (isEtale_chartBaseChangeInclusion B S hS g V) H hH)

/-! ### Stacks 0720 -/

/-- **Stacks 0720.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces over a scheme `S`, and let `F` be a quasi-coherent `𝒪_X`-module on the small
étale site of `X`.  Then the higher direct image `R^i f_*F` is quasi-coherent for every `i`.

Quasi-coherence of `R^i f_*F` is tested on the affine étale charts `V` of `Y`, over which it
restricts to `R^i f'_*(F|_U)` for the base change `f' : U = V ×_Y X ⟶ V`
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_of_forall_affine_chart_general`, by
Stacks 03M0, condition (4), and the higher-direct-image clause of Stacks 03LX); `f'` is
quasi-compact and quasi-separated, and the affine-target case is
`Space.isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_of_qcqs`. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_of_qcqs {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (i : ℕ) :
    (((modulePushforward B S hS f).rightDerived i).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_of_forall_affine_chart_general B S hS f hfqc hfqs F i
    fun V hV hqc hqs _ ↦
      isQuasicoherentOnSite_rightDerived_modulePushforward_of_isAffineSpace_of_qcqs B S hS _
        (isAffineSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj V) hV) hqc hqs i _
        (isQuasicoherentOnSite_etaleModulePullback B S hS
          (chartBaseChangeInclusion B S hS f V)
          (isEtale_chartBaseChangeInclusion B S hS f V) F inferInstance)

end AlgebraicGeometry.Space

end
