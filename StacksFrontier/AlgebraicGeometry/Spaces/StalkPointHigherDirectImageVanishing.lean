module

public import StacksFrontier.AlgebraicGeometry.CommutingFamilyNoetherian
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing

/-!
# Vanishing of a stalk of a higher direct image from the cohomology over the local ring

Let `Y` be a Noetherian scheme of the big fppf site over `S`, `y ∈ Y`, and `f : X ⟶ Y` a
quasi-compact and quasi-separated morphism from an algebraic space.  Let `X' = X ×_Y Spec 𝒪_{Y,y}`
with its projection `q : X' ⟶ X`.  For a quasi-coherent `𝒪_X`-module `𝒢` and `i ≥ 0`, if
`Hⁱ(X', q^*𝒢) = 0` then the stalk at `y` of `Rⁱf_*𝒢` vanishes.

This is the first paragraph of the proof of Stacks 0D39, read in the direction that proof uses
it: by flat base change along `c : Spec 𝒪_{Y,y} ⟶ Y` (Stacks 073K, part (1)) the inverse image
`c^*Rⁱf_*𝒢` is `Rⁱf'_*(q^*𝒢)`, whose global sections over the affine `Spec 𝒪_{Y,y}` are
`Hⁱ(X', q^*𝒢)` (Stacks 08EX over an affine base); a quasi-coherent module on an affine scheme
with no global sections is zero; and the stalk of a quasi-coherent module at `y` is the module of
global sections of its pullback to `Spec 𝒪_{Y,y}`.

## Main definitions

* `AlgebraicGeometry.Space.stalkPointObject`: `Spec 𝒪_{Y,y}` as an object of the site, and
  `AlgebraicGeometry.Space.stalkPointHom` its canonical morphism to `Y`.

## Main results

* `AlgebraicGeometry.Space.isFlat_stalkPointHom`: `Spec 𝒪_{Y,y} ⟶ Y` is flat, read as a morphism
  of algebraic spaces.
* `AlgebraicGeometry.Space.isZero_zariskiModule_stalk_of_isZero_cohomology`: the vanishing.

## References

* [Stacks Project, Tag 0D39](https://stacks.math.columbia.edu/tag/0D39)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- Injective resolutions of the `𝒪`-modules of an algebraic space, at the universe of the
structure rings. -/
local instance stalkPointHasInjectiveResolutions (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasInjectiveResolutions (Modules.{u, u} B S hS F hF) :=
  hasInjectiveResolutions_modules B S hS F hF

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The local ring at a point, as an object of the site -/

section StalkPoint

variable (Y : BigFppfOver B S hS)
  [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
  (y : (BigFppfOver.toScheme B S hS).obj Y)

/-- `Spec 𝒪_{Y,y}` for a point `y` of a Noetherian scheme `Y` of the site, as an object of the
site. -/
def stalkPointObject : BigFppfOver B S hS :=
  siteObject B S hS
    (BigFppfSite.contains_spec_stalk (X := (BigFppfOver.toScheme B S hS).obj Y) B Y.left.2 y)
    (((BigFppfOver.toScheme B S hS).obj Y).fromSpecStalk y ≫ Y.hom.hom)

/-- The canonical morphism `Spec 𝒪_{Y,y} ⟶ Y` in the site. -/
def stalkPointHom : stalkPointObject Y y ⟶ Y :=
  Over.homMk (ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).obj Y).fromSpecStalk y)) rfl

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.stalkPointHom` is
`Spec 𝒪_{Y,y} ⟶ Y`. -/
theorem map_stalkPointHom :
    (BigFppfOver.toScheme B S hS).map (stalkPointHom Y y) =
      ((BigFppfOver.toScheme B S hS).obj Y).fromSpecStalk y :=
  rfl

/-- `Spec 𝒪_{Y,y} ⟶ Y` is flat, read as a morphism of algebraic spaces. -/
theorem isFlat_stalkPointHom : IsFlat B S hS (yoneda.map (stalkPointHom Y y)) :=
  holdsOnEveryEtaleChart_yoneda_map B S hS
    AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget (stalkPointHom Y y)
    (by rw [map_stalkPointHom]; exact AlgebraicGeometry.flat_fromSpecStalk _ y)

end StalkPoint

/-! ### Zero modules over an affine represented space -/

/-- The Zariski module of a quasi-coherent module on the algebraic space of a scheme of the site
is quasi-coherent. -/
private theorem isQuasicoherent_zariskiModule (U : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) : (zariskiModule U N).IsQuasicoherent := by
  have := isQuasicoherent_restrictToChart B S hS (representedAlgebraicSpace B S hS U) N hN
    (idEtaleChart B S hS U)
  rwa [restrictToChart_eq_restrictToChartScheme] at this

/-- **A quasi-coherent module on the algebraic space of an affine scheme with no global sections
is zero after restriction to the Zariski site.** -/
theorem isZero_zariskiModule_of_isZero_globalSections (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite)
    (h : IsZero ((globalSectionsFunctor.{u + 1, u, u, u} (ringSheaf (smallEtaleRingedSite B S hS
      (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)).obj N)) :
    IsZero (zariskiModule U N) := by
  have := isQuasicoherent_zariskiModule U N hN
  have hsub : ∀ s : N.sections, s = 0 := fun s =>
    (ModuleCat.isZero_iff_subsingleton.mp h).elim s 0
  refine Stacks.CommutingFamily.isZero_of_isQuasicoherent_of_finset_affine (zariskiModule U N)
    {⟨⊤, isAffineOpen_top _⟩} (fun x => ⟨_, Finset.mem_singleton_self _, by
      change x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens); trivial⟩)
    fun w hw t => ?_
  rw [Finset.mem_singleton] at hw
  subst hw
  -- The sections over `⊤` are the sections over the identity chart, which are global.
  let e := restrictToChartSchemeTopSectionsAddEquiv B S hS (representedAlgebraicSpace B S hS U) N
    (idEtaleChart B S hS U)
  have hzero : ∀ a, e a = 0 := fun a => by
    obtain ⟨g, hg⟩ := (sectionsEvalAddEquiv N (isTerminalIdEtaleChart B S hS U)).surjective (e a)
    rw [← hg, hsub g, map_zero]
  have : Subsingleton (type_of% t) :=
    ⟨fun a b => e.injective ((hzero a).trans (hzero b).symm)⟩
  exact Subsingleton.elim _ _

/-! ### The vanishing of the stalk -/

/-- **The stalk at `y` of `Rⁱf_*𝒢` vanishes when `Hⁱ(X ×_Y Spec 𝒪_{Y,y}, 𝒢) = 0`.**

Let `Y` be a Noetherian scheme of the site, `y ∈ Y`, `f : X ⟶ Y` quasi-compact and
quasi-separated, `𝒢` a quasi-coherent `𝒪_X`-module, and `(X', q, f')` a cartesian square of `f`
along `Spec 𝒪_{Y,y} ⟶ Y`.  If `Hⁱ(X', q^*𝒢) = 0`, the stalk at `y` of `Rⁱf_*𝒢`, restricted to
the Zariski site of `Y`, is zero. -/
theorem isZero_zariskiModule_stalk_of_isZero_cohomology (Y : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    (y : (BigFppfOver.toScheme B S hS).obj Y) {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite) {X' : AlgebraicSpaces B S hS} (q : X' ⟶ X)
    (f' : X' ⟶ schemeSpace (stalkPointObject Y y))
    (sq : IsPullback q f' f (schemeSpaceMap (stalkPointHom Y y))) (i : ℕ)
    (hvan : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).rightDerived i).obj
        ((modulePullback B S hS q).obj G))) :
    letI := modulePushforward_additive B S hS f
    IsZero ((zariskiModule Y (((modulePushforward B S hS f).rightDerived i).obj G)).presheaf.stalk
      y) := by
  let := modulePushforward_additive B S hS f
  let := modulePushforward_additive B S hS f'
  let T := stalkPointObject Y y
  let c := stalkPointHom Y y
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    (inferInstance : IsAffine (Spec (.of (((BigFppfOver.toScheme B S hS).obj Y).presheaf.stalk y))))
  have hT : IsAffineSpace B S hS (representedAlgebraicSpace B S hS T).1 :=
    isAffineSpace_yoneda B S hS T inferInstance
  have hf'qc : IsQuasiCompact B S hS f'.hom :=
    isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hfqc
  have hf'qs : IsQuasiSeparated B S hS f'.hom :=
    (isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback sq hfqs
  have hg : IsFlat B S hS (representedSpaceMap B S hS c).hom := isFlat_stalkPointHom Y y
  have hqG : ((modulePullback B S hS q).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS q G hG
  have : G.IsQuasicoherentOnSite := hG
  -- `Hⁱ(X', q^*𝒢)` is the module of global sections of `Rⁱf'_*(q^*𝒢)`.
  have hN : IsZero ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS T).1
        (representedAlgebraicSpace B S hS T).2).O)).obj
        (((modulePushforward B S hS f').rightDerived i).obj ((modulePullback B S hS q).obj G))) :=
    (Functor.map_isZero (globalSectionsRestrictScalars B S hS f') hvan).of_iso
      (cohomologyRestrictScalarsIsoGlobalSectionsHigherDirectImage B S hS f' hT hf'qc hf'qs
        ((modulePullback B S hS q).obj G)
        (fun Z _ => acyclic_globalSectionsFunctor_modulePushforward_of_injective B S hS f' Z)
          i).symm
  -- So `Rⁱf'_*(q^*𝒢)` vanishes on the Zariski site of the affine `Spec 𝒪_{Y,y}`.
  have hNqc : (((modulePushforward B S hS f').rightDerived i).obj
      ((modulePullback B S hS q).obj G)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f' hf'qc hf'qs _ i
  have hzN := isZero_zariskiModule_of_isZero_globalSections T _ hNqc hN
  -- By flat base change it is the inverse image of `Rⁱf_*𝒢`.
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS
    (representedSpaceMap B S hS c) hg
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS (representedSpaceMap B S hS c)
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS q
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq.flip hg)
  have := preservesFiniteColimits_modulePullback_smallEtale B S hS q
  have hiso := isIso_higherDirectImageBaseChangeMap_of_isFlat sq hg hfqc hfqs G hG i
  have hM : (((modulePushforward B S hS f).rightDerived i).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f hfqc hfqs G i
  let e₁ : (modulePullback B S hS (representedSpaceMap B S hS c)).obj
        (((modulePushforward B S hS f).rightDerived i).obj G) ≅
      ((modulePushforward B S hS f').rightDerived i).obj ((modulePullback B S hS q).obj G) :=
    @asIso _ _ _ _ _ hiso
  have hzM : IsZero (zariskiModule T ((modulePullback B S hS (representedSpaceMap B S hS c)).obj
      (((modulePushforward B S hS f).rightDerived i).obj G))) :=
    hzN.of_iso ((restrictToChartSchemeFunctor B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) (idEtaleChart B S hS T)).mapIso e₁)
  -- The restriction to the Zariski site commutes with the inverse image of a quasi-coherent
  -- module, so the pullback of the Zariski module of `Rⁱf_*𝒢` to `Spec 𝒪_{Y,y}` vanishes.
  have hzP : IsZero ((Scheme.Modules.pullback (((BigFppfOver.toScheme B S hS).obj Y).fromSpecStalk
      y)).obj (zariskiModule Y (((modulePushforward B S hS f).rightDerived i).obj G))) :=
    hzM.of_iso (restrictToChartSchemeBaseChangeIso c _ hM).symm
  -- The stalk is the module of sections of that pullback.
  have := isQuasicoherent_zariskiModule Y _ hM
  obtain ⟨U, hU, hyU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := y) (U := ⊤) trivial
  obtain ⟨e, -⟩ := exists_fromSpecStalkSectionsStalkLinearEquiv
    (zariskiModule Y (((modulePushforward B S hS f).rightDerived i).obj G)) y hU hyU
  have hsub : Subsingleton (Γ((Scheme.Modules.pullback
      (((BigFppfOver.toScheme B S hS).obj Y).fromSpecStalk y)).obj
        (zariskiModule Y (((modulePushforward B S hS f).rightDerived i).obj G)), ⊤)) := by
    have h1 := hzP.eq_of_src (𝟙 _) 0
    have hz : ∀ a : Γ((Scheme.Modules.pullback (((BigFppfOver.toScheme B S hS).obj Y).fromSpecStalk
        y)).obj (zariskiModule Y (((modulePushforward B S hS f).rightDerived i).obj G)), ⊤),
        a = 0 := fun a => by
      have := congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤) a) h1
      simpa using this
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩
  refine @AddCommGrpCat.isZero_of_subsingleton _
    ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩

end AlgebraicGeometry.Space

end
