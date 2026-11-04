module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompIso
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomGlobalise
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomLocalized

/-!
# Flat pullback and internal Hom for a locally finitely presented module

The localization canonical maps are invertible. The composition law therefore transfers
invertibility from the localized morphism to the restriction of the original canonical map,
by cancellation, without an expanded restriction-square equation. The covering by finite
global presentations then gives the result on the whole site.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe u

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  (F G : SheafOfModules.{u} (Tensor.ringSheaf Y.O))

/-- Read the finite-global-presentation case at the associated morphism of ringed topoi. -/
theorem isIso_toposPullbackInternalHomMap_of_hasFiniteGlobalPresentation
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      f.ringedToposHom.fSharpInverseImage)
    (hF : _root_.SheafOfModules.HasFiniteGlobalPresentation F) :
    IsIso (toposPullbackInternalHomMap f.ringedToposHom F G) :=
  Eq.mpr (congrArg IsIso (toposPullbackInternalHomMap_ringedToposHom
    (F := F) (G := G) f))
    (isIso_pullbackInternalHomMap_of_hasFiniteGlobalPresentation f F G hf hF)

/-- Restriction of the canonical map is invertible wherever the first module has a finite
global presentation, by the two factorizations of the localization square. -/
theorem isIso_pullbackInternalHomMap_over_of_hasFiniteGlobalPresentation
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      f.ringedToposHom.fSharpInverseImage)
    (V : Y.C) (hV : _root_.SheafOfModules.HasFiniteGlobalPresentation (F.over V)) :
    IsIso ((pullbackInternalHomMap f F G).over (f.u.obj V)) := by
  let U := f.u.obj V
  let jU := X.localizationRingedToposHom U
  let jV := Y.localizationRingedToposHom V
  let fV := f.localizedRingedToposHom V
  let χ := RingedToposHom.comp (X := RingedSite.ringedTopos (X.over U))
    (Y := RingedSite.ringedTopos X) (Z := RingedSite.ringedTopos Y) f.ringedToposHom jU
  have hlocal := isIso_toposPullbackInternalHomMap_of_hasFiniteGlobalPresentation
    (f.localized V) (F.over V) ((toposPullback jV).obj G)
    (f.isFlatMapULift_localized_ringedToposHom_fSharpInverseImage V hf) hV
  have hlocal' := isIso_toposPullbackInternalHomMap_of_iso_first
    (X := X.over U) (Y := Y.over V) fV
    ((Y.localizationPullbackToposIsoRestriction V).app F)
    ((toposPullback jV).obj G) hlocal
  let τ := toposCompositeComparisonOfTwoIso
    (X := X.over U) (Y := Y.over V) (Z := Y) fV jV χ (f.localizedRingedSquare V)
  have hτ := fSharpSet_toposCompositeComparisonOfTwoIso
    (X := X.over U) (Y := Y.over V) (Z := Y) fV jV χ (f.localizedRingedSquare V)
  have hχ := isIso_toposPullbackInternalHomMap_compOf
    (X := X.over U) (Y := Y.over V) (Z := Y) fV jV χ τ hτ F G
    (isIso_toposPullbackInternalHomMap_localization Y V F G) hlocal'
  have hm0 := isIso_map_toposPullbackInternalHomMap_of_compOf
    (X := X.over U) (Y := X) (Z := Y) jU f.ringedToposHom χ
    (RingedToposHom.toModulesHomPushforwardIso jU f.ringedToposHom)
    (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso jU f.ringedToposHom) F G hχ
    (isIso_toposPullbackInternalHomMap_localization X U
      ((toposPullback f.ringedToposHom).obj F) ((toposPullback f.ringedToposHom).obj G))
  have hm : IsIso ((toposPullback jU).map (pullbackInternalHomMap f F G)) :=
    Eq.mp (congrArg (fun a ↦ IsIso ((toposPullback jU).map a))
      (toposPullbackInternalHomMap_ringedToposHom (F := F) (G := G) f)) hm0
  exact isIso_map_of_comparison (X.localizationPullbackToposIsoRestriction U)
    (pullbackInternalHomMap f F G) hm

/-- Flat pullback commutes with the canonical internal-Hom map for a module which is locally
finitely presented. This statement uses a single universe for the site and coefficients. -/
@[stacks 0GN2 "the isomorphism under the source's own hypotheses: `F` of finite presentation in
the local sense of Tag 03DL and `f` flat; stated for a site and coefficients in one universe"]
theorem isIso_pullbackInternalHomMap_of_isFinitePresentationOnSite
    [F.IsFinitePresentationOnSite]
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      f.ringedToposHom.fSharpInverseImage) : IsIso (pullbackInternalHomMap f F G) :=
  isIso_pullbackInternalHomMap_of_isIso_over f F G fun V ↦
    isIso_pullbackInternalHomMap_over_of_hasFiniteGlobalPresentation f F G hf V.val V.property

end Stacks.SheafOfModules.InternalHom

end
