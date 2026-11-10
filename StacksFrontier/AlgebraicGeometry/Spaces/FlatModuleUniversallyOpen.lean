module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Universal openness from a flat module with full support on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite presentation, and let `𝓕` be an `𝒪_X`-module which, on étale scheme charts, is
quasi-coherent, of finite type, of full support and flat over `Y`. Then `f` is universally open.

## Main definitions

* `AlgebraicGeometry.Space.HasFullSupportOnCharts`: the restriction of the module to every étale
  scheme chart has the whole chart as its support.

## Main results

* `AlgebraicGeometry.Space.universallyOpen_map_chartDiagram_of_isFlatOver_of_fullSupport`: the
  morphism of schemes of every commuting square of étale scheme charts is universally open.
* `AlgebraicGeometry.Space.universallyOpen_of_universallyOpen_comp`: universal openness of `p ≫ f`
  implies that of `f` when `p` is surjective on points.
* `AlgebraicGeometry.Space.universallyOpen_of_isFlatOver_of_fullSupport`: `f` is universally open.

## References

* [Stacks Project, Tag 0CVU](https://stacks.math.columbia.edu/tag/0CVU)
* [Stacks Project, Tag 0CVT](https://stacks.math.columbia.edu/tag/0CVT)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Full support on charts -/

/-- A module on an algebraic space *has full support on charts* when the restriction of the
module to every étale scheme chart has the whole chart as its support. -/
abbrev HasFullSupportOnCharts (hX : IsAlgebraicSpace B S hS X)
    (F : Modules.{u, u} B S hS X hX) : Prop :=
  ∀ U : SmallEtale B S hS X, SheafOfModules.supp (chartModule B S hS hX F U) = Set.univ

/-! ### The chartwise half -/

/-- On every commuting square of étale scheme charts of a morphism locally of finite presentation
carrying a module which is quasi-coherent, of finite type, of full support and flat over the target
on charts, the morphism of schemes is universally open. -/
@[ega "IV 11.3.1" "more general"]
theorem universallyOpen_map_chartDiagram_of_isFlatOver_of_fullSupport
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hsupp : HasFullSupportOnCharts B S hS hX F) (hflat : IsFlatOver B S hS hX f F)
    (d : ChartDiagram B S hS X Y f) :
    _root_.AlgebraicGeometry.UniversallyOpen ((BigFppfOver.toScheme B S hS).map d.g) := by
  have := locallyOfFinitePresentation_chartDiagram B S hS hf d
  have := hqc d.U
  have := hft d.U
  exact _root_.AlgebraicGeometry.universallyOpen_of_isFlatOver_of_supp_eq_univ
    ((BigFppfOver.toScheme B S hS).map d.g) (chartModule B S hS hX F d.U) (hsupp d.U) (hflat d)

/-! ### Cancelling a morphism surjective on points -/

section Cancel

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on `BigFppfOver B S hS`
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_FlatModuleUniversallyOpen :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_FlatModuleUniversallyOpen
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- If `p` is surjective on points and `p ≫ f` is universally open, then `f` is universally
open. -/
theorem universallyOpen_of_universallyOpen_comp {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : X' ⟶ X) (f : X ⟶ Y) {k : X' ⟶ Y} (hk : p ≫ f = k)
    (hp : Function.Surjective (pointsMap B S hS X' p))
    (hkopen : UniversallyOpen B S hS k) :
    UniversallyOpen B S hS f := by
  subst hk
  intro Z hZ g
  have hsurj : Function.Surjective (pointsMap B S hS (pullback (pullback.snd g f) p)
      (pullback.fst (pullback.snd g f) p)) :=
    surjective_pointsMap_of_isPullback B S hS
      (IsPullback.of_hasPullback (pullback.snd g f) p).flip hp
  have hcomp : IsOpenMap (pointsMap B S hS (pullback (pullback.snd g f) p)
      (pullback.fst (pullback.snd g f) p ≫ pullback.fst g f)) :=
    isOpenMap_pointsMap_of_comp_isIso B S hS (pullbackLeftPullbackSndIso g f p).hom
      (pullbackLeftPullbackSndIso_hom_fst g f p) (hkopen Z hZ g)
  rw [pointsMap_comp] at hcomp
  exact IsOpenMap.of_comp (continuous_pointsMap B S hS _) hsurj hcomp

end Cancel

/-! ### Universal openness from a flat module of full support -/

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite
presentation and let `𝓕` be an `𝒪_X`-module which, on charts, is quasi-coherent, of finite type,
of full support and flat over `Y`. Then `f` is universally open. -/
@[stacks 0CVU, ega "IV 11.3.1" "f|U open", ega "IV 2.4.6", ega "IV 15.2.1" "more general"]
theorem universallyOpen_of_isFlatOver_of_fullSupport
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX)
    (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : IsQuasicoherentOnCharts B S hS hX F) (hft : IsFiniteTypeOnCharts B S hS hX F)
    (hsupp : HasFullSupportOnCharts B S hS hX F) (hflat : IsFlatOver B S hS hX f F) :
    UniversallyOpen B S hS f := by
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hqSurj hqEtale
  have hqIsEtale : IsEtale B S hS q := isEtale_of_presheaf_etale B S hS hqEtale
  have hαOpen : _root_.AlgebraicGeometry.UniversallyOpen
      ((BigFppfOver.toScheme B S hS).map α) :=
    universallyOpen_map_chartDiagram_of_isFlatOver_of_fullSupport B S hS hX F hf hqc hft hsupp
      hflat { U := ⟨CostructuredArrow.mk p, hpEtale⟩
              V := ⟨CostructuredArrow.mk q, hqEtale⟩
              g := α
              comm := hcomm }
  have hyα : UniversallyOpen B S hS (yoneda.map α) :=
    universallyOpen_of_presheaf_universallyOpen B S hS _
      (presheaf_yoneda_map_of_inverseImage B S hS inferInstance α hαOpen)
  have hqOpen : UniversallyOpen B S hS q :=
    universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS
      (isAlgebraicSpace_yoneda B S hS V) hY q (isFlat_of_isEtale B S hS hqIsEtale)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hqIsEtale)
  exact universallyOpen_of_universallyOpen_comp B S hS p f hcomm
    ((surjective_iff_surjective_pointsMap B S hS X hX U p).mp hpSurj)
    (universallyOpen_comp B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) hY _ _ hyα hqOpen)

end AlgebraicGeometry.Space

end
