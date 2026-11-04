module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCondition2
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartScheme

/-!
# Finite local freeness of a morphism of algebraic spaces, read on represented base changes

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is *finite locally free* in the sense
of Stacks 03ZV when it is affine and `f_*𝒪_X` is a finite locally free `𝒪_Y`-module on the small
étale site of `Y`; it has rank `r` when `f_*𝒪_X` has rank `r`. Stacks 03ZU compares this with the
representable reading of Section 03HA: every represented base change of `f` is a finite locally
free morphism of schemes (of rank `r`). This file proves the "if" direction without rank and the
equivalence with rank.

At an étale scheme chart `V` of `Y`, with `ψ : V ×_Y X ⟶ V` the base change of an affine `f`, the
restriction of `f_*𝒪_X` to the slice at `V`, read on the small étale site of the scheme `V`, is the
associated module of the Zariski direct image `ψ_*𝒪`; by Stacks 05VG at `τ = étale` its finite
local freeness, and its rank, are those of `ψ_*𝒪`.

## Main results

* `isFiniteLocallyFreeOfRank_chartSchemeSiteModule_iff`: the rank clause of Stacks 0409 crosses the
  identification of the slice at a chart with the small étale site of the chart scheme.
* `isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_baseChangeChartHom`: if the base change of
  `f` over an étale chart `V` is finite locally free, so is the restriction of `f_*𝒪_X` to the
  slice at `V`.
* `isFiniteLocallyFreeOfRank_over_iff_baseChangeChartHom`: the chart comparison of Stacks 03ZU in
  its rank form, for an affine morphism.
* `isFiniteLocallyFree_of_presheaf`: **Stacks 03ZU**, the "if" direction.
* `presheaf_iff_isFiniteLocallyFreeOfRank`: Stacks 03ZU for a fixed rank.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rank clause of Stacks 0409 crosses the chart-scheme identification.**  A module on the
slice of the small étale site of an algebraic space at an étale chart has rank `r` if and only if
the module it becomes on the small étale site of the scheme underlying that chart has rank `r`. -/
theorem isFiniteLocallyFreeOfRank_chartSchemeSiteModule_iff (U : AlgebraicSpaces B S hS)
    (W : (smallEtaleRingedSite B S hS U.1 U.2).C)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS U.1 U.2).over W).O)) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
          (chartOverObject B S hS U W).left.property)
        (chartSchemeSiteModule B S hS U W M) r ↔
      RingedSite.IsFiniteLocallyFreeOfRank ((smallEtaleRingedSite B S hS U.1 U.2).over W) M r := by
  have h₁ := isContinuous_chartSchemeIdentification_functor B S hS U W
  have h₂ := isContinuous_chartSchemeIdentification_inverse B S hS U W
  have h₃ := isDenseSubsite_chartSchemeIdentification_inverse B S hS U W
  exact @RingedSite.isFiniteLocallyFreeOfRank_reindex_iff
    ((smallEtaleRingedSite B S hS U.1 U.2).over W) _ _ (chartSchemeTopology B S hS U W)
    (chartSchemeIdentification B S hS U W) h₁ h₂ h₃ M r

section ChartComparison

variable {X Y : AlgebraicSpaces B S hS}

/-- The slice module of `f_*𝒪_X` at a chart `V`, read on the chart scheme, is the associated
module of the Zariski direct image of the structure sheaf along the base change over `V`. -/
private noncomputable def chartSchemeSiteModuleIsoAssociatedModule (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    [_root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (baseChangeChartHom B S hS f hrep V).left)] :
    chartSchemeSiteModule B S hS Y V ((pushforwardStructureModule B S hS f).over V) ≅
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) _
        (chartOverObject B S hS Y V).left.property).obj
        (Stacks.Morphisms.pushforwardStructureSheaf
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            (baseChangeChartHom B S hS f hrep V).left)) :=
  chartSchemePushforwardStructureModuleIso B S hS f hrep V ≪≫
    AlgebraicGeometry.SmallEtale.pushforwardUnitAssociatedModuleIso (associatedBigEtaleSite B)
      (baseChangeChartHom B S hS f hrep V).left

/-- **The chart comparison of Stacks 03ZU, from the base change to the module.**  For a
representable morphism `f : X ⟶ Y` of algebraic spaces over `S` and an étale scheme chart `V`
of `Y`, if the base change `ψ : V ×_Y X ⟶ V` of `f` over `V` is a finite locally free morphism of
schemes, the restriction of `f_*𝒪_X` to the slice at `V` is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
    (h : Stacks.Morphisms.IsFiniteLocallyFree
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V))) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).over V)
      ((pushforwardStructureModule B S hS f).over V) := by
  have : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (baseChangeChartHom B S hS f hrep V).left) := h.toIsAffineHom
  refine (isFiniteLocallyFreeOnSite_chartSchemeModule_iff B S hS Y V _).1 ?_
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (chartSchemeSiteModuleIsoAssociatedModule B S hS f hrep V).symm ?_
  exact AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule _ _ _ _
    h.toIsFiniteLocallyFree

/-- **The chart comparison of Stacks 03ZU, for a fixed rank.**  For an affine morphism
`f : X ⟶ Y` of algebraic spaces over `S` and an étale scheme chart `V` of `Y`, the restriction of
`f_*𝒪_X` to the slice at `V` has rank `r` if and only if the base change `ψ : V ×_Y X ⟶ V` of `f`
over `V` is a finite locally free morphism of schemes of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_over_iff_baseChangeChartHom (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (V : (smallEtaleRingedSite B S hS Y.1 Y.2).C) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank ((smallEtaleRingedSite B S hS Y.1 Y.2).over V)
        ((pushforwardStructureModule B S hS f).over V) r ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)) r := by
  have : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (baseChangeChartHom B S hS f hrep V).left) :=
    isAffineHom_baseChangeChartHom B S hS f hrep haff V
  have : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (baseChangeChartHom B S hS f hrep V)) := this
  refine Iff.trans (isFiniteLocallyFreeOfRank_chartSchemeSiteModule_iff B S hS Y V _ r).symm ?_
  refine Iff.trans ?_ (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff _ r).symm
  refine Iff.trans ?_ (and_iff_right this).symm
  refine Iff.trans ?_ (RingedSite.isFiniteLocallyFreeOfRank_iff_sheafOfModules
    (Scheme.zariskiRingedSite ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS Y V)))
    _ r)
  refine Iff.trans ?_ (AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_associatedModule_iff
    (associatedBigEtaleSite B) _ (chartOverObject B S hS Y V).left.property _ r)
  exact ⟨RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      (chartSchemeSiteModuleIsoAssociatedModule B S hS f hrep V),
    RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
      (chartSchemeSiteModuleIsoAssociatedModule B S hS f hrep V).symm⟩

/-! ### Stacks 03ZU -/

/-- **Stacks 03ZU, the "if" direction.**  A morphism of algebraic spaces over `S` which is finite
locally free in the sense of Section 03HA — representable, with every represented base change a
finite locally free morphism of schemes — is finite locally free in the sense of Stacks 03ZV:
affine, with `f_*𝒪_X` a finite locally free `𝒪_Y`-module. -/
theorem isFiniteLocallyFree_of_presheaf (f : X ⟶ Y)
    (h : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    IsFiniteLocallyFree B S hS f := by
  obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  exact isFiniteLocallyFree_of_presheaf_of_chartComparison_at B S hS f h.rep V hV
    (isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_baseChangeChartHom B S hS f h.rep V) h

/- **Stacks 03ZU.**  A morphism `f : X ⟶ Y` of algebraic spaces over `S` is finite locally free
in the sense of Section 03HA — representable, with every represented base change a finite
locally free morphism of schemes — if and only if it is finite locally free in the sense of
Stacks 03ZV: affine, with `f_*𝒪_X` a finite locally free `𝒪_Y`-module. -/

add_to_stacks 03ZU AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree

/-- **Stacks 03ZU, for a fixed rank.**  A morphism `f : X ⟶ Y` of algebraic spaces over `S` is
representable with every represented base change a finite locally free morphism of schemes of
rank `r` if and only if it is finite locally free of rank `r` in the sense of Stacks 03ZV:
affine, with `f_*𝒪_X` of rank `r` on the small étale site of `Y`. -/
theorem presheaf_iff_isFiniteLocallyFreeOfRank (f : X ⟶ Y) (r : ℕ) :
    (MorphismProperty.inverseImage
        (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
        (BigFppfOver.toScheme B S hS)).presheaf f.hom ↔
      IsFiniteLocallyFreeOfRank B S hS f r := by
  obtain ⟨V, hV⟩ := exists_surjective_smallEtale_chart B S hS Y.1 Y.2
  have hC := isFiniteLocallyFreeOfRank_iff_over_of_isSurjective B S hS f r V hV
  refine ⟨fun hL => ?_, fun hR => ?_⟩
  · have haff := isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank B S hS r hL
    have hB := isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints
      B S hS r X.2 Y.2 hL.rep V.2 hV
    exact hC.2 ⟨haff,
      (isFiniteLocallyFreeOfRank_over_iff_baseChangeChartHom B S hS f hL.rep haff V r).2
        (hB.1 hL)⟩
  · have hrep := relativelyRepresentable_of_isAffineHom B S hS f hR.1.1
    have hB := isFiniteLocallyFreeOfRank_presheaf_iff_of_etaleChart_surjectiveOnPoints
      B S hS r X.2 Y.2 hrep V.2 hV
    exact hB.2 ((isFiniteLocallyFreeOfRank_over_iff_baseChangeChartHom B S hS f hrep hR.1.1 V
      r).1 (hC.1 hR).2)

end ChartComparison

end AlgebraicGeometry.Space

end
