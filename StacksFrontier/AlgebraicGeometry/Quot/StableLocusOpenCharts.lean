module

public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenSchemes
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Quot.ExtendsFibreIsoNearPoint

/-!
# Stability of a prestable family of curves near a point, over a scheme chart

Let `G ⟶ S` be a prestable family of curves (Stacks 0E6T) and `φ : U ⟶ S` a morphism of the big
fppf site, with `U` quasi-compact and quasi-separated, such that `G ×_S U` is a scheme `Z` over
`U` (an étale scheme chart, Stacks 0E6F). If the fibre of `Z ⟶ U` over a point `u ∈ U` has genus
at least two and neither a rational tail nor a rational bridge, then there is an open
neighbourhood `W` of `u` in `U` such that every family of curves mapping to `G` over a morphism of
bases factoring through `W` is stable (Stacks 0E75).

The fibres of `G` over field-valued points factoring through `U` are presented by fibre products
of the site `Z ×_U Spec k`, so they are schemes; their stability is read off the scheme-level
statement `CurveFibres.exists_mem_forall_hasGenusTwoNoRationalTailNoRationalBridge` (Stacks 0D2S
applied to the relative dualizing sheaf of `Z ⟶ U`).

## Main results

* `AlgebraicGeometry.CurveFamily.isPullback_presentation_of_factors`: the fibre product of the
  site `Z ×_U Spec k` presents the fibre of `G` over a field-valued point factoring through `U`.
* `CurveFamily.exists_mem_forall_hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback`:
  the fibre condition of Stacks 0E75 near `u`, on those presentations.
* `AlgebraicGeometry.CurveFamily.exists_mem_forall_isStableCurveFamily_of_isPullback`: every
  family mapping to `G` through `W` is stable.
* `AlgebraicGeometry.CurveFamily.isStableCurveFamily_of_forall_fieldValuedPoint_eq_map`: a
  prestable family is stable as soon as it has stable base changes through which every
  field-valued point lifts over the same field (the stability of the glued stabilization of
  Stacks 0E8A, without the openness of the stable locus).

## Implementation notes

The full condition (o) of Stacks 0E0E for stable families, `AlgebraicGeometry.IsOpenCurvesLocus`
of `AlgebraicGeometry.IsStableCurveFamily`, needs in addition the openness of the prestable locus
(Stacks 0E6U, through Stacks 0E6I) and presentations of the fibres over field-valued points which
do not lift to a scheme chart over their own field (Stacks 0ADD for the fibres).

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **The fibre product of the site presents the fibre over a point through a chart.** If
`G ×_S U` is the scheme `Z` (through `p` and `q`) and the field-valued point `pG` of `S` factors
as `c ≫ φ` through `U`, then `Z ×_U Spec k` presents the fibre of `G` over `pG`. -/
theorem isPullback_presentation_of_factors {G : CurveFamily B hZ}
    {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ G.base} {p : schemeSpace Z ⟶ G.total}
    {q : Z ⟶ U} (sq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    (pG : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
    (c : pG.siteObject ⟶ U) (hc : c ≫ φ = pG.value) :
    IsPullback (yoneda.map (pullback.fst q c) ≫ p.hom) (yoneda.map (pullback.snd q c))
      G.toBase.hom (yonedaEquiv.symm pG.value) := by
  have hp : yonedaEquiv.symm pG.value = yoneda.map pG.value :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map pG.value).symm
  have sq' := AlgebraicSpaces.isPullback_hom B integerBase hZ sq
  simp only [schemeSpaceMap_hom] at sq'
  rw [hp, ← hc, Functor.map_comp]
  exact ((IsPullback.of_hasPullback q c).map yoneda).paste_horiz sq'

/-- The yoneda-side value of a field-valued point pushed forward along a base map is the
composite with the image of the base map. -/
private theorem yonedaEquiv_symm_value_map {X Y : BigFppfOver B integerBase hZ} (f : X ⟶ Y)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X).obj) :
    yonedaEquiv.symm
        (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap f).hom p).value =
      yonedaEquiv.symm p.value ≫ (schemeSpaceMap f).hom :=
  (yonedaEquiv_symm_naturality_right _ _ _).symm

/-- **The fibre condition of Stacks 0E75 near a point, through a scheme chart.** Let `G` be a
prestable family of curves and `G ×_S U ≅ Z` a scheme chart along `φ : U ⟶ S` with `U`
quasi-compact and quasi-separated. If the fibre of `Z ⟶ U` over `u`, presented by `C₀` over
`Spec κ(u)` with `H⁰(C₀, 𝒪) = κ(u)`, has genus at least two and neither a rational tail nor a
rational bridge, then there is an open `W ∋ u` such that for every field-valued point of `S`
factoring through `W`, the presentation `Z ×_U Spec k` of the fibre of `G` there has genus at least
two and neither a rational tail nor a rational bridge. -/
theorem exists_mem_forall_hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G)
    {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ G.base} {p : schemeSpace Z ⟶ G.total}
    {q : Z ⟶ U} (sq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    [CompactSpace ((𝒯).obj U)] [QuasiSeparatedSpace ((𝒯).obj U)] (u : (𝒯).obj U)
    (hu : ∃ (C₀ : Scheme.{u}) (h₀ : C₀ ⟶ (𝒯).obj Z)
      (g₀ : C₀ ⟶ Spec (.of (((𝒯).obj U).residueField u))),
      IsPullback h₀ g₀ ((𝒯).map q) (((𝒯).obj U).fromSpecResidueField u) ∧
        Function.Bijective g₀.appTop ∧
        HasGenusTwoNoRationalTailNoRationalBridge (((𝒯).obj U).residueField u) g₀) :
    ∃ W : ((𝒯).obj U).Opens, u ∈ W ∧
      ∀ (pG : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
        (c : pG.siteObject ⟶ U), c ≫ φ = pG.value → Set.range ((𝒯).map c) ⊆ W →
        HasGenusTwoNoRationalTailNoRationalBridge pG.carrier ((𝒯).map (pullback.snd q c)) := by
  have : IsProper ((𝒯).map q) := isProper_toScheme_map_of_isPullback_schemeSpaceMap G sq
  have : Flat ((𝒯).map q) := flat_toScheme_map_of_isPullback G sq
  have : LocallyOfFinitePresentation ((𝒯).map q) :=
    locallyOfFinitePresentation_toScheme_map_of_isPullback G sq
  have hnod : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne ((𝒯).map q) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget q).1
      ((Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase
        hZ).of_isPullback sq hG.1)
  have hstd : ∀ (pG : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
      (c : pG.siteObject ⟶ U), c ≫ φ = pG.value →
      IsProper ((𝒯).map (pullback.snd q c)) ∧
        Function.Bijective ((𝒯).map (pullback.snd q c)).appTop ∧
        topologicalKrullDim ((𝒯).obj (pullback q c)) = 1 ∧
        @Stacks.Curves.HasAtWorstNodalSingularities pG.carrier _ ((𝒯).obj (pullback q c))
          ⟨(𝒯).map (pullback.snd q c)⟩ := by
    intro pG c hc
    obtain ⟨hprop, hH0, hdim, hnodal⟩ := fibre_standing_of_isPrestableCurveFamily hG
      (isPullback_presentation_of_factors sq pG c hc)
    refine ⟨hprop, ?_, hdim, hnodal⟩
    have : IsIso ((𝒯).map (pullback.snd q c)).appTop :=
      IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of pG.carrier)).inv _
    exact ConcreteCategory.bijective_of_isIso _
  have hfib : ∀ t : (𝒯).obj U, ∃ (C : Scheme.{u}) (h : C ⟶ (𝒯).obj Z)
      (g : C ⟶ Spec (.of (((𝒯).obj U).residueField t))),
      IsPullback h g ((𝒯).map q) (((𝒯).obj U).fromSpecResidueField t) ∧
        Function.Bijective g.appTop := by
    intro t
    let pG := Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ).hom
      (residueFieldValuedPoint B hZ U t)
    let c : pG.siteObject ⟶ U := Space.residueFieldMap B integerBase hZ U t
      (B.residueField_spec_contains U.left.property t)
    obtain ⟨-, hbij, -, -⟩ := hstd pG c rfl
    exact ⟨_, _, _, (IsPullback.of_hasPullback q c).map (𝒯), hbij⟩
  obtain ⟨V, huV, hV⟩ := CurveFibres.exists_mem_forall_hasGenusTwoNoRationalTailNoRationalBridge
    ((𝒯).map q) hnod hfib u hu
  refine ⟨V, huV, fun pG c hc hcV => ?_⟩
  obtain ⟨hprop, hbij, hdim, hnodal⟩ := hstd pG c hc
  exact hV pG.carrier _ _ _ _ ((IsPullback.of_hasPullback q c).map (𝒯)) hcV hdim hbij hnodal

/-- **A prestable family of curves is stable near a point with stable fibre, over a scheme
chart** (Stacks 0E74 (1) ⟹ (2), the openness of Stacks 0E76, the step "after possibly shrinking
`U`, `Y → U` is a stable family" of Stacks 0E8A). Let `G` be a prestable family of curves and
`G ×_S U ≅ Z` a scheme chart along `φ : U ⟶ S` with `U` quasi-compact and quasi-separated. If the
fibre of `Z ⟶ U` over `u`, presented by `C₀` over `Spec κ(u)` with `H⁰(C₀, 𝒪) = κ(u)`, has genus
at least two and neither a rational tail nor a rational bridge, then there is an open `W ∋ u` of
`U` such that every family of curves mapping to `G` over a morphism of bases which factors
through `W` is stable. -/
theorem exists_mem_forall_isStableCurveFamily_of_isPullback
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G)
    {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ G.base} {p : schemeSpace Z ⟶ G.total}
    {q : Z ⟶ U} (sq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    [CompactSpace ((𝒯).obj U)] [QuasiSeparatedSpace ((𝒯).obj U)] (u : (𝒯).obj U)
    (hu : ∃ (C₀ : Scheme.{u}) (h₀ : C₀ ⟶ (𝒯).obj Z)
      (g₀ : C₀ ⟶ Spec (.of (((𝒯).obj U).residueField u))),
      IsPullback h₀ g₀ ((𝒯).map q) (((𝒯).obj U).fromSpecResidueField u) ∧
        Function.Bijective g₀.appTop ∧
        HasGenusTwoNoRationalTailNoRationalBridge (((𝒯).obj U).residueField u) g₀) :
    ∃ W : ((𝒯).obj U).Opens, u ∈ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G) (b : F.base ⟶ U), b ≫ φ = a.baseMap →
        Set.range ((𝒯).map b) ⊆ W → IsStableCurveFamily B hZ F := by
  obtain ⟨W, huW, hW⟩ :=
    exists_mem_forall_hasGenusTwoNoRationalTailNoRationalBridge_of_isPullback hG sq u hu
  refine ⟨W, huW, fun F a b hb hbW => ⟨isPrestableCurveFamily_of_hom a hG, fun pF => ?_⟩⟩
  let pG := Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap a.baseMap).hom pF
  let m : pF.siteObject ⟶ F.base := pF.value
  let c : pG.siteObject ⟶ U := m ≫ b
  have hc : c ≫ φ = pG.value := by
    change (m ≫ b) ≫ φ = m ≫ a.baseMap
    rw [Category.assoc, hb]
  have hcW : Set.range ((𝒯).map c) ⊆ W := by
    rintro _ ⟨y, rfl⟩
    change ((𝒯).map (m ≫ b)).base y ∈ W
    rw [Functor.map_comp]
    exact hbW ⟨((𝒯).map m).base y, rfl⟩
  have hsqG := isPullback_presentation_of_factors sq pG c hc
  have hcond := hW pG c hc hcW
  have hsq := AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian
  rw [yonedaEquiv_symm_value_map] at hsqG
  have hw : (yoneda.map (pullback.fst q c) ≫ p.hom) ≫ G.toBase.hom =
      (yoneda.map (pullback.snd q c) ≫ yonedaEquiv.symm pF.value) ≫
        (schemeSpaceMap a.baseMap).hom := by
    rw [Category.assoc]
    exact hsqG.w
  refine ⟨pullback q c, pullback.snd q c, hsq.lift _ _ hw,
    IsPullback.of_right ?_ (hsq.lift_snd _ _ _) hsq, hcond⟩
  rw [hsq.lift_fst]
  exact hsqG

/-- **Stability descends along base changes through which every field-valued point lifts over
the same field.** Let `Y` be a prestable family of curves and `aᵢ : Yᵢ ⟶ Y` morphisms of families
(cartesian squares) from stable families. If every field-valued point of the base of `Y` is the
image of a field-valued point of the base of some `Yᵢ` over the same field, then `Y` is stable
(Stacks 0E75): the fibre of `Y` over such a point is the fibre of `Yᵢ`. -/
theorem isStableCurveFamily_of_forall_fieldValuedPoint_eq_map {Y : CurveFamily B hZ}
    (hY : IsPrestableCurveFamily B hZ Y) {ι : Type*} {Yi : ι → CurveFamily B hZ}
    (a : ∀ i, Yi i ⟶ Y) (hst : ∀ i, IsStableCurveFamily B hZ (Yi i))
    (hlift : ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj,
      ∃ i, ∃ p' : Space.FieldValuedPoint B integerBase hZ (schemeSpace (Yi i).base).obj,
        Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap (a i).baseMap).hom p' =
          p) :
    IsStableCurveFamily B hZ Y := by
  refine ⟨hY, fun p => ?_⟩
  obtain ⟨i, p', rfl⟩ := hlift p
  obtain ⟨V, v, q, hq, hcond⟩ := (hst i).2 p'
  have hsq := AlgebraicSpaces.isPullback_hom B integerBase hZ (a i).cartesian
  refine ⟨V, v, q ≫ (a i).totalMap.hom, ?_, hcond⟩
  rw [yonedaEquiv_symm_value_map]
  exact hq.paste_horiz hsq

end CurveFamily

end AlgebraicGeometry
