module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistable
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionLowerSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneSchematicLocus
import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Families of curves with `H⁰ = κ` and fibres of dimension one (Stacks 0E6J)

Let `f : X ⟶ S` be a family of curves (Tag 0D4Z) such that `f_*𝒪_X = 𝒪_S`, and this holds after
every base change, and all of whose fibres have dimension one. These are the families defining
the open substack `Curves^{h0,1}` of Tag 0E6I. Then `f` is Cohen–Macaulay of relative dimension
one, so that the family is one of those defining the open substack `Curves^{CM,1}` of Tag 0E1F:
this is the inclusion `Curves^{h0,1} ⊂ Curves^{CM,1}` of Tag 0E6J.

The proof is the source's. At a point `x` of `X` lying over `s ∈ S`, choose a field-valued point
`Spec k ⟶ S` representing `s`; the base change `X_k ⟶ Spec k` is again a family of curves with
`H⁰(X_k, 𝒪_{X_k}) = k` and of dimension one, and both conditions at `x` may be read off it. The
algebraic space `X_k` is a scheme (Tag 0ADD), so that Tag 0BY5 applies to it: a proper scheme of
dimension one over `k` with only constant global functions is Cohen–Macaulay and
equidimensional of dimension one.

## Main definitions

* `AlgebraicGeometry.CurveFamily.ofIsPullback`: the family of curves obtained from a family by a
  cartesian square over its base, and `AlgebraicGeometry.CurveFamily.homOfIsPullback` its
  morphism to the given family.

## Main results

* `CurveFamily.isCohenMacaulayDimOneFamily_of_hasUniversallyBijectiveGlobalFunctions`:
  **Stacks 0E6J**, a family of curves with `f_*𝒪_X = 𝒪_S` universally and fibres of dimension
  one is Cohen–Macaulay of relative dimension one.
* `AlgebraicGeometry.CurveFamily.isCohenMacaulayDimOneFamily_of_base_eq_spec`: the same over the
  spectrum of a field, by Tags 0ADD and 0BY5.
* `AlgebraicGeometry.CurveFamily.fiberDimension_eq_of_hom`: the fibre dimension is unchanged
  along a morphism of families, so that, with
  `AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hom`, both conditions
  pass to every family of curves mapping to the given one.
* `AlgebraicGeometry.CurveFamily.isCohenMacaulayAt_iff_hom`: Cohen–Macaulayness at a point is read
  off any morphism of families.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_dimensionAtPoint_of_eq_spec`: over a field,
  relative dimension at a point is the dimension at that point.

## Implementation notes

The open substacks of the source are determined by their objects, and inclusion of open
substacks is inclusion of their objects (Tag 04YM), so the inclusion is stated objectwise, on the
category of families of curves of Tag 0D4Z: the hypotheses are the defining conditions of
`Curves^{h0,1}` in clause (1)(b) of Tag 0E6I, and the conclusion is
`AlgebraicGeometry.IsCohenMacaulayDimOneFamily`, the defining condition of `Curves^{CM,1}` in
clause (1)(b) of Tag 0E1F.

The condition `f_*𝒪_X = 𝒪_S`, universally, is
`AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions`: pullback of global regular functions
along every base change `X ×_S Y ⟶ Y` by an algebraic space `Y` over `S` is bijective. The
condition that the fibres have dimension one is that the fibre dimension of Tag 0D4M is one at
every point of `S`; in particular every fibre is nonempty. Over a field `k` the first condition
gives `H⁰(X_k, 𝒪_{X_k}) = k`, by base change along the identity of `Spec k`.

## References

* [Stacks Project, Tag 0E6J](https://stacks.math.columbia.edu/tag/0E6J)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E1F](https://stacks.math.columbia.edu/tag/0E1F)
* [Stacks Project, Tag 0BY5](https://stacks.math.columbia.edu/tag/0BY5)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
-/

/- The source states the inclusion for the open substacks
`Curves^{h0,1}` (Tag 0E6I) and `Curves^{CM,1}` (Tag 0E1F) of the algebraic
stack `Curves` (Tag 0D5A). Neither open substack is constructed in this library. The inclusion
of open substacks is the inequality of their object properties, which
this theorem gives through their characterizations (1) in Tags 0E6I and 0E1F. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### Base change of families of curves along a cartesian square -/

/-- The family of curves obtained from a family `X` by a cartesian square over a morphism
`g : V ⟶ S` into its base: the morphism `q : T ⟶ V` of the square, whose properties are those of
the structure morphism of `X` by base change. -/
def CurveFamily.ofIsPullback (X : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (g : V ⟶ X.base) {T : AlgebraicSpaces B integerBase hZ} (t : T ⟶ X.total)
    (q : T ⟶ schemeSpace V) (sq : IsPullback t q X.toBase (schemeSpaceMap g)) :
    CurveFamily B hZ where
  base := V
  total := T
  toBase := q
  flat := (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback sq X.flat
  proper := (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback sq X.proper
  finitePresentation :=
    (Space.isFinitePresentation_isStableUnderBaseChange B integerBase hZ).of_isPullback sq
      X.finitePresentation
  relativeDimensionLE x := by
    obtain ⟨e, he, hrel⟩ := X.relativeDimensionLE (Space.pointsMap B integerBase hZ T.obj t.hom x)
    refine ⟨e, he, ?_⟩
    exact (Space.hasRelativeDimensionAt_iff_of_isPullback' B integerBase hZ (e : ℕ∞)
      (AlgebraicSpaces.isPullback_hom B integerBase hZ sq).flip X.total.property
      (schemeSpace X.base).property (schemeSpace V).property
      (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        X.finitePresentation.1) x).mpr hrel

/-- The morphism of families of curves from the base change `CurveFamily.ofIsPullback` to the
family it was obtained from. -/
def CurveFamily.homOfIsPullback (X : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ}
    (g : V ⟶ X.base) {T : AlgebraicSpaces B integerBase hZ} (t : T ⟶ X.total)
    (q : T ⟶ schemeSpace V) (sq : IsPullback t q X.toBase (schemeSpaceMap g)) :
    X.ofIsPullback B hZ g t q sq ⟶ X :=
  ⟨g, t, sq⟩

/-! ### Fibre dimension along a morphism of families -/

/-- The fibre dimension of a family of curves at a point of its base is the fibre dimension of
any family it maps to, at the image point: the fibres correspond along the cartesian square of
the morphism, and relative dimension is unchanged by base change (part (1) of Tag 04NS). -/
theorem CurveFamily.fiberDimension_eq_of_hom {X Y : CurveFamily B hZ} (φ : Y ⟶ X)
    (y : Space.points B integerBase hZ (schemeSpace Y.base).obj) :
    Space.fiberDimension B integerBase hZ Y.toBase.hom y =
      Space.fiberDimension B integerBase hZ X.toBase.hom
        (Space.pointsMap B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom y) := by
  have sq := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  unfold Space.fiberDimension
  congr 1
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h x hx
    obtain ⟨w, hw, hwy⟩ := Space.exists_points_of_isPullback B integerBase hZ sq x y hx
    obtain ⟨e, he, hed⟩ := h w hwy
    exact ⟨e, hw ▸ (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ e w).mp he, hed⟩
  · intro h w hw
    obtain ⟨e, he, hed⟩ := h (Space.pointsMap B integerBase hZ _ φ.totalMap.hom w) (by
      rw [Space.pointsMap_apply_comm B integerBase hZ sq.w w, hw])
    exact ⟨e, (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ e w).mpr he, hed⟩

/-- Cohen–Macaulayness of a family of curves at a point of its total space is
Cohen–Macaulayness of any family it maps to, at the image point (Tag 0E10 along the cartesian
square of the morphism). -/
theorem CurveFamily.isCohenMacaulayAt_iff_hom {X Y : CurveFamily B hZ} (φ : Y ⟶ X)
    (w : Space.points B integerBase hZ Y.total.obj) :
    Space.IsCohenMacaulayAt B integerBase hZ Y.toBase.hom w ↔
      Space.IsCohenMacaulayAt B integerBase hZ X.toBase.hom
        (Space.pointsMap B integerBase hZ _ φ.totalMap.hom w) := by
  have h := Space.setOf_isCohenMacaulayAt_of_isPullback B integerBase hZ X.toBase
    (schemeSpaceMap φ.baseMap) (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian)
    X.flat X.finitePresentation.1
  exact Set.ext_iff.mp h w

/-- A family of curves mapping to a family of curves with surjective map on the points of total
spaces is Cohen–Macaulay of relative dimension one as soon as the source family is. -/
theorem CurveFamily.isCohenMacaulayDimOneFamily_of_hom_of_surjective {X Y : CurveFamily B hZ}
    (φ : Y ⟶ X) (hφ : Function.Surjective (Space.pointsMap B integerBase hZ _ φ.totalMap.hom))
    (hY : IsCohenMacaulayDimOneFamily B hZ Y) : IsCohenMacaulayDimOneFamily B hZ X := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨w, rfl⟩ := hφ x
    exact (CurveFamily.isCohenMacaulayAt_iff_hom B hZ φ w).mp (hY.1 w)
  · obtain ⟨w, rfl⟩ := hφ x
    exact (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ _ w).mp (hY.2 w)

/-! ### Proper curves over a field whose only global functions are constants -/

/-- The fibre of a morphism of schemes over a point of a one-point target is the whole source, so
the two have the same dimension. -/
theorem Scheme.Hom.topologicalKrullDim_fiber_of_subsingleton {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Subsingleton Y] (y : Y) : topologicalKrullDim (f.fiber y) = topologicalKrullDim X := by
  have hpre : f ⁻¹' {y} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr
      (Subsingleton.elim _ _))
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.isHomeomorph
    ((f.fiberHomeo y).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ X))))

/-- A morphism of the site whose morphism of algebraic spaces is proper is proper on underlying
schemes. -/
theorem isProper_toScheme_map_of_isProper_yoneda_map {S : Scheme.{u}} {hS : B.Contains S}
    {T U : BigFppfOver B S hS} (g : T ⟶ U) (hg : Space.IsProper B S hS (yoneda.map g)) :
    IsProper ((BigFppfOver.toScheme B S hS).map g) := by
  have hstab : (MorphismProperty.inverseImage
      (@IsProper.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsProper) (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@IsProper.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))).mp
    ((Space.presheaf_isProper_iff B S hS (yoneda.map g) (isAlgebraicSpace_yoneda B S hS T)
      (isAlgebraicSpace_yoneda B S hS U) (Functor.relativelyRepresentable.map yoneda g)).mp hg)

/-- Pullback of global regular functions along `schemeSpaceMap g` is bijective exactly when
pullback of global sections along the underlying morphism of schemes is. -/
private theorem bijective_globalFunctionsMap_iff_appTop {S : Scheme.{u}} {hS : B.Contains S}
    {T T' : BigFppfOver B S hS} (g : T ⟶ T') :
    Function.Bijective (Space.globalFunctionsMap B S hS (schemeSpaceMap g)) ↔
      Function.Bijective ((BigFppfOver.toScheme B S hS).map g).appTop := by
  have hnat (s : Space.globalFunctions' B S hS (yoneda.obj T')) :
      Space.globalFunctionsYonedaRingEquiv B S hS T
          (Space.globalFunctionsMap B S hS (schemeSpaceMap g) s) =
        ((BigFppfOver.toScheme B S hS).map g).appTop
          (Space.globalFunctionsYonedaRingEquiv B S hS T' s) :=
    Space.globalFunctionsMap_val_chart B S hS (schemeSpaceMap g)
      (Space.idEtaleChart B S hS T') (Space.idEtaleChart B S hS T) g
      (by change yoneda.map g ≫ 𝟙 _ = 𝟙 _ ≫ yoneda.map g; simp) s
  have hcomm : ⇑(Space.globalFunctionsYonedaRingEquiv B S hS T) ∘
        ⇑(Space.globalFunctionsMap B S hS (schemeSpaceMap g)) =
      ⇑((BigFppfOver.toScheme B S hS).map g).appTop ∘
        ⇑(Space.globalFunctionsYonedaRingEquiv B S hS T') :=
    funext hnat
  refine ((Space.globalFunctionsYonedaRingEquiv B S hS T).bijective.of_comp_iff'
    (Space.globalFunctionsMap B S hS (schemeSpaceMap g))).symm.trans ?_
  rw [hcomm]
  exact Function.Bijective.of_comp_iff _ (Space.globalFunctionsYonedaRingEquiv B S hS T').bijective

/-- Over a base with one point, the fibre dimension of the morphism of algebraic spaces given by a
morphism `g` of the site is the dimension of the source scheme. -/
private theorem fiberDimension_yoneda_map_of_subsingleton {T U : BigFppfOver B integerBase hZ}
    (g : T ⟶ U) [Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj U)]
    (hft : Space.IsFiniteType B integerBase hZ (yoneda.map g))
    (s : Space.points B integerBase hZ (yoneda.obj U)) :
    Space.fiberDimension B integerBase hZ (yoneda.map g) s =
      topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep s
  exact (Space.fiberDimension_yoneda_map_class B integerBase hZ g hft p).trans
    (Scheme.Hom.topologicalKrullDim_fiber_of_subsingleton _ _)

/-- **A family of curves over a field whose total space is a scheme.** Let `g`
be a morphism of the site whose target is the spectrum of a field `k` and whose morphism of
algebraic spaces is flat, proper and of finite presentation, bijective on global regular
functions, with fibres of dimension one. Then it is Cohen–Macaulay of relative dimension one:
the scheme `T` is proper of dimension one over `k` with only constant global functions, so it is
Cohen–Macaulay and equidimensional by Tag 0BY5. -/
theorem isCohenMacaulay_and_hasRelativeDimension_one_schemeSpaceMap
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hflat : Space.IsFlat B integerBase hZ (schemeSpaceMap g).hom)
    (hproper : Space.IsProper B integerBase hZ (schemeSpaceMap g).hom)
    (hfp : Space.IsFinitePresentation B integerBase hZ (schemeSpaceMap g).hom)
    (hΓ : Function.Bijective (Space.globalFunctionsMap B integerBase hZ (schemeSpaceMap g)))
    (hdim : ∀ y, Space.fiberDimension B integerBase hZ (schemeSpaceMap g).hom y = 1) :
    Space.IsCohenMacaulay B integerBase hZ (schemeSpaceMap g).hom ∧
      Space.HasRelativeDimension 1 B integerBase hZ (schemeSpaceMap g).hom := by
  set F := BigFppfOver.toScheme B integerBase hZ with hF
  have : Flat (F.map g) := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    Flat.isEtaleLocalOnSourceAndTarget g).mp hflat
  have : LocallyOfFinitePresentation (F.map g) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget g).mp hfp.1
  have : IsProper (F.map g) := isProper_toScheme_map_of_isProper_yoneda_map B g hproper
  have hfib : ∀ v, IsLocallyNoetherian ((F.map g).fiber v) := fun v =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (F.map g) v
  have hΓS : Function.Bijective (F.map g).appTop.hom :=
    (bijective_globalFunctionsMap_iff_appTop B g).mp hΓ
  have : Subsingleton (F.obj U) := hU ▸ inferInstance
  obtain ⟨v⟩ : Nonempty (F.obj U) := hU ▸ inferInstance
  have hdimS : topologicalKrullDim (F.obj T) = 1 :=
    (fiberDimension_yoneda_map_of_subsingleton B hZ g hproper.2.1
      ((Space.pointsEquivScheme B integerBase hZ U).symm v)).symm.trans (hdim _)
  have hBY5 : ∀ (Y : Scheme.{u}) (_ : Y = Spec (.of k)) {X : Scheme.{u}} (f : X ⟶ Y)
      [IsProper f], topologicalKrullDim X = 1 → Function.Bijective f.appTop.hom →
        IsCohenMacaulay X ∧ TopologicalSpace.Equidimensional X := by
    intro Y hY X f _ hdimX hΓX
    subst hY
    have : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hΓX
    exact ⟨isCohenMacaulay_of_isIso_globalSections_of_dimension_one k f hdimX,
      equidimensional_of_isIso_globalSections_of_dimension_one k f hdimX⟩
  obtain ⟨hcm, hequi⟩ := hBY5 _ hU (F.map g) hdimS hΓS
  have hne : Nonempty (F.obj T) := by
    rw [← not_isEmpty_iff, ← topologicalKrullDim_eq_bot_iff_isEmpty, hdimS]
    exact WithBot.one_ne_bot
  exact ⟨(isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec B hZ g k hU hfib).mpr hcm,
    (hasRelativeDimension_schemeSpaceMap_iff_equidimensional B hZ 1 g k hU inferInstance
      hne).mpr ⟨hequi, by exact_mod_cast hdimS⟩⟩

/-! ### Families of curves over a field -/

/-- When the target of a morphism of algebraic spaces is represented by an object of the site
whose underlying scheme is the spectrum of a field, relative dimension `d` at a point is
absolute dimension `d` at that point: over a field the fibre of a chart is the chart itself. -/
theorem Space.hasRelativeDimensionAt_iff_dimensionAtPoint_of_eq_spec {S : Scheme.{u}}
    {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {V : BigFppfOver B S hS} (k : Type u) [Field k]
    (hV : (BigFppfOver.toScheme B S hS).obj V = Spec (.of k)) (f : F ⟶ yoneda.obj V)
    (x : Space.points B S hS F) (d : ℕ∞) :
    Space.HasRelativeDimensionAt d B S hS f x ↔
      Space.dimensionAtPoint B S hS F hF x = (d : WithBot ℕ∞) := by
  have hT : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hiff := Space.holdsOnEveryEtaleChartAtPoint_iff_some B S hS
    (@HasFiberDimensionAt.{u} d) (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) hF hT f x
  have hgen : ∀ (Y : Scheme.{u}) (_ : Y = Spec (.of k)) {X : Scheme.{u}} (h : X ⟶ Y) (t : X),
      topologicalKrullDimAt (h.fiber (h t)) (h.asFiber t) = topologicalKrullDimAt X t := by
    intro Y hY X h t
    subst hY
    exact topologicalKrullDimAt_fiber_eq_of_field h t
  obtain ⟨U, a, ha, q, hq⟩ := Space.exists_etale_chart_at_point B S hS F hF x
  let c : Space.EtaleChartAtPoint B S hS f x :=
    { U := U
      V := V
      a := a
      b := 𝟙 (yoneda.obj V)
      h := yoneda.preimage (a ≫ f)
      a_etale := ha
      b_etale := Space.presheaf_etale_id B S hS V
      comm := by simp
      representative := q
      point := IsLocalRing.closedPoint q.carrier
      maps_to := hq }
  have hdimOfChart :
      HasFiberDimensionAt d
        (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
          (c.sourcePoint B S hS)) ↔
      Space.dimensionAtPoint B S hS F hF x = (d : WithBot ℕ∞) := by
    rw [hasFiberDimensionAt_ofSchemeHom_iff, hgen _ hV]
    exact (Space.dimensionAtPoint_eq_of_etale_chart B S hS F hF x c.U c.a c.a_etale
      c.representative c.maps_to).symm ▸ Iff.rfl
  exact ⟨fun hall ↦ hdimOfChart.mp (hall c), fun hdim ↦ hiff.mpr ⟨c, hdimOfChart.mpr hdim⟩⟩

/-- The condition `f_*𝒪_X = 𝒪_S` universally gives in particular that pullback of global
regular functions along the structure morphism of the family is bijective: this is the base
change along the identity of the base. -/
theorem HasUniversallyBijectiveGlobalFunctions.bijective_globalFunctionsMap
    {X : CurveFamily B hZ} (hX : HasUniversallyBijectiveGlobalFunctions B hZ X) :
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ X.toBase) := by
  have hfib := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
    (𝟙 (schemeSpace X.base))
  let e := hfib.isoIsPullback _ _ (IsPullback.id_horiz X.toBase)
  have hsnd := (hfib.isoIsPullback_hom_snd _ _ (IsPullback.id_horiz X.toBase)).symm
  have h := hX (schemeSpace X.base) (𝟙 _)
  rw [hsnd, Space.globalFunctionsMap_comp, RingHom.coe_comp] at h
  exact (Function.Bijective.of_comp_iff' (Space.globalFunctionsMap_bijective_of_iso B e) _).mp h

/-- **The inclusion over a field.** A family of curves over the spectrum of a field `k` whose
structure sheaf pushes forward to the structure sheaf of the base universally, and whose fibre has
dimension one, is Cohen–Macaulay of relative dimension one.

The total space is a scheme: it is separated and Noetherian, being proper over `Spec k`, and its
local rings have dimension at most one, so Tag 0ADD makes every point lie in a representable
open subspace. Replacing the family by the isomorphic family whose total space is that scheme,
Tag 0BY5 applies to it. -/
theorem CurveFamily.isCohenMacaulayDimOneFamily_of_base_eq_spec (Y : CurveFamily B hZ) (k : Type u)
    [Field k] (hU : (BigFppfOver.toScheme B integerBase hZ).obj Y.base = Spec (.of k))
    (hΓ : HasUniversallyBijectiveGlobalFunctions B hZ Y)
    (hdim : ∀ y, Space.fiberDimension B integerBase hZ Y.toBase.hom y = 1) :
    IsCohenMacaulayDimOneFamily B hZ Y := by
  -- the total space is a scheme
  have hsep : Space.IsAbsolutelySeparated B integerBase hZ B.contains_terminal Y.total.obj :=
    Space.isAbsolutelySeparated_of_isSeparated_to_affine B integerBase hZ B.contains_terminal
      Y.base (hU ▸ inferInstance) Y.toBase.hom Y.proper.1
  have hnoeth : Space.HasEtaleLocalProperty B integerBase hZ Y.total.obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B integerBase hZ
      Y.total.property (schemeSpace Y.base).property Y.toBase.hom Y.proper.2.1.1
      (Space.hasEtaleLocalProperty_of_representable B integerBase hZ (yoneda.obj Y.base)
        (fun T : Scheme.{u} => IsLocallyNoetherian T) Y.base (Iso.refl _)
        (by rw [hU]; infer_instance))
  have hdimle : Space.dimension B integerBase hZ Y.total.obj Y.total.property ≤ 1 := by
    refine iSup_le fun x => ?_
    obtain ⟨e, he, hrel⟩ := Y.relativeDimensionLE x
    rw [(Space.hasRelativeDimensionAt_iff_dimensionAtPoint_of_eq_spec B Y.total.property k hU
      Y.toBase.hom x e).mp hrel]
    exact_mod_cast he
  have hloc : ∀ x, Space.localRingDimension B integerBase hZ x ≤ 1 := fun x => by
    have h := (le_iSup (fun y : Space.points B integerBase hZ Y.total.obj =>
      (Space.localRingDimension B integerBase hZ y : WithBot ℕ∞)) x).trans
      ((Space.dimension_eq_iSup_localRingDimension B integerBase hZ Y.total.obj
        Y.total.property).symm.le.trans hdimle)
    exact_mod_cast h
  have hrep : Y.total.obj.IsRepresentable :=
    Space.isRepresentable_of_surjective_pointsMap_schematicLocus B integerBase hZ
      Y.total.property fun x =>
        (Space.mem_range_pointsMap_schematicLocus_iff B integerBase hZ _ x).2
          (Space.exists_isOpenSubspace_isRepresentable_of_localRingDimension_le_one B
            integerBase hZ Y.total.property hsep hnoeth x (hloc x))
  -- the isomorphic family whose total space is that scheme
  let e := Y.total.obj.reprW
  let E : schemeSpace Y.total.obj.reprX ≅ Y.total :=
    (ObjectProperty.fullyFaithfulι _).preimageIso e
  let h : Y.total.obj.reprX ⟶ Y.base := yoneda.preimage (e.hom ≫ Y.toBase.hom)
  have hid : schemeSpaceMap (𝟙 Y.base) = 𝟙 (schemeSpace Y.base) :=
    ObjectProperty.hom_ext _ (yoneda.map_id _)
  have sq : IsPullback E.hom (schemeSpaceMap h) Y.toBase (schemeSpaceMap (𝟙 Y.base)) := by
    rw [hid]
    refine IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ ?_⟩
    show e.hom ≫ Y.toBase.hom = yoneda.map h ≫ 𝟙 _
    rw [Category.comp_id]
    exact (Functor.map_preimage yoneda _).symm
  let Y' := Y.ofIsPullback B hZ (𝟙 Y.base) E.hom (schemeSpaceMap h) sq
  let φ : Y' ⟶ Y := Y.homOfIsPullback B hZ (𝟙 Y.base) E.hom (schemeSpaceMap h) sq
  have hΓ' := (CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hom φ
    hΓ).bijective_globalFunctionsMap
  have hdim' : ∀ y, Space.fiberDimension B integerBase hZ Y'.toBase.hom y = 1 := fun y =>
    (CurveFamily.fiberDimension_eq_of_hom B hZ φ y).trans (hdim _)
  have hY' : IsCohenMacaulayDimOneFamily B hZ Y' :=
    isCohenMacaulay_and_hasRelativeDimension_one_schemeSpaceMap B hZ h k hU Y'.flat Y'.proper
      Y'.finitePresentation hΓ' hdim'
  exact CurveFamily.isCohenMacaulayDimOneFamily_of_hom_of_surjective B hZ φ
    (Space.pointsMap_surjective_of_isIso B integerBase hZ e.hom) hY'

/-! ### The inclusion of `Curves^{h0,1}` in `Curves^{CM,1}` -/

/-- Every point of the total space of a family of curves with `f_*𝒪_X = 𝒪_S` universally and
fibres of dimension one lies in the image of a family over the spectrum of a field mapping to
it, and that family is Cohen–Macaulay of relative dimension one. -/
theorem CurveFamily.exists_hom_isCohenMacaulayDimOneFamily_of_field (X : CurveFamily B hZ)
    (hΓ : HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hdim : ∀ y, Space.fiberDimension B integerBase hZ X.toBase.hom y = 1)
    (x : Space.points B integerBase hZ X.total.obj) :
    ∃ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (w : Space.points B integerBase hZ Y.total.obj),
      Space.pointsMap B integerBase hZ _ φ.totalMap.hom w = x ∧
        IsCohenMacaulayDimOneFamily B hZ Y := by
  obtain ⟨p, hp⟩ := Quot.exists_rep (Space.pointsMap B integerBase hZ _ X.toBase.hom x)
  let K := p.siteObject B integerBase hZ (schemeSpace X.base).obj
  let v : K ⟶ X.base := p.value
  have hfib := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
    (schemeSpaceMap v)
  let Y := X.ofIsPullback B hZ v _ _ hfib
  let φ : Y ⟶ X := X.homOfIsPullback B hZ v _ _ hfib
  let q : Space.FieldValuedPoint B integerBase hZ (schemeSpace K).obj :=
    ⟨p.carrier, p.contained, p.toBase, 𝟙 K⟩
  have hq : Space.pointsMap B integerBase hZ _ (schemeSpaceMap v).hom
      (q.class B integerBase hZ _) = Space.pointsMap B integerBase hZ _ X.toBase.hom x := by
    refine Eq.trans ?_ hp
    refine congrArg (Quot.mk _) ?_
    show Space.FieldValuedPoint.mk p.carrier p.contained p.toBase (𝟙 K ≫ v) = p
    rw [Category.id_comp]
  obtain ⟨w, hw, -⟩ := Space.exists_points_of_isPullback B integerBase hZ
    (AlgebraicSpaces.isPullback_hom B integerBase hZ hfib) x _ hq.symm
  exact ⟨Y, φ, w, hw, Y.isCohenMacaulayDimOneFamily_of_base_eq_spec B hZ p.carrier rfl
    (CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hom φ hΓ)
    (fun y => (CurveFamily.fiberDimension_eq_of_hom B hZ φ y).trans (hdim _))⟩

/-- **Stacks 0E6J.** `Curves^{h0,1} ⊂ Curves^{CM,1}`: a family of curves `f : X ⟶ S` with
`f_*𝒪_X = 𝒪_S`, universally, and all of whose fibres have dimension one is Cohen–Macaulay of
relative dimension one.

At a point of `X` the family is the base change of the family over the spectrum of a field
representing the image point; that family is again of this kind, and is Cohen–Macaulay of
relative dimension one by Tag 0BY5
(`AlgebraicGeometry.CurveFamily.isCohenMacaulayDimOneFamily_of_base_eq_spec`). Both properties at a
point are read off a base change along the cartesian square (Tags 0E10 and 04NS). -/
@[stacks 0E6J "the objects of Curves^{h0,1} (f_*O_X = O_S universally and fibres of dimension 1) \
  lie in Curves^{CM,1} (Cohen-Macaulay of relative dimension 1)"]
theorem CurveFamily.isCohenMacaulayDimOneFamily_of_hasUniversallyBijectiveGlobalFunctions
    (X : CurveFamily B hZ) (hΓ : HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hdim : ∀ y, Space.fiberDimension B integerBase hZ X.toBase.hom y = 1) :
    IsCohenMacaulayDimOneFamily B hZ X := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨Y, φ, w, rfl, hY⟩ := X.exists_hom_isCohenMacaulayDimOneFamily_of_field B hZ hΓ hdim x
    exact (CurveFamily.isCohenMacaulayAt_iff_hom B hZ φ w).mp (hY.1 w)
  · obtain ⟨Y, φ, w, rfl, hY⟩ := X.exists_hom_isCohenMacaulayDimOneFamily_of_field B hZ hΓ hdim x
    exact (CurveFamily.hasRelativeDimensionAt_iff_hom B hZ φ _ w).mp (hY.2 w)

end AlgebraicGeometry

end

/-!
## The open substack `Curves^{h0,1}` of the stack of curves (towards Stacks 0E6I)

Stacks 0E6I cuts out of the stack of curves the open substack `Curves^{h0,1}` of families of
curves `f : X → S` with `f_*𝒪_X = 𝒪_S`, universally, and whose fibres have dimension `1`. Its
proof combines three inputs with the method of Section 0E0E:

* the locus of points `s` of the base where `κ(s) = H⁰(X_s, 𝒪_{X_s})` is open, and its formation
  commutes with base change (Stacks 0E0R);
* the locus where the fibres have dimension `1` is open (Stacks 0D4R);
* for a family all of whose fibres over fields `k` have `H⁰ = k`, `f_*𝒪_X = 𝒪_S` holds
  universally (Stacks 0E6B, part (a)).

This file proves the second input and every step of the assembly, including part (2) over a
field; the first and third inputs enter as explicit hypotheses `hopen` and `hpush`, in the
curve-family form stated here, so no declaration of this file carries a `stacks` attribute.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasFibresOfDimensionOne`: every fibre of the family has
  dimension `1` (in particular is nonempty).
* `AlgebraicGeometry.CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres`: for every morphism
  `Spec k → S` from the spectrum of a field, `k = H⁰(X_k, 𝒪_{X_k})`.
* `AlgebraicGeometry.IsH01CurveFamily`: `f_*𝒪_X = 𝒪_S` universally and the fibres have
  dimension `1`, the condition (1)(b) of Stacks 0E6I.

## Main results

* `AlgebraicGeometry.Space.fiberDimension_eq_comp_of_isPullback`: the fibre dimension of a base
  change along a cartesian square is the fibre dimension of the original morphism at the image
  point (Stacks 0D4N for an arbitrary cartesian square).
* `AlgebraicGeometry.isOpenCurvesLocus_hasFibresOfDimensionOne`: condition (o) of Section 0E0E
  for having fibres of dimension `1`, from Stacks 0D4R.
* `CurveFamily.hasBijectiveGlobalFunctionsOnFieldFibres_of_hasUniversallyBijectiveGlobalFunctions`:
  `f_*𝒪_X = 𝒪_S` universally implies `k = H⁰(X_k, 𝒪_{X_k})` on every fibre over a field.
* `AlgebraicGeometry.isOpenCurvesLocus_isH01CurveFamily_of`: condition (o) for `IsH01CurveFamily`,
  from the two inputs above.
* `AlgebraicGeometry.CurveFamily.hasFibresOfDimensionOne_curveFamilyOfSchemeMorphism_iff`: for a
  proper scheme `X` of dimension at most one over a field, the fibres have dimension `1` exactly
  when `dim(X) = 1`.
* `CurveFamily.hasBijectiveGlobalFunctionsOnFieldFibres_curveFamilyOfSchemeMorphism`:
  for such `X`, `H⁰(X, 𝒪_X) = k` gives `k' = H⁰(X_{k'}, 𝒪)` for every field extension in the site,
  by flat base change in degree zero.
* `AlgebraicGeometry.CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of`: for such
  `X`, condition (1)(b) of Stacks 0E6I holds exactly when `H⁰(X, 𝒪_X) = k` and `dim(X) = 1`, from
  the input Stacks 0E6B (a).
* `AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of`: the whole
  statement of Stacks 0E6I, parts (1) and (2), from the two inputs.

## Implementation notes

"`f_*𝒪_X = 𝒪_S`, universally" is `AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions`, as
for prestable families (Stacks 0E6T). The fibrewise condition `κ = H⁰` is read in the same
language, at the base changes along the morphisms `Spec k → S` of the site: pullback of global
regular functions along `X ×_S Spec k → Spec k` is bijective. That is the hypothesis (2) of Stacks
0E6B, and it is the specialization of `HasUniversallyBijectiveGlobalFunctions` to field spectra.

The dimension of a fibre is `AlgebraicGeometry.Space.fiberDimension`, the quantity (1) of Stacks
0D4M; it is `⊥` over a point with empty fibre, so "the fibres have dimension `1`" includes the
surjectivity of `f` noted in the source.

Part (2) is stated, as part (1) of Stacks 0E0E is, for the family of curves
`AlgebraicGeometry.curveFamilyOfSchemeMorphism` of a proper morphism `g : T ⟶ W` of the site with
`W = Spec k`; `H⁰(X, 𝒪_X) = k` is the bijectivity of pullback of global sections along
`X → Spec k`. The converse direction of part (2) passes through hypothesis (2) of Stacks 0E6B:
global sections of the quasi-compact, quasi-separated scheme `X` commute with the flat base change
`k → k'` (`AlgebraicGeometry.isPushout_appTop_of_flat`).

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0D4R](https://stacks.math.columbia.edu/tag/0D4R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The fibre dimension is unchanged by precomposition with an isomorphism of the source. -/
theorem fiberDimension_iso_comp {W X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : W ≅ X)
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    fiberDimension B S hS (e.hom ≫ f) = fiberDimension B S hS f := by
  have hsq : IsPullback (e.hom ≫ f) e.hom (𝟙 Y) f :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id]⟩
  have hiff (d : ℕ∞) (w : points B S hS W) :
      HasRelativeDimensionAt d B S hS (e.hom ≫ f) w ↔
        HasRelativeDimensionAt d B S hS f (pointsMap B S hS W e.hom w) :=
    hasRelativeDimensionAt_iff_of_isPullback' B S hS d hsq hX hY hY hf w
  have hcancel (x : points B S hS X) :
      pointsMap B S hS W e.hom (pointsMap B S hS X e.inv x) = x := by
    rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
  funext y
  unfold fiberDimension
  congr 1
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h x hx
    obtain ⟨n, hn, hle⟩ := h (pointsMap B S hS X e.inv x)
      (by rw [pointsMap_comp_apply, hcancel, hx])
    exact ⟨n, hcancel x ▸ (hiff n _).1 hn, hle⟩
  · intro h w hw
    obtain ⟨n, hn, hle⟩ := h (pointsMap B S hS W e.hom w) (by rw [← pointsMap_comp_apply, hw])
    exact ⟨n, (hiff n w).2 hn, hle⟩

/-- **Fibre dimension along a cartesian square** (Stacks 0D4N for an arbitrary cartesian
square). If `p : W ⟶ Z` is the base change of a morphism of finite type `f : X ⟶ Y` of algebraic
spaces along `g : Z ⟶ Y`, the fibre of `p` over `z` has the dimension of the fibre of `f` over
`g(z)`. -/
theorem fiberDimension_eq_comp_of_isPullback {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hf : IsFiniteType B S hS f) :
    fiberDimension B S hS p = fiberDimension B S hS f ∘ pointsMap B S hS Z g := by
  have hpb : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hZ hY
  have hfg : IsFiniteType B S hS (pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A C : AlgebraicSpaces B S hS⦄ (k : A ⟶ C) ↦ IsFiniteType B S hS k.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)) hf
  have hp : p = sq.flip.isoPullback.hom ≫ pullback.snd f g := sq.flip.isoPullback_hom_snd.symm
  rw [hp, fiberDimension_iso_comp _ _ hpb hZ hfg.1,
    fiberDimension_pullback_snd B S hS f g hX hY hZ hf]

end Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_curvesH01 :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
  inferInstance

local instance (priority := high) hasPullback_presheaf_curvesH01
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_curvesH01 B hZ).has_limit _

namespace CurveFamily

/-- **The fibres of a family of curves have dimension `1`.** Every point `s` of the base has a
fibre of dimension exactly `1` (quantity (1) of Stacks 0D4M); in particular no fibre is empty. -/
def HasFibresOfDimensionOne (X : CurveFamily B hZ) : Prop :=
  ∀ s : Space.points B integerBase hZ (schemeSpace X.base).obj,
    Space.fiberDimension B integerBase hZ X.toBase.hom s = ((1 : ℕ) : WithBot ℕ∞)

/-- **`k = H⁰(X_k, 𝒪_{X_k})` on every fibre over a field.** For every morphism `Spec k → S` of
the site from the spectrum of a field, pullback of global regular functions along the projection
`X ×_S Spec k → Spec k` is bijective. This is hypothesis (2) of Stacks 0E6B. -/
def HasBijectiveGlobalFunctionsOnFieldFibres (X : CurveFamily B hZ) : Prop :=
  ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ
      (ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap p.value).hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap p.value) ⟶
          schemeSpace p.siteObject))

variable {B hZ}

/-- `f_*𝒪_X = 𝒪_S` universally gives `k = H⁰(X_k, 𝒪_{X_k})` on every fibre over a field: it is
the special case of the base change along `Spec k → S`. -/
theorem hasBijectiveGlobalFunctionsOnFieldFibres_of_hasUniversallyBijectiveGlobalFunctions
    {X : CurveFamily B hZ} (hX : HasUniversallyBijectiveGlobalFunctions B hZ X) :
    HasBijectiveGlobalFunctionsOnFieldFibres B hZ X :=
  fun p => hX (schemeSpace p.siteObject) (schemeSpaceMap p.value)

/-- For a morphism of families of curves `F ⟶ G`, the fibre of `F` over a point `t` of its base
has the dimension of the fibre of `G` over the image of `t`: the square of the morphism is
cartesian. -/
theorem fiberDimension_toBase_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G) :
    Space.fiberDimension B integerBase hZ F.toBase.hom =
      Space.fiberDimension B integerBase hZ G.toBase.hom ∘
        Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
          (schemeSpaceMap a.baseMap).hom :=
  funext (fiberDimension_eq_of_hom B hZ a)

/-- For a morphism of families of curves `F ⟶ G`, the fibres of `F` have dimension `1` exactly
when the fibres of `G` over the image of the base of `F` do. -/
theorem hasFibresOfDimensionOne_iff_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G) :
    HasFibresOfDimensionOne B hZ F ↔
      ∀ t : Space.points B integerBase hZ (schemeSpace F.base).obj,
        Space.fiberDimension B integerBase hZ G.toBase.hom
          (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
            (schemeSpaceMap a.baseMap).hom t) = ((1 : ℕ) : WithBot ℕ∞) := by
  unfold HasFibresOfDimensionOne
  rw [fiberDimension_toBase_of_hom a]
  rfl

end CurveFamily

variable {B hZ}

/-- **Condition (o) of Stacks 0E0E for having fibres of dimension `1`.** The locus of points of
the base whose fibre has dimension `1` is open, the fibre dimension of a flat, proper morphism of
finite presentation being locally constant (Stacks 0D4R); and a family mapping to the given one
has fibres of dimension `1` exactly when its base maps into that locus. -/
theorem isOpenCurvesLocus_hasFibresOfDimensionOne :
    IsOpenCurvesLocus B hZ (CurveFamily.HasFibresOfDimensionOne B hZ) := by
  refine IsOpenCurvesLocus.of_points fun G => ?_
  refine ⟨Space.fiberDimension B integerBase hZ G.toBase.hom ⁻¹' {((1 : ℕ) : WithBot ℕ∞)},
    (Space.isLocallyConstant_fiberDimension B integerBase hZ G.total.property
      (schemeSpace G.base).property G.toBase.hom G.proper G.flat G.finitePresentation).isOpen_fiber
      _, fun F a => ?_⟩
  rw [CurveFamily.hasFibresOfDimensionOne_iff_of_hom a, Set.range_subset_iff]
  rfl

variable (B hZ) in
/-- **Condition (1)(b) of Stacks 0E6I.** A family of curves `f : X → S` with `f_*𝒪_X = 𝒪_S`,
this holding after arbitrary base change, and whose fibres have dimension `1`. -/
abbrev IsH01CurveFamily (X : CurveFamily B hZ) : Prop :=
  HasUniversallyBijectiveGlobalFunctions B hZ X ∧ CurveFamily.HasFibresOfDimensionOne B hZ X

/-- **Condition (o) of Stacks 0E0E for `Curves^{h0,1}`, from its two cohomological inputs.** If
the fibrewise condition `k = H⁰(X_k, 𝒪_{X_k})` satisfies condition (o) (the openness of its locus
and the compatibility of that locus with base change, Stacks 0E0R at `i = 0`), and if that
fibrewise condition implies `f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B, part (a)), then so does the
condition (1)(b) of Stacks 0E6I: it is the conjunction of the fibrewise condition with having
fibres of dimension `1`, whose locus is open by Stacks 0D4R. -/
theorem isOpenCurvesLocus_isH01CurveFamily_of
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X) :
    IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := (hopen.and isOpenCurvesLocus_hasFibresOfDimensionOne) G
  refine ⟨W, hW, fun F a => Iff.trans ?_ (hchar F a)⟩
  refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨hpush F h.1, h.2⟩⟩
  exact
    CurveFamily.hasBijectiveGlobalFunctionsOnFieldFibres_of_hasUniversallyBijectiveGlobalFunctions
      h.1

/-- **Stacks 0E6I, part (1), from its two cohomological inputs.** If the fibrewise condition
`k = H⁰(X_k, 𝒪_{X_k})` satisfies condition (o) of Stacks 0E0E (Stacks 0E0R at `i = 0`) and implies
`f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B, part (a)), then the strictly full subcategory
`Curves^{h0,1}` of families with `f_*𝒪_X = 𝒪_S` universally and fibres of dimension `1` is an open
substack of `Curves` — its inclusion is representable by algebraic spaces and an open immersion —
and the classifying morphism of a family of curves factors through it exactly when the family
satisfies these two conditions. -/
theorem curvesH01_isOpenSubstack_and_factors_iff_of
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        IsH01CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left)))) :=
  isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)

/-! ### Part (2): a proper scheme of dimension at most one over a field -/

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullback of global regular functions along the morphism of algebraic spaces represented by a
morphism `g` of the site is bijective exactly when pullback of global sections along the
underlying morphism of schemes is. -/
theorem bijective_globalFunctionsMap_schemeSpaceMap_iff {T T' : BigFppfOver B S hS}
    (g : T ⟶ T') :
    Function.Bijective (globalFunctionsMap B S hS (schemeSpaceMap g)) ↔
      Function.Bijective ((BigFppfOver.toScheme B S hS).map g).appTop :=
  bijective_globalFunctionsMap_iff_appTop B g

end Space

namespace CurveFamily

section OverField

variable (hpush : ∀ X : CurveFamily B hZ, HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
    HasUniversallyBijectiveGlobalFunctions B hZ X)
  {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
  (k : Type u) [Field k] (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
  (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
  (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)

include hW in
/-- For the family of curves of a proper scheme `X = T` of dimension at most one over a field
`k = W`, the fibres have dimension `1` exactly when `dim X = 1`: the base has one point, whose
fibre is `X`. -/
theorem hasFibresOfDimensionOne_curveFamilyOfSchemeMorphism_iff :
    HasFibresOfDimensionOne B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 := by
  set F := curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim
  have hsub : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj W) := by
    rw [hW]; infer_instance
  have hft : Space.IsFiniteType B integerBase hZ (yoneda.map g) := F.proper.2.1
  have key (s : Space.points B integerBase hZ (yoneda.obj W)) :
      Space.fiberDimension B integerBase hZ (yoneda.map g) s =
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
    exact fiberDimension_yoneda_map_of_subsingleton B hZ g hft s
  refine ⟨fun h => ?_, fun h s => (key s).trans h⟩
  obtain ⟨y⟩ : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj W) := hW ▸ inferInstance
  exact (key ((Space.pointsEquivScheme B integerBase hZ W).symm y)).symm.trans (h _)

include hW in
/-- For the family of curves of a proper scheme `X = T` over a field `k = W`, if `H⁰(X, 𝒪_X) = k`
then `k' = H⁰(X_{k'}, 𝒪_{X_{k'}})` for every morphism `Spec k' → Spec k` of the site from the
spectrum of a field: global sections commute with the flat base change `k → k'` (Stacks 02KH in
degree zero). -/
theorem hasBijectiveGlobalFunctionsOnFieldFibres_curveFamilyOfSchemeMorphism
    (hg : Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop) :
    HasBijectiveGlobalFunctionsOnFieldFibres B hZ
      (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) := by
  intro p
  let v : p.siteObject ⟶ W := p.value
  have hsite : IsPullback (yoneda.map (pullback.fst g v)) (yoneda.map (pullback.snd g v))
      (yoneda.map g) (yoneda.map v) :=
    Functor.map_isPullback yoneda (IsPullback.of_hasPullback g v)
  have hsp : IsPullback (schemeSpaceMap (pullback.fst g v)) (schemeSpaceMap (pullback.snd g v))
      (schemeSpaceMap g) (schemeSpaceMap v) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsite.w) hsite
  let e := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ (schemeSpaceMap g)
    (schemeSpaceMap v)).isoIsPullback _ _ hsp
  have he : (ObjectProperty.homMk (pullback.snd (schemeSpaceMap g).hom (schemeSpaceMap v).hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ (schemeSpaceMap g) (schemeSpaceMap v) ⟶
        schemeSpace p.siteObject) = e.hom ≫ schemeSpaceMap (pullback.snd g v) :=
    (IsPullback.isoIsPullback_hom_snd _ _ _ _).symm
  show Function.Bijective (Space.globalFunctionsMap B integerBase hZ
    (ObjectProperty.homMk (pullback.snd (schemeSpaceMap g).hom (schemeSpaceMap v).hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ (schemeSpaceMap g) (schemeSpaceMap v) ⟶
        schemeSpace p.siteObject))
  rw [he, Space.globalFunctionsMap_comp, RingHom.coe_comp]
  refine ((Space.globalFunctionsMapEquiv B integerBase hZ e).bijective.of_comp_iff' _).2 ?_
  rw [Space.bijective_globalFunctionsMap_schemeSpaceMap_iff]
  have hscheme : IsPullback ((BigFppfOver.toScheme B integerBase hZ).map (pullback.fst g v))
      ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd g v))
      ((BigFppfOver.toScheme B integerBase hZ).map g)
      ((BigFppfOver.toScheme B integerBase hZ).map v) :=
    Functor.map_isPullback (BigFppfOver.toScheme B integerBase hZ) (IsPullback.of_hasPullback g v)
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj W) := by
    rw [hW]; infer_instance
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj p.siteObject) :=
    inferInstanceAs (IsAffine (Spec (.of p.carrier)))
  have : Flat ((BigFppfOver.toScheme B integerBase hZ).map v) := by
    have h1 : Flat ((BigFppfOver.toScheme B integerBase hZ).map v ≫ eqToHom hW) :=
      inferInstance
    have h2 : (BigFppfOver.toScheme B integerBase hZ).map v =
        ((BigFppfOver.toScheme B integerBase hZ).map v ≫ eqToHom hW) ≫ eqToHom hW.symm := by
      simp
    rw [h2]
    infer_instance
  have := hproper
  have : CompactSpace ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B integerBase hZ).map g)
  have : QuasiSeparatedSpace ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
    quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B integerBase hZ).map g)
  have : IsIso ((BigFppfOver.toScheme B integerBase hZ).map g).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).2 hg
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isPushout_appTop_of_flat hscheme).isIso_inr_of_isIso

include hpush hW in
/-- For the family of curves of a proper scheme `X = T` over a field `k = W`, if the fibrewise
condition `k' = H⁰(X_{k'}, 𝒪)` implies `f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B, part (a)), then
`f_*𝒪_X = 𝒪_S` universally holds exactly when `H⁰(X, 𝒪_X) = H⁰(Spec k, 𝒪)`. -/
theorem hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_iff_of :
    HasUniversallyBijectiveGlobalFunctions B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop := by
  constructor
  · intro h
    have h1 := HasUniversallyBijectiveGlobalFunctions.bijective_globalFunctionsMap B hZ h
    exact (Space.bijective_globalFunctionsMap_schemeSpaceMap_iff g).1 h1
  · intro h
    exact hpush (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim)
      (hasBijectiveGlobalFunctionsOnFieldFibres_curveFamilyOfSchemeMorphism g k hW hflat
        hproper hlfp hqc hsep hqsep hdim h)

include hpush hW in
/-- **The condition (1)(b) of Stacks 0E6I on a proper scheme over a field, from Stacks 0E6B (a).**
For the family of curves of a proper scheme `X = T` of dimension at most one over a field
`k = W`: if the fibrewise condition `k' = H⁰(X_{k'}, 𝒪)` implies `f_*𝒪_X = 𝒪_S` universally
(Stacks 0E6B, part (a)), then `f_*𝒪_X = 𝒪_S` universally with fibres of dimension `1` holds
exactly when `H⁰(X, 𝒪_X) = k` and `dim(X) = 1`. -/
theorem isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of :
    IsH01CurveFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 := by
  have hcomp : ⇑((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop =
      ⇑((BigFppfOver.toScheme B integerBase hZ).map g).appTop ∘ ⇑(eqToHom hW).appTop := by
    rw [Scheme.Hom.comp_appTop]
    funext x
    exact ConcreteCategory.comp_apply _ _ x
  have hiso : Function.Bijective ⇑(eqToHom hW).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).1
      (inferInstanceAs (IsIso (Scheme.Γ.map (eqToHom hW).op)))
  rw [hcomp, Function.Bijective.of_comp_iff _ hiso]
  exact and_congr
    (hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hflat
      hproper hlfp hqc hsep hqsep hdim)
    (hasFibresOfDimensionOne_curveFamilyOfSchemeMorphism_iff g k hW hflat hproper hlfp hqc hsep
      hqsep hdim)

end OverField

end CurveFamily

/-- **Stacks 0E6I, parts (1) and (2), from its two cohomological inputs.** If the fibrewise
condition `k = H⁰(X_k, 𝒪_{X_k})` satisfies condition (o) of Stacks 0E0E (Stacks 0E0R at `i = 0`)
and implies `f_*𝒪_X = 𝒪_S` universally (Stacks 0E6B, part (a)), then `Curves^{h0,1} ⊂ Curves` is
an open substack such that
1. the classifying morphism of a family of curves `f : X → S` factors through it exactly when
   `f_*𝒪_X = 𝒪_S`, universally, and the fibres of `f` have dimension `1`;
2. for a proper scheme `X = T` of dimension at most one over a field `k = W`, the classifying
   morphism `Spec k → Curves` of `X` factors through it exactly when `H⁰(X, 𝒪_X) = k` and
   `dim(X) = 1`. -/
theorem curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        IsH01CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅
        curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1)) :=
  ⟨isOpenImmersion_curvesSubstackInclusion (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush),
    fun U y hy => factors_curvesSubstack_iff (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)
      U y hy,
    fun g k _ hW hflat hproper hlfp hqc hsep hqsep hdim U y hy e =>
      (factors_curvesSubstack_iff_of_iso (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)
        U y hy _ e).trans
        (CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush g k hW hflat
          hproper hlfp hqc hsep hqsep hdim)⟩

end AlgebraicGeometry

end
