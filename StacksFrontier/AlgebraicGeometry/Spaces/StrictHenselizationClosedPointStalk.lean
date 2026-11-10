module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalkPBCSets
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed point of the strict henselization of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `x̄` be a geometric point of `X`.  The
strict henselization `T = Spec(𝒪_{X, x̄})` and its canonical morphism `h : T ⟶ X` of
Stacks 04KG are `AlgebraicGeometry.Space.strictHenselizationObj` and
`AlgebraicGeometry.Space.strictHenselizationToSpace`.  This file supplies the facts about the
closed geometric point `t̄` of `T` that compute stalks there.

## Main definitions

* `AlgebraicGeometry.Space.strictHenselizationGeometricPoint`: the geometric point `t̄` of `T`
  given by the canonical lift of `x̄`; it lies over the closed point and `h ∘ t̄ = x̄`
  (`AlgebraicGeometry.Space.geometricPointMap_strictHenselizationGeometricPoint`).
* `AlgebraicGeometry.Space.strictHenselizationIdNeighborhood`: the identity chart of `T`
  with the lift `t̄`, as a small étale neighbourhood of `t̄`.

## Main results

* `AlgebraicGeometry.Space.isInitialStrictHenselizationIdNeighborhood`: that neighbourhood is
  initial.  An étale chart of `T` with a lift of `t̄` has a unique section through the lift,
  because `𝒪_{X, x̄}` is strictly henselian and `t̄` lies over its closed point.
* `AlgebraicGeometry.Space.bijective_geometricModuleStalkGerm_of_isInitial` and
  `AlgebraicGeometry.Space.bijective_etaleLocalRingGerm_of_isInitial`: at an initial small étale
  neighbourhood the germ maps of a module and of the structure sheaf are bijective.  So the
  stalk at `t̄` of an `𝒪_T`-module is its module of sections over `T`.
* `AlgebraicGeometry.Space.isFlat_strictHenselizationToSpace`: `h` is flat.

## References

* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

/-! ### Germs at an initial neighbourhood -/

section Initial

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **At an initial small étale neighbourhood the germ map of a module is bijective.**  Every
germ is the germ of a section over some neighbourhood, which restricts to the initial one, and
two sections over the initial neighbourhood with the same germ agree on a refinement, from which
the initial neighbourhood maps back by the identity. -/
theorem bijective_geometricModuleStalkGerm_of_isInitial (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (F : Modules.{u, m} B S hS X.1 X.2)
    {N₀ : SmallEtaleNeighborhood x} (h : IsInitial N₀) :
    Function.Bijective (geometricModuleStalkGerm B S hS X x F N₀) := by
  refine ⟨fun s t hst => ?_, fun z => ?_⟩
  · obtain ⟨M, f, hf⟩ := (geometricModuleStalkGerm_eq_iff B S hS X x F N₀ s t).1 hst
    have key : ∀ u : F.val.obj (Opposite.op N₀.chart),
        F.val.map (h.to M).hom.op (F.val.map f.hom.op u) = u := by
      intro u
      have hcomp : f.hom.op ≫ (h.to M).hom.op = 𝟙 (Opposite.op N₀.chart) := by
        rw [← op_comp]
        change (h.to M ≫ f).hom.op = _
        rw [h.hom_ext (h.to M ≫ f) (𝟙 N₀)]
        rfl
      refine (PresheafOfModules.map_comp_apply F.val f.hom.op (h.to M).hom.op u).symm.trans ?_
      refine (PresheafOfModules.congr_map_apply F.val hcomp u).trans ?_
      have e := F.val.presheaf.map_id (Opposite.op N₀.chart)
      exact congrArg (fun k : F.val.presheaf.obj (Opposite.op N₀.chart) ⟶
        F.val.presheaf.obj (Opposite.op N₀.chart) => ConcreteCategory.hom k u) e
    rw [← key s, ← key t, hf]
  · obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x F z
    exact ⟨F.val.map (h.to N).hom.op s, geometricModuleStalkGerm_map B S hS X x F (h.to N) s⟩

/-- **At an initial small étale neighbourhood the germ map of the structure sheaf is
bijective.**  The étale local ring is the colimit of the sections over the opposite of the
neighbourhood category, in which the initial neighbourhood is terminal. -/
theorem bijective_etaleLocalRingGerm_of_isInitial {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : GeometricPoint B S hS F) {N₀ : SmallEtaleNeighborhood x} (h : IsInitial N₀) :
    Function.Bijective (etaleLocalRingGerm B S hS F x (Opposite.op N₀)) := by
  have : IsIso (colimit.ι (SmallEtaleNeighborhood.sections (x := x)
      (liftedStructurePresheaf B S hS F)) (Opposite.op N₀)) :=
    isIso_ι_of_isTerminal h.op _
  unfold etaleLocalRingGerm
  rw [RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (colimit.ι (SmallEtaleNeighborhood.sections (x := x)
      (liftedStructurePresheaf B S hS F)) (Opposite.op N₀))).comp
    ULift.ringEquiv.symm.bijective

end Initial

/-! ### The closed geometric point of the strict henselization -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (ybar : GeometricPoint B S hS Y)

/-- **The closed geometric point `t̄` of the strict henselization `T = Spec(𝒪_{Y, ȳ})`**: the
canonical lift of `ȳ`, on the same algebraically closed field. -/
def strictHenselizationGeometricPoint :
    GeometricPoint B S hS (yoneda.obj (strictHenselizationObj hY ybar)) :=
  ⟨strictHenselizationLiftPoint hY ybar, ybar.property⟩

/-- The canonical morphism `T ⟶ Y` carries the lift of `ȳ` to the section defining `ȳ`. -/
theorem strictHenselizationToSpace_app_lift :
    (strictHenselizationToSpace hY ybar).app (Opposite.op ybar.val.siteObject)
      (strictHenselizationLift hY ybar) = ybar.val.value := by
  change (strictHenselizationNbhd hY ybar).chart.obj.hom.app _
    (strictHenselizationLift hY ybar ≫ strictHenselizationToChart hY ybar) = _
  rw [strictHenselizationLift_comp_toChart]
  exact (strictHenselizationNbhd hY ybar).point_comp

/-- **The canonical morphism `T ⟶ Y` carries `t̄` to `ȳ`.** -/
theorem geometricPointMap_strictHenselizationGeometricPoint :
    geometricPointMap (strictHenselizationToSpace hY ybar)
      (strictHenselizationGeometricPoint hY ybar) = ybar :=
  Subtype.ext (congrArg (fun v : Y.obj (Opposite.op ybar.val.siteObject) ↦
    ({ carrier := ybar.val.carrier, field := ybar.val.field,
       contained := ybar.val.contained, toBase := ybar.val.toBase,
       value := v } : FieldValuedPoint B S hS Y)) (strictHenselizationToSpace_app_lift hY ybar))

/-- The scheme-level geometric point of `T = Spec(𝒪_{Y, ȳ})` underlying `t̄`: the canonical
lift of the geometric point of the chosen chart. -/
abbrev strictHenselizationSchemePoint :
    _root_.AlgebraicGeometry.GeometricPoint (strictHenselizationScheme hY ybar) where
  residueField := (strictHenselizationChartPoint hY ybar).residueField
  hom := geometricPointToStrictHenselization (strictHenselizationSite hY ybar)
    (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
    (strictHenselizationChartPoint hY ybar)

/-- The point `t̄` lies over the closed point of `T`. -/
theorem strictHenselizationSchemePoint_default :
    (strictHenselizationSchemePoint hY ybar).hom
        (default : (strictHenselizationSchemePoint hY ybar).source) =
      IsLocalRing.closedPoint _ :=
  geometricPointToStrictHenselization_base_default _ _ _ _

/-- The lift of `ȳ` to `T`, as a morphism of schemes, is the canonical point of the strict
henselization of the chart. -/
theorem toScheme_map_strictHenselizationLift :
    (BigFppfOver.toScheme B S hS).map (strictHenselizationLift hY ybar) =
      (strictHenselizationSchemePoint hY ybar).hom :=
  toScheme_map_siteHomMk B S hS _ _

/-- **The identity chart of `T` with the lift `t̄`**, as a small étale neighbourhood of `t̄`. -/
def strictHenselizationIdNeighborhood :
    SmallEtaleNeighborhood (strictHenselizationGeometricPoint hY ybar) where
  chart := idChart B S hS (strictHenselizationObj hY ybar)
  point := strictHenselizationLift hY ybar
  point_comp := rfl

section Lift

variable {hY ybar}
variable (N : SmallEtaleNeighborhood (strictHenselizationGeometricPoint hY ybar))

/-- The structure morphism of an étale chart of `T`, as a morphism of the site. -/
abbrev chartToStrictHenselization : N.chart.obj.left ⟶ strictHenselizationObj hY ybar :=
  yonedaEquiv N.chart.obj.hom

/-- The Yoneda image of `chartToStrictHenselization N` is the structure morphism of the chart. -/
theorem yoneda_map_chartToStrictHenselization :
    yoneda.map (chartToStrictHenselization N) = N.chart.obj.hom :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map _)

/-- The structure morphism of an étale chart of `T`, as a morphism of schemes to `T`. -/
abbrev strictHenselizationChartSchemeMap :
    (BigFppfOver.toScheme B S hS).obj N.chart.obj.left ⟶ strictHenselizationScheme hY ybar :=
  (BigFppfOver.toScheme B S hS).map (chartToStrictHenselization N)

/-- The structure morphism of an étale chart of `T` is étale. -/
instance etale_strictHenselizationChartSchemeMap : Etale (strictHenselizationChartSchemeMap N) := by
  refine (presheaf_yoneda_map_etale_iff B S hS (chartToStrictHenselization N)).1 ?_
  rw [yoneda_map_chartToStrictHenselization]
  exact N.chart.property

/-- The lift of `t̄` to an étale chart of `T`, as a morphism of schemes out of the field
spectrum of `t̄`. -/
abbrev chartPointToStrictHenselization :
    (strictHenselizationSchemePoint hY ybar).source ⟶
      (BigFppfOver.toScheme B S hS).obj N.chart.obj.left :=
  (BigFppfOver.toScheme B S hS).map N.point

/-- The lift of `t̄` to the chart, followed by the structure morphism, is the lift of `ȳ` to
`T`. -/
theorem point_comp_chartToStrictHenselization :
    N.point ≫ chartToStrictHenselization N = strictHenselizationLift hY ybar := by
  have h := N.point_comp
  rw [← yoneda_map_chartToStrictHenselization] at h
  exact h

/-- A composite of morphisms of the site is equal to a third iff it is so on schemes. -/
private theorem comp_eq_iff_toScheme_map {X Y Z : BigFppfOver B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z} : f ≫ g = h ↔
      (BigFppfOver.toScheme B S hS).map f ≫ (BigFppfOver.toScheme B S hS).map g =
        (BigFppfOver.toScheme B S hS).map h :=
  ⟨fun e => by rw [← Functor.map_comp, e],
    fun e => hom_ext_toScheme B S hS (by rwa [Functor.map_comp])⟩

/-- On schemes, the lift of `t̄` to the chart, followed by the structure morphism, is `t̄`. -/
theorem chartPointToStrictHenselization_comp :
    chartPointToStrictHenselization N ≫ strictHenselizationChartSchemeMap N =
      (strictHenselizationSchemePoint hY ybar).hom :=
  (comp_eq_iff_toScheme_map.1 (point_comp_chartToStrictHenselization N)).trans
    (toScheme_map_strictHenselizationLift hY ybar)

/-- A morphism of the site from `T` to an étale chart of `T` which is a section of the chart's
structure morphism is one on schemes. -/
theorem toScheme_comp_strictHenselizationChartSchemeMap_eq_id
    {σ : strictHenselizationObj hY ybar ⟶ N.chart.obj.left}
    (hσ : σ ≫ chartToStrictHenselization N = 𝟙 _) :
    ((BigFppfOver.toScheme B S hS).map σ : strictHenselizationScheme hY ybar ⟶ _) ≫
        strictHenselizationChartSchemeMap N = 𝟙 (strictHenselizationScheme hY ybar) :=
  (comp_eq_iff_toScheme_map.1 hσ).trans ((BigFppfOver.toScheme B S hS).map_id _)

/-- A section through the lift exists on schemes. -/
theorem exists_strictHenselizationSchemeSection :
    ∃ t : strictHenselizationScheme hY ybar ⟶
        (BigFppfOver.toScheme B S hS).obj N.chart.obj.left,
      t ≫ strictHenselizationChartSchemeMap N = 𝟙 (strictHenselizationScheme hY ybar) ∧
        (strictHenselizationSchemePoint hY ybar).hom ≫ t = chartPointToStrictHenselization N :=
  exists_hom_of_strictlyHenselian (strictHenselizationSchemePoint hY ybar)
    (𝟙 (strictHenselizationScheme hY ybar))
    (strictHenselizationSchemePoint hY ybar).hom (Category.comp_id _)
    (strictHenselizationSchemePoint_default hY ybar) (strictHenselizationChartSchemeMap N)
    (chartPointToStrictHenselization N)
    (chartPointToStrictHenselization_comp N)

/-- The section through the lift, on schemes. -/
def strictHenselizationSchemeSection : strictHenselizationScheme hY ybar ⟶
    (BigFppfOver.toScheme B S hS).obj N.chart.obj.left :=
  (exists_strictHenselizationSchemeSection N).choose

/-- `strictHenselizationSchemeSection N` is a section of the chart's structure morphism. -/
theorem strictHenselizationSchemeSection_comp :
    strictHenselizationSchemeSection N ≫ strictHenselizationChartSchemeMap N =
      𝟙 (strictHenselizationScheme hY ybar) :=
  (exists_strictHenselizationSchemeSection N).choose_spec.1

/-- `strictHenselizationSchemeSection N` sends `t̄` to the lift of `t̄` to the chart. -/
theorem point_comp_strictHenselizationSchemeSection :
    (strictHenselizationSchemePoint hY ybar).hom ≫ strictHenselizationSchemeSection N =
      chartPointToStrictHenselization N :=
  (exists_strictHenselizationSchemeSection N).choose_spec.2

/-- `strictHenselizationSchemeSection N` is a morphism over the base. -/
theorem strictHenselizationSchemeSection_comp_structure :
    strictHenselizationSchemeSection N ≫ B.inclusion.map N.chart.obj.left.hom =
      B.inclusion.map (strictHenselizationObj hY ybar).hom := by
  have hw' : strictHenselizationChartSchemeMap N ≫
      B.inclusion.map (strictHenselizationObj hY ybar).hom =
      B.inclusion.map N.chart.obj.left.hom :=
    (B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map (Over.w (chartToStrictHenselization N)))
  refine (congrArg (fun k => strictHenselizationSchemeSection N ≫ k) hw').symm.trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ B.inclusion.map (strictHenselizationObj hY ybar).hom)
    (strictHenselizationSchemeSection_comp N)).trans ?_
  exact Category.id_comp _

/-- The section through the lift, as a morphism of the site. -/
def strictHenselizationSection : strictHenselizationObj hY ybar ⟶ N.chart.obj.left :=
  siteHomMk B S hS (strictHenselizationSchemeSection N)
    (strictHenselizationSchemeSection_comp_structure N)

/-- On schemes, `strictHenselizationSection N` is `strictHenselizationSchemeSection N`. -/
theorem toScheme_map_strictHenselizationSection :
    (BigFppfOver.toScheme B S hS).map (strictHenselizationSection N) =
      strictHenselizationSchemeSection N :=
  toScheme_map_siteHomMk B S hS _ _

/-- `strictHenselizationSection N` is a section of the chart's structure morphism. -/
theorem strictHenselizationSection_comp :
    strictHenselizationSection N ≫ chartToStrictHenselization N = 𝟙 _ := by
  refine comp_eq_iff_toScheme_map.2 ?_
  rw [toScheme_map_strictHenselizationSection, (BigFppfOver.toScheme B S hS).map_id]
  exact strictHenselizationSchemeSection_comp N

/-- `strictHenselizationSection N` sends the lift of `ȳ` to `T` to the lift of `t̄` to the
chart. -/
theorem strictHenselizationLift_comp_section :
    strictHenselizationLift hY ybar ≫ strictHenselizationSection N = N.point := by
  refine comp_eq_iff_toScheme_map.2 ?_
  rw [toScheme_map_strictHenselizationSection, toScheme_map_strictHenselizationLift]
  exact point_comp_strictHenselizationSchemeSection N

/-- The morphism of small étale neighbourhoods out of the identity neighbourhood. -/
def strictHenselizationIdNeighborhoodTo : strictHenselizationIdNeighborhood hY ybar ⟶ N where
  hom := ObjectProperty.homMk (CostructuredArrow.homMk (strictHenselizationSection N) (by
    change yoneda.map (strictHenselizationSection N) ≫ N.chart.obj.hom = 𝟙 _
    rw [← yoneda_map_chartToStrictHenselization, ← Functor.map_comp,
      strictHenselizationSection_comp]
    exact yoneda.map_id _))
  point_comp := strictHenselizationLift_comp_section N

/-- Two morphisms out of the identity neighbourhood agree: both are sections, through the lift,
of an étale morphism to the spectrum of a strictly henselian local ring. -/
theorem strictHenselizationIdNeighborhood_hom_ext
    (m m' : strictHenselizationIdNeighborhood hY ybar ⟶ N) : m = m' := by
  have hsec : ∀ k : strictHenselizationIdNeighborhood hY ybar ⟶ N,
      k.hom.hom.left ≫ chartToStrictHenselization N = 𝟙 _ := by
    intro k
    apply yoneda.map_injective
    refine (yoneda.map_comp _ _).trans ?_
    refine Eq.trans ?_ (yoneda.map_id _).symm
    rw [yoneda_map_chartToStrictHenselization]
    exact CostructuredArrow.w k.hom.hom
  have hpt : ∀ k : strictHenselizationIdNeighborhood hY ybar ⟶ N,
      (strictHenselizationSchemePoint hY ybar).hom ≫
        (BigFppfOver.toScheme B S hS).map k.hom.hom.left = chartPointToStrictHenselization N := by
    intro k
    rw [← toScheme_map_strictHenselizationLift]
    exact comp_eq_iff_toScheme_map.1 k.point_comp
  have heq := Stacks.EtaleCohomology.eq_of_etale_section_of_comp_eq
    (strictHenselizationChartSchemeMap N)
    (strictHenselizationSchemePoint hY ybar).hom
    (strictHenselizationSchemePoint_default hY ybar)
    ((BigFppfOver.toScheme B S hS).map m.hom.hom.left)
    ((BigFppfOver.toScheme B S hS).map m'.hom.hom.left)
    (toScheme_comp_strictHenselizationChartSchemeMap_eq_id N (hsec m))
    (toScheme_comp_strictHenselizationChartSchemeMap_eq_id N (hsec m'))
    ((hpt m).trans (hpt m').symm)
  apply SmallEtaleNeighborhood.Hom.ext
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  exact hom_ext_toScheme B S hS heq

end Lift

/-- **The identity neighbourhood of `t̄` is initial among the small étale neighbourhoods of
`t̄`.**  This is where `𝒪_{Y, ȳ}` being strictly henselian, with `t̄` over its closed point, is
used. -/
def isInitialStrictHenselizationIdNeighborhood :
    IsInitial (strictHenselizationIdNeighborhood hY ybar) :=
  IsInitial.ofUniqueHom (fun N => strictHenselizationIdNeighborhoodTo N)
    (fun N m => strictHenselizationIdNeighborhood_hom_ext N m _)

/-! ### The étale local rings at `ȳ` and at `t̄` -/

section LocalRing

/-- The chosen chart of `Y`, as a small étale neighbourhood of the image `h ∘ t̄` of the closed
point of `T` (which is `ȳ`, by `geometricPointMap_strictHenselizationGeometricPoint`). -/
def strictHenselizationImageNbhd :
    SmallEtaleNeighborhood (geometricPointMap (strictHenselizationToSpace hY ybar)
      (strictHenselizationGeometricPoint hY ybar)) where
  chart := (strictHenselizationNbhd hY ybar).chart
  point := (strictHenselizationNbhd hY ybar).point
  point_comp := (strictHenselizationNbhd hY ybar).point_comp.trans
    (strictHenselizationToSpace_app_lift hY ybar).symm

/-- The chosen chart of `Y` lies in the big fppf site. -/
theorem contains_strictHenselizationChart : B.Contains (strictHenselizationChart hY ybar) :=
  (strictHenselizationNbhd hY ybar).chart.obj.left.left.property

variable {hY ybar} in
/-- A member of the small cofinal family of affine étale neighbourhoods of the geometric point of
the chosen chart lies in the big fppf site: it is affine and étale over the chart. -/
theorem contains_strictHenselizationAffineNbhd
    (a : etaleNeighborhoodAffineIndex (strictHenselizationSite hY ybar)
      (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
      (strictHenselizationChartPoint hY ybar)) :
    B.Contains ((etaleNeighborhoodAffineDiagram (strictHenselizationSite hY ybar)
      (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
      (strictHenselizationChartPoint hY ybar)).obj a) := by
  have : Etale ((strictHenselizationSite hY ybar).inclusion.map
      ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar)).obj a).1.obj.hom) :=
    ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
      (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
      (strictHenselizationChartPoint hY ybar)).obj a).1.property
  have : CompactSpace ((strictHenselizationSite hY ybar).inclusion.obj
      ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar)).obj a).1.obj.left) :=
    (inferInstance : CompactSpace ((etaleNeighborhoodAffineDiagram (strictHenselizationSite hY ybar)
      (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
      (strictHenselizationChartPoint hY ybar)).obj a))
  exact (Scheme.size_le_of_locallyOfFiniteType ((strictHenselizationSite hY ybar).inclusion.map
      ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar)).obj a).1.obj.hom)).trans_lt
    (contains_strictHenselizationChart hY ybar)

variable {hY ybar} in
/-- A member of the small cofinal family of affine étale neighbourhoods of the chosen chart, as a
refinement of the chosen chart in the small étale neighbourhoods of `h ∘ t̄`. -/
def strictHenselizationAffineRefinement
    (a : etaleNeighborhoodAffineIndex (strictHenselizationSite hY ybar)
      (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
      (strictHenselizationChartPoint hY ybar)) :
    Over (strictHenselizationImageNbhd hY ybar) :=
  chartRefinement (strictHenselizationImageNbhd hY ybar)
    (contains_strictHenselizationAffineNbhd a)
    ((strictHenselizationSite hY ybar).inclusion.map
      ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar)).obj a).1.obj.hom)
    ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar)).obj a).1.property
    ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar)).obj a).2.1
    ((etaleNeighborhoodAffineInclusion (strictHenselizationSite hY ybar)
        (strictHenselizationChart hY ybar) (contains_strictHenselizationSite hY ybar)
        (strictHenselizationChartPoint hY ybar)).obj a).2.2

end LocalRing

local notation "𝔈" => strictHenselizationSite hY ybar
local notation "𝔙" => strictHenselizationChart hY ybar
local notation "𝔥" => contains_strictHenselizationSite hY ybar
local notation "𝔳" => strictHenselizationChartPoint hY ybar

variable {hY ybar} in
/-- The leg at a member of the small affine family of the cone exhibiting `T` as the limit of
the étale neighbourhoods of the chosen chart, as a morphism of the site into the corresponding
refinement of the chart. -/
def strictHenselizationAffineSection (a : etaleNeighborhoodAffineIndex 𝔈 𝔙 𝔥 𝔳) :
    strictHenselizationObj hY ybar ⟶ (strictHenselizationAffineRefinement a).left.chart.obj.left :=
  siteHomMk B S hS ((strictHenselizationAffineCone 𝔈 𝔙 𝔥 𝔳).π.app a) (by
    change (strictHenselizationAffineCone 𝔈 𝔙 𝔥 𝔳).π.app a ≫
        ((𝔈).inclusion.map ((etaleNeighborhoodAffineInclusion 𝔈 𝔙 𝔥 𝔳).obj a).1.obj.hom ≫
          B.inclusion.map (strictHenselizationNbhd hY ybar).chart.obj.left.hom) =
      strictHenselizationSchemeToChart hY ybar ≫
        B.inclusion.map (strictHenselizationNbhd hY ybar).chart.obj.left.hom
    rw [← Category.assoc, strictHenselizationAffineCone_π_comp_hom_eq]
    rfl)

variable {hY ybar} in
/-- **The canonical homomorphism `𝒪_{Y, ȳ} ⟶ 𝒪_{T, t̄}` on a germ at an affine refinement of the
chosen chart**: the germ of the pullback of the function along the leg of the limit cone, at the
identity neighbourhood of `t̄`. -/
theorem etaleLocalRingMap_germ_strictHenselizationAffineRefinement
    (a : etaleNeighborhoodAffineIndex 𝔈 𝔙 𝔥 𝔳)
    (b : Γ((etaleNeighborhoodAffineDiagram 𝔈 𝔙 𝔥 𝔳).obj a, ⊤)) :
    etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS (strictHenselizationObj hY ybar))
        (strictHenselizationToSpace hY ybar) (strictHenselizationGeometricPoint hY ybar)
        (etaleLocalRingGerm B S hS Y _ (Opposite.op (strictHenselizationAffineRefinement a).left)
          b) =
      etaleLocalRingGerm B S hS _ (strictHenselizationGeometricPoint hY ybar)
        (Opposite.op (strictHenselizationIdNeighborhood hY ybar))
        (((strictHenselizationAffineCone 𝔈 𝔙 𝔥 𝔳).π.app a).appTop.hom b) := by
  let ι := (strictHenselizationAffineRefinement a).hom
  have hw : yoneda.map ι.hom.hom.left ≫ (strictHenselizationImageNbhd hY ybar).chart.obj.hom =
      (strictHenselizationAffineRefinement a).left.chart.obj.hom :=
    CostructuredArrow.w ι.hom.hom
  have hk : strictHenselizationToChart hY ybar =
      strictHenselizationAffineSection a ≫ ι.hom.hom.left := by
    refine (comp_eq_iff_toScheme_map.2 ?_).symm
    exact strictHenselizationAffineCone_π_comp_hom_eq 𝔈 𝔙 𝔥 𝔳 a
  have hcomm : (strictHenselizationIdNeighborhood hY ybar).chart.obj.hom ≫
      strictHenselizationToSpace hY ybar =
      yoneda.map (strictHenselizationAffineSection a) ≫
        (strictHenselizationAffineRefinement a).left.chart.obj.hom := by
    have e1 : strictHenselizationToSpace hY ybar =
        yoneda.map (strictHenselizationAffineSection a) ≫
          (yoneda.map ι.hom.hom.left ≫ (strictHenselizationImageNbhd hY ybar).chart.obj.hom) := by
      rw [← Category.assoc, ← Functor.map_comp, ← hk]
      rfl
    rw [hw] at e1
    exact (Category.id_comp _).trans e1
  have hpoint : (strictHenselizationIdNeighborhood hY ybar).point ≫
      strictHenselizationAffineSection a = (strictHenselizationAffineRefinement a).left.point := by
    exact comp_eq_iff_toScheme_map.2
      (geometricPointToStrictHenselization_comp_strictHenselizationAffineCone_π_app 𝔈 𝔙 𝔥 𝔳 a)
  exact (RingHom.congr_fun (etaleLocalRingMap_isEtaleLocalRingMap
    (isAlgebraicSpace_yoneda B S hS (strictHenselizationObj hY ybar))
    (strictHenselizationToSpace hY ybar) (strictHenselizationGeometricPoint hY ybar)
    (strictHenselizationIdNeighborhood hY ybar) (strictHenselizationAffineRefinement a).left
    (strictHenselizationAffineSection a) hcomm hpoint) b).symm

variable {hY ybar} in
/-- **The comparison of Stacks 04KF on a germ at an affine refinement of the chosen chart**: it
is the pullback of the function along the leg of the limit cone, read in the étale local ring of
the chart through `Γ(Spec R, 𝒪) = R`. -/
theorem etaleLocalRingEquivChart_germ_strictHenselizationAffineRefinement
    (a : etaleNeighborhoodAffineIndex 𝔈 𝔙 𝔥 𝔳)
    (b : Γ((etaleNeighborhoodAffineDiagram 𝔈 𝔙 𝔥 𝔳).obj a, ⊤)) :
    (etaleLocalRingEquivChart hY (strictHenselizationImageNbhd hY ybar) 𝔈 𝔥).val
        (etaleLocalRingGerm B S hS Y _ (Opposite.op (strictHenselizationAffineRefinement a).left)
          b) =
      (Scheme.ΓSpecIso (CommRingCat.of ↥(_root_.AlgebraicGeometry.etaleLocalRing 𝔈 𝔙 𝔥 𝔳))).hom.hom
        (((strictHenselizationAffineCone 𝔈 𝔙 𝔥 𝔳).π.app a).appTop.hom b) :=
  ((etaleLocalRingEquivChart hY (strictHenselizationImageNbhd hY ybar) 𝔈 𝔥).property.2
      (strictHenselizationAffineRefinement a).left (strictHenselizationAffineRefinement a).hom
      (Opposite.op ((etaleNeighborhoodAffineInclusion 𝔈 𝔙 𝔥 𝔳).obj a)) b rfl HEq.rfl
      HEq.rfl).trans
    (strictHenselizationCone_π_appTop_affine 𝔈 𝔙 𝔥 𝔳 a b).symm

/-- **The canonical homomorphism of étale local rings `𝒪_{Y, ȳ} ⟶ 𝒪_{T, t̄}` is bijective**,
for `T = Spec(𝒪_{Y, ȳ})` and its closed point `t̄`.  It is the composite of the comparison
`𝒪_{Y, ȳ} ≅ R` of Stacks 04KF with the chosen chart, of `R = Γ(T, 𝒪_T)`, and of the germ at the
initial neighbourhood of `t̄`: every germ is the germ at an affine refinement of the chart of a
function whose pullback to `T` along the leg of the limit cone represents it in `R`. -/
theorem bijective_etaleLocalRingMap_strictHenselizationToSpace :
    Function.Bijective (etaleLocalRingMap
      (isAlgebraicSpace_yoneda B S hS (strictHenselizationObj hY ybar))
      (strictHenselizationToSpace hY ybar) (strictHenselizationGeometricPoint hY ybar)) := by
  let e := (etaleLocalRingEquivChart hY (strictHenselizationImageNbhd hY ybar) 𝔈 𝔥).val
  let ρ := (Scheme.ΓSpecIso (CommRingCat.of
    ↥(_root_.AlgebraicGeometry.etaleLocalRing 𝔈 𝔙 𝔥 𝔳))).commRingCatIsoToRingEquiv
  let g := etaleLocalRingGerm B S hS _ (strictHenselizationGeometricPoint hY ybar)
    (Opposite.op (strictHenselizationIdNeighborhood hY ybar))
  have hg : Function.Bijective g := bijective_etaleLocalRingGerm_of_isInitial B S hS _
    (isInitialStrictHenselizationIdNeighborhood hY ybar)
  have key : ∀ z, etaleLocalRingMap
      (isAlgebraicSpace_yoneda B S hS (strictHenselizationObj hY ybar))
      (strictHenselizationToSpace hY ybar) (strictHenselizationGeometricPoint hY ybar) z =
        g (ρ.symm (e z)) := by
    intro z
    obtain ⟨a, b, hab⟩ := exists_appTop_π_eq_of_isLimit
      (etaleNeighborhoodAffineDiagram 𝔈 𝔙 𝔥 𝔳) (strictHenselizationAffineCone 𝔈 𝔙 𝔥 𝔳)
      (strictHenselizationAffineConeIsLimit 𝔈 𝔙 𝔥 𝔳) (ρ.symm (e z))
    have hz : z = etaleLocalRingGerm B S hS Y _
        (Opposite.op (strictHenselizationAffineRefinement a).left) b := by
      apply e.injective
      refine Eq.trans ?_
        (etaleLocalRingEquivChart_germ_strictHenselizationAffineRefinement a b).symm
      refine (ρ.apply_symm_apply (e z)).symm.trans ?_
      exact congrArg ρ hab
    rw [hab, hz]
    exact etaleLocalRingMap_germ_strictHenselizationAffineRefinement a b
  have hb : Function.Bijective (fun z => g (ρ.symm (e z))) :=
    hg.comp (ρ.symm.bijective.comp e.bijective)
  convert hb using 1
  funext z
  exact key z


/-! ### Flatness -/

/-- **The canonical morphism `Spec(𝒪_{Y, ȳ}) ⟶ Y` is flat**: it is the flat morphism of
schemes from the strict henselization of the chosen chart to that chart, followed by the étale
chart. -/
@[sga "4 XVII 5.5.29" "more general"]
theorem isFlat_strictHenselizationToSpace :
    IsFlat B S hS (strictHenselizationToSpace hY ybar) :=
  isFlat_comp B S hS (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hY
    _ _ ((holdsOnEveryEtaleChart_yoneda_map_iff B S hS Flat.isEtaleLocalOnSourceAndTarget
      (strictHenselizationToChart hY ybar)).2 (flat_strictHenselizationSchemeToChart hY ybar))
    (isFlat_of_isEtale B S hS (isEtale_strictHenselizationNbhd_hom hY ybar))

end AlgebraicGeometry.Space

end
