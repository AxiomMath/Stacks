module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FilteredColimitComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint

/-!
# The étale local ring of an algebraic space at a scheme chart

Let `x` be a geometric point of an algebraic space `F` over a scheme `S` and let `V` be a small
étale neighbourhood of `x`, that is, a scheme chart of `F` carrying a lift of `x`.  The étale
local ring of `F` at `x` (Stacks 04KG) is canonically the étale local ring of the scheme
underlying `V` at the induced geometric point (Stacks 03PS), and hence, by Stacks 04HX, the
strict henselization of the ordinary local ring of that scheme.

## Main definitions

* `AlgebraicGeometry.Space.neighborhoodChartScheme` and
  `AlgebraicGeometry.Space.chartGeometricPoint` extract the scheme and the geometric point from
  a small étale neighbourhood, and `AlgebraicGeometry.Space.neighborhoodChartMap` the morphism
  of schemes underlying a morphism of neighbourhoods.
* `AlgebraicGeometry.Space.etaleLocalRingEquivChart` is the comparison of the two étale local
  rings, and `AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing` its composite
  with the strict-henselization comparison of Stacks 04HX.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingEquivChart`: the two stalks agree by a ring
  equivalence which matches the germ of a chart section with its ordinary germ and, more
  precisely, matches germs at every pointed étale refinement common to the two sites.
* `AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing_germ` records what that
  composite does to an ordinary germ of a chart section.
* `AlgebraicGeometry.Space.commonToChart_initial` and
  `AlgebraicGeometry.Space.commonInclusion_initial` are the two cofinality statements the
  comparison rests on.

## Implementation notes

Both étale local rings are filtered colimits, but over different index categories: on the
space side the small étale neighbourhoods of `x`, on the scheme side the étale neighbourhoods
of the induced geometric point of the chart inside a chosen big étale site.  The comparison is
made by exhibiting a third category which is initial in both — the scheme étale neighbourhoods
whose scheme lies in both size cutoffs — and transporting the two colimit presentations to it
with `CommRingCat.ringEquivOfIsColimit`.  The chosen big étale site only selects a
size-bounded model of the small étale site of the chart;
`AlgebraicGeometry.Space.commonInclusion_initial` is what makes the comparison independent of
that choice, since affine neighbourhoods are small enough for any cutoff containing the chart.

The first comparison states the agreement of the two stalks on actual pointed étale germs
rather than only on global chart sections or their evaluations in the geometric field, which is
why its conclusion carries the refinement clause as well as the chart clause.  Its existence is
proved first and the comparison is then chosen from it, since the underlying bijection is only
determined up to the data of the two colimit presentations.

## References

* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : GeometricPoint B S hS F}

/-- The scheme underlying the chart of a small étale neighbourhood of a geometric point of an
algebraic space. -/
abbrev neighborhoodChartScheme (V : SmallEtaleNeighborhood x) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj V.chart.obj.left

/-- The geometric point of the chart selected by an étale neighborhood. -/
@[implicit_reducible]
noncomputable def chartGeometricPoint
    (V : SmallEtaleNeighborhood x) :
    _root_.AlgebraicGeometry.GeometricPoint (neighborhoodChartScheme V) where
  residueField := x.val.carrier
  field_residueField := x.val.field
  isAlgClosed_residueField := x.property
  hom := (BigFppfOver.toScheme B S hS).map V.point

/-- The scheme morphism underlying a morphism of pointed étale charts. -/
abbrev neighborhoodChartMap {W V : SmallEtaleNeighborhood x}
    (f : W ⟶ V) : neighborhoodChartScheme W ⟶ neighborhoodChartScheme V :=
  (BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS F).map f.hom)

/-- An étale refinement of a chart of the algebraic space by a scheme which the ambient big
fppf site contains, together with a lift of the geometric point, read as an object over that
chart in the small étale neighbourhoods of the point. -/
@[implicit_reducible]
def chartRefinement
    (V : SmallEtaleNeighborhood x)
    {W : Scheme.{u}} (hW : B.Contains W) (f : W ⟶ neighborhoodChartScheme V) (hf : Etale f)
    (p : (chartGeometricPoint V).source ⟶ W)
    (hp : p ≫ f = (chartGeometricPoint V).hom) :
    Over V := by
  let W' : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (f ≫ B.inclusion.map V.chart.obj.left.hom) :
      B.obj hW ⟶ B.obj hS)
  let f' : W' ⟶ V.chart.obj.left :=
    Over.homMk (ObjectProperty.homMk f) rfl
  let p' : x.val.siteObject ⟶ W' :=
    Over.homMk (ObjectProperty.homMk p) (by
      apply ObjectProperty.hom_ext
      change p ≫ (f ≫ B.inclusion.map V.chart.obj.left.hom) = _
      rw [← Category.assoc, hp]
      exact congrArg B.inclusion.map (Over.w V.point))
  have hpf : p' ≫ f' = V.point := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hp
  let N : SmallEtaleNeighborhood x := {
    chart := ⟨CostructuredArrow.mk (yoneda.map f' ≫ V.chart.obj.hom),
      etale_comp_of_scheme B S hS f' V.chart.obj.hom
        hf V.chart.property⟩
    point := p'
    point_comp := by
      change V.chart.obj.hom.app (Opposite.op x.val.siteObject) (p' ≫ f') = _
      rw [hpf]
      exact V.point_comp }
  exact Over.mk (show N ⟶ V from
    ⟨ObjectProperty.homMk (CostructuredArrow.homMk f' rfl), hpf⟩)

/-- The étale neighbourhoods, inside a chosen big étale site, of the geometric point selected
on the scheme underlying a chart of the algebraic space. -/
abbrev schemeNeighborhoods
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :=
  (geometricPointFiber E (neighborhoodChartScheme V) hV
    (chartGeometricPoint V)).Elements

/-- The property of such a scheme étale neighbourhood that its scheme is contained in the
ambient big fppf site as well, so that it is simultaneously a chart of the algebraic space. -/
abbrev commonNeighborhoodProperty
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    ObjectProperty (schemeNeighborhoods V E hV) :=
  fun U ↦ B.Contains ((_root_.AlgebraicGeometry.SmallEtale.toScheme E
    (neighborhoodChartScheme V) hV).obj U.1)

/-- A scheme étale neighbourhood of the selected point whose scheme both sites contain, read
as a refinement of the chart among the small étale neighbourhoods of the geometric point. -/
@[implicit_reducible]
def commonToChart
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    (commonNeighborhoodProperty V E hV).FullSubcategory ⥤ Over V where
  obj U := chartRefinement V U.property (E.inclusion.map U.obj.1.obj.hom)
    U.obj.1.property U.obj.2.1 U.obj.2.2
  map {U T} a := Over.homMk
    ⟨ObjectProperty.homMk (CostructuredArrow.homMk
      (Over.homMk (ObjectProperty.homMk
        ((_root_.AlgebraicGeometry.SmallEtale.toScheme E (neighborhoodChartScheme V) hV).map
          a.hom.1))
        (by
          apply ObjectProperty.hom_ext
          change _ ≫ (_ ≫ _) = _ ≫ _
          rw [← Category.assoc]
          exact congrArg (fun f ↦ f ≫ B.inclusion.map V.chart.obj.left.hom)
            (congrArg E.inclusion.map (Over.w a.hom.1.hom))))
      (by
        change yoneda.map _ ≫ (yoneda.map _ ≫ V.chart.obj.hom) =
          yoneda.map _ ≫ V.chart.obj.hom
        rw [← Category.assoc, ← Functor.map_comp]
        congr 2
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        exact congrArg E.inclusion.map (Over.w a.hom.1.hom))),
      by
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        exact congrArg Subtype.val a.hom.2⟩
    (by
      apply SmallEtaleNeighborhood.Hom.ext
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact congrArg E.inclusion.map (Over.w a.hom.1.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `AlgebraicGeometry.Space.commonToChart` is faithful: a morphism of scheme étale
neighbourhoods is determined by the morphism of schemes underlying it. -/
instance commonToChart_faithful
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    (commonToChart V E hV).Faithful where
  map_injective {U T} a b h := by
    apply ObjectProperty.hom_ext
    apply Functor.Elements.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact congrArg (fun f ↦ neighborhoodChartMap f.left) h

/-- `AlgebraicGeometry.Space.commonToChart` is full: a refinement of charts between two
neighbourhoods lying in both sites is itself a morphism of scheme étale neighbourhoods. -/
instance commonToChart_full
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    (commonToChart V E hV).Full where
  map_surjective {U T} a := by
    have ha : neighborhoodChartMap a.left ≫ E.inclusion.map T.obj.1.obj.hom =
        E.inclusion.map U.obj.1.obj.hom :=
      congrArg (fun f ↦ neighborhoodChartMap f) (Over.w a)
    refine ⟨ObjectProperty.homMk ⟨ObjectProperty.homMk
      (Over.homMk (ObjectProperty.homMk (neighborhoodChartMap a.left))
        (by
          apply ObjectProperty.hom_ext
          exact ha)), ?_⟩, ?_⟩
    · apply Subtype.ext
      exact congrArg (BigFppfOver.toScheme B S hS).map a.left.point_comp
    · apply Over.OverMorphism.ext
      apply SmallEtaleNeighborhood.Hom.ext
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      rfl

/-- A morphism from the spectrum of the residue field of a geometric point to a scheme
factors through an affine open neighbourhood of the image point. -/
lemma exists_affine_point_refinement {A W : Scheme.{u}}
    (s : _root_.AlgebraicGeometry.GeometricPoint A) (p : s.source ⟶ W) :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ W) (_ : _root_.AlgebraicGeometry.IsOpenImmersion j)
      (q : s.source ⟶ Spec R), q ≫ j = p := by
  obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := p.base (default : s.source)) (U := ⊤) (by simp)
  refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j p ?_⟩
  rintro _ ⟨a, rfl⟩
  rwa [Subsingleton.elim a default]

/-- A morphism of small étale neighbourhoods is étale on the underlying schemes. -/
private theorem etale_neighborhoodChartMap {W V : SmallEtaleNeighborhood x} (f : W ⟶ V) :
    Etale (neighborhoodChartMap f) :=
  etale_of_etale_charts B S hS W.chart.obj.hom V.chart.obj.hom W.chart.property V.chart.property
    f.hom.hom.left (CostructuredArrow.w f.hom.hom)

/-- The scheme étale neighbourhoods lying in both sites are initial among all the scheme
étale neighbourhoods of the selected point: every one of the latter is refined by an affine
one, which is small enough for both size cutoffs. -/
instance commonInclusion_initial
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    (commonNeighborhoodProperty V E hV).ι.Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro U
  obtain ⟨R, j, hj, q, hq⟩ :=
    exists_affine_point_refinement (chartGeometricPoint V) U.2.1
  let f := E.inclusion.map U.1.obj.hom
  have hE : E.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ f)).trans_lt hV
  have hB : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ f)).trans_lt V.chart.obj.left.left.property
  let T : _root_.AlgebraicGeometry.SmallEtale E (neighborhoodChartScheme V) hV :=
    ⟨Over.mk (ObjectProperty.homMk (j ≫ f) : E.obj (Spec R) hE ⟶
      E.obj (neighborhoodChartScheme V) hV), (show Etale (j ≫ f) from inferInstance)⟩
  have hqf : q ≫ (j ≫ f) = (chartGeometricPoint V).hom := by
    rw [← Category.assoc, hq]
    exact U.2.2
  exact ⟨⟨Functor.elementsMk _ T ⟨q, hqf⟩, hB⟩, ⟨Functor.Elements.homMk (ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk j) rfl)) (Subtype.ext hq)⟩⟩

/-- `AlgebraicGeometry.Space.commonToChart` is initial: every small étale neighbourhood
refining the chart is itself refined by a scheme étale neighbourhood lying in both sites. -/
theorem commonToChart_initial
    (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    (commonToChart V E hV).Initial := by
  have : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS F hF x
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro W
  let f := neighborhoodChartMap W.hom
  have hf : Etale f := etale_neighborhoodChartMap W.hom
  obtain ⟨R, j, hj, q, hq⟩ := exists_affine_point_refinement
    (chartGeometricPoint V) (chartGeometricPoint W.left).hom
  have hqf : q ≫ j ≫ f = (chartGeometricPoint V).hom := by
    rw [← Category.assoc, hq]
    exact congrArg (BigFppfOver.toScheme B S hS).map W.hom.point_comp
  have hE : E.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ f)).trans_lt hV
  have hB : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ f)).trans_lt V.chart.obj.left.left.property
  let T : _root_.AlgebraicGeometry.SmallEtale E (neighborhoodChartScheme V) hV :=
    ⟨Over.mk (ObjectProperty.homMk (j ≫ f) : E.obj (Spec R) hE ⟶
      E.obj (neighborhoodChartScheme V) hV), (show Etale (j ≫ f) from inferInstance)⟩
  let U : (commonNeighborhoodProperty V E hV).FullSubcategory :=
    ⟨Functor.elementsMk _ T ⟨q, hqf⟩, hB⟩
  let j' : ((commonToChart V E hV).obj U).left.chart.obj.left ⟶
      W.left.chart.obj.left := Over.homMk (ObjectProperty.homMk j) (by
        apply ObjectProperty.hom_ext
        change j ≫ _ = (j ≫ f) ≫ _
        rw [Category.assoc]
        congr 1
        exact (congrArg B.inclusion.map (Over.w W.hom.hom.hom.left)).symm)
  have hjf : j' ≫ W.hom.hom.hom.left =
      ((commonToChart V E hV).obj U).hom.hom.hom.left := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    rfl
  refine ⟨U, ⟨Over.homMk ⟨ObjectProperty.homMk
    (CostructuredArrow.homMk j' ?_), ?_⟩ ?_⟩⟩
  · have hw : yoneda.map W.hom.hom.hom.left ≫ V.chart.obj.hom =
        W.left.chart.obj.hom := by simp
    rw [← hw, ← Category.assoc, ← Functor.map_comp, hjf]
    rfl
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hq
  · apply SmallEtaleNeighborhood.Hom.ext
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact hjf

/-- The sections of the structure presheaf of the algebraic space over the small étale
neighbourhoods of the geometric point. -/
abbrev spaceSections :
    (SmallEtaleNeighborhood x)ᵒᵖ ⥤ CommRingCat.{u} :=
  SmallEtaleNeighborhood.sections (structurePresheaf B S hS F)

/-- The germ maps into the étale local ring of the algebraic space are compatible with
restriction of sections to a refinement. -/
lemma spaceGerm_naturality
    {U W : (SmallEtaleNeighborhood x)ᵒᵖ} (f : U ⟶ W) :
    (etaleLocalRingGerm B S hS F x W).comp (spaceSections.map f).hom =
      etaleLocalRingGerm B S hS F x U := by
  ext a
  exact congrArg (fun g ↦ g.hom (ULift.up a))
    (colimit.w (SmallEtaleNeighborhood.sections
      (liftedStructurePresheaf B S hS F)) f)

/-- The germ maps exhibit the étale local ring of the algebraic space as the colimit of the
sections of its structure presheaf over the small étale neighbourhoods of the point. -/
theorem spaceGerms_isColimit
    (hF : IsAlgebraicSpace B S hS F) :
    (CommRingCat.coconeTypesOfRingHoms spaceSections (etaleLocalRingGerm B S hS F x)
      (fun f ↦ spaceGerm_naturality f)).IsColimit := by
  have : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS F hF x
  let D := SmallEtaleNeighborhood.sections
    (x := x) (liftedStructurePresheaf B S hS F)
  have : FinallySmall.{u + 1} (SmallEtaleNeighborhood x)ᵒᵖ :=
    finallySmall_of_essentiallySmall _
  have : PreservesColimit D (forget CommRingCat.{u + 1}) :=
    preservesColimit_of_finallySmall.{u + 1, u, u + 1} (forget CommRingCat.{u + 1}) D
  exact ((Types.isColimit_iff_coconeTypesIsColimit _).mp
    ⟨isColimitOfPreserves (forget CommRingCat.{u + 1}) (colimit.isColimit D)⟩).precompose
    (G := spaceSections ⋙ forget CommRingCat.{u}) (fun _ ↦ Equiv.ulift.symm) (fun _ ↦ rfl)

/-- The global regular functions on the scheme étale neighbourhoods of the point selected on
a chart. -/
abbrev schemeSections
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    (schemeNeighborhoods V E hV)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.Elements.π (geometricPointFiber E (neighborhoodChartScheme V) hV
    (chartGeometricPoint V))).op ⋙
    (_root_.AlgebraicGeometry.SmallEtale.toScheme E (neighborhoodChartScheme V) hV).op ⋙ Scheme.Γ

/-- The germ map from the global regular functions on a scheme étale neighbourhood into the
étale local ring of the chart. -/
abbrev schemeGerm
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V))
    (U : (schemeNeighborhoods V E hV)ᵒᵖ) :
    (schemeSections V E hV).obj U →+*
      _root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme V) hV
        (chartGeometricPoint V) :=
  (colimit.ι ((Functor.Elements.π (geometricPointFiber E
      (neighborhoodChartScheme V) hV (chartGeometricPoint V))).op ⋙
      (_root_.AlgebraicGeometry.SmallEtale.structureSheaf E
        (neighborhoodChartScheme V) hV).obj) U).hom

/-- The germ maps into the étale local ring of the chart are compatible with restriction of
functions to a refinement. -/
lemma schemeGerm_naturality
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V))
    {U W : (schemeNeighborhoods V E hV)ᵒᵖ} (f : U ⟶ W) :
    (schemeGerm V E hV W).comp ((schemeSections V E hV).map f).hom =
      schemeGerm V E hV U := by
  ext a
  exact congrArg (fun g ↦ g.hom a) (colimit.w
    ((Functor.Elements.π (geometricPointFiber E
      (neighborhoodChartScheme V) hV (chartGeometricPoint V))).op ⋙
      (_root_.AlgebraicGeometry.SmallEtale.structureSheaf E (neighborhoodChartScheme V) hV).obj) f)

/-- The germ maps exhibit the étale local ring of the chart as the colimit of the global
regular functions over the scheme étale neighbourhoods of the selected point. -/
theorem schemeGerms_isColimit
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    (CommRingCat.coconeTypesOfRingHoms (schemeSections V E hV) (schemeGerm V E hV)
      (fun f ↦ schemeGerm_naturality V E hV f)).IsColimit := by
  let D := (Functor.Elements.π (geometricPointFiber E
    (neighborhoodChartScheme V) hV (chartGeometricPoint V))).op ⋙
      (_root_.AlgebraicGeometry.SmallEtale.structureSheaf E (neighborhoodChartScheme V) hV).obj
  have : PreservesColimit D (forget RingCat.{u}) :=
    preservesColimit_of_finallySmall (forget RingCat.{u}) D
  exact (Types.isColimit_iff_coconeTypesIsColimit _).mp
    ⟨isColimitOfPreserves (forget RingCat.{u}) (colimit.isColimit D)⟩

/-- The scheme étale neighbourhoods lying in both sites are cofiltered, being initial in the
cofiltered category of all of them. -/
instance commonNeighborhoods_cofiltered
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    IsCofiltered (commonNeighborhoodProperty V E hV).FullSubcategory := by
  let L := (commonNeighborhoodProperty V E hV).ι
  apply IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful L
  intro U
  have : IsConnected (CostructuredArrow L U) := Functor.Initial.out U
  obtain ⟨T⟩ := (inferInstance : Nonempty (CostructuredArrow L U))
  exact ⟨T.left, ⟨T.hom⟩⟩

/-- Comparing the two colimit presentations over the neighbourhoods common to both sites
gives a ring equivalence between the two étale local rings which respects the germ maps of
those common neighbourhoods. -/
def etaleLocalRingEquivOnCommonNeighborhoods
    (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    { e : etaleLocalRing B S hS F x ≃+*
        _root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme V) hV
          (chartGeometricPoint V) //
      ∀ (U : (commonNeighborhoodProperty V E hV).FullSubcategoryᵒᵖ)
        (a : (schemeSections V E hV).obj (Opposite.op U.unop.obj)),
        e (etaleLocalRingGerm B S hS F x
          (Opposite.op ((commonToChart V E hV).obj U.unop).left) a) =
          schemeGerm V E hV (Opposite.op U.unop.obj) a } := by
  have : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS F hF x
  have : (commonToChart V E hV).Initial := commonToChart_initial hF V E hV
  let L := ((commonToChart V E hV) ⋙ Over.forget V).op
  let K := (commonNeighborhoodProperty V E hV).ι.op
  exact CommRingCat.ringEquivOfIsColimit (L ⋙ spaceSections)
    (fun U ↦ etaleLocalRingGerm B S hS F x (L.obj U))
    (fun U ↦ schemeGerm V E hV (K.obj U))
    (fun f ↦ spaceGerm_naturality (L.map f))
    (fun f ↦ schemeGerm_naturality V E hV (K.map f))
    ((spaceGerms_isColimit hF).comp_final L)
    ((schemeGerms_isColimit V E hV).comp_final K)

/-- A scheme étale neighbourhood of a geometric point is determined by its scheme, its
structure morphism and its lift of the point. -/
lemma boundedNeighborhood_eq
    (E : BigEtaleSite.{u}) (A : Scheme.{u}) (hA : E.Contains A)
    (s : _root_.AlgebraicGeometry.GeometricPoint A)
    (U T : (geometricPointFiber E A hA s).Elements)
    (hs : (_root_.AlgebraicGeometry.SmallEtale.toScheme E A hA).obj U.1 =
      (_root_.AlgebraicGeometry.SmallEtale.toScheme E A hA).obj T.1)
    (hf : HEq (E.inclusion.map U.1.obj.hom) (E.inclusion.map T.1.obj.hom))
    (hp : HEq U.2.1 T.2.1) : U = T := by
  rcases U with @⟨⟨⟨⟨W, hW⟩, ⟨⟨⟩⟩, f⟩, hf'⟩, ⟨p, hp'⟩⟩
  rcases T with @⟨⟨⟨⟨W', hW'⟩, ⟨⟨⟩⟩, f'⟩, hf''⟩, ⟨p', hp''⟩⟩
  dsimp at hs
  subst W'
  obtain rfl : f = f' := by
    apply ObjectProperty.hom_ext
    exact eq_of_heq hf
  obtain rfl : p = p' := eq_of_heq hp
  rfl

/-- Refining a chart along a morphism of small étale neighbourhoods does not change the germ
of a section: the refinement carries the same chart, read through the identity. -/
lemma chartRefinement_germ
    (W V : SmallEtaleNeighborhood x) (f : W ⟶ V) (hf : Etale (neighborhoodChartMap f))
    (a : Γ(neighborhoodChartScheme W, ⊤)) :
    etaleLocalRingGerm B S hS F x
      (Opposite.op (chartRefinement V W.chart.obj.left.left.property (neighborhoodChartMap f) hf
        (chartGeometricPoint W).hom
        (congrArg (BigFppfOver.toScheme B S hS).map f.point_comp)).left) a =
      etaleLocalRingGerm B S hS F x (Opposite.op W) a := by
  let Z := chartRefinement V W.chart.obj.left.left.property (neighborhoodChartMap f) hf
    (chartGeometricPoint W).hom
    (congrArg (BigFppfOver.toScheme B S hS).map f.point_comp)
  let j' : Z.left.chart.obj.left ⟶ W.chart.obj.left :=
    Over.homMk (ObjectProperty.homMk (𝟙 (neighborhoodChartScheme W))) (by
      apply ObjectProperty.hom_ext
      change 𝟙 _ ≫ _ = neighborhoodChartMap f ≫ _
      rw [Category.id_comp]
      exact (congrArg B.inclusion.map (Over.w f.hom.hom.left)).symm)
  have hjf : j' ≫ f.hom.hom.left = Z.hom.hom.hom.left := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Category.id_comp _
  let j : Z.left ⟶ W := ⟨ObjectProperty.homMk (CostructuredArrow.homMk j' (by
      rw [← CostructuredArrow.w f.hom.hom, ← Category.assoc, ← Functor.map_comp, hjf]
      rfl)), by
        apply Over.OverMorphism.ext
        apply ObjectProperty.hom_ext
        exact Category.comp_id _⟩
  have h := DFunLike.congr_fun (spaceGerm_naturality j.op) a
  change etaleLocalRingGerm B S hS F x (Opposite.op Z.left)
    ((Scheme.Hom.appTop (𝟙 (neighborhoodChartScheme W))).hom a) = _ at h
  have hid : (Scheme.Hom.appTop (𝟙 (neighborhoodChartScheme W))).hom a = a := by
    simp
  rwa [hid] at h

/-- The comparison equivalence sends the germ of a section on any small étale neighbourhood
refining the chart to its germ on the corresponding scheme étale neighbourhood. -/
lemma etaleLocalRingEquivOnCommonNeighborhoods_germ
    (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V))
    (W : SmallEtaleNeighborhood x) (f : W ⟶ V)
    (U : (schemeNeighborhoods V E hV)ᵒᵖ) (a : Γ(neighborhoodChartScheme W, ⊤))
    (hs : neighborhoodChartScheme W =
      (_root_.AlgebraicGeometry.SmallEtale.toScheme E (neighborhoodChartScheme V) hV).obj U.unop.1)
    (hp : HEq (chartGeometricPoint W).hom U.unop.2.1)
    (hf : HEq (neighborhoodChartMap f) (E.inclusion.map U.unop.1.obj.hom)) :
    (etaleLocalRingEquivOnCommonNeighborhoods hF V E hV).val
      (etaleLocalRingGerm B S hS F x (Opposite.op W) a) =
      schemeGerm V E hV U (show Γ((_root_.AlgebraicGeometry.SmallEtale.toScheme E
        (neighborhoodChartScheme V) hV).obj U.unop.1, ⊤) from hs ▸ a) := by
  have hW : E.Contains (neighborhoodChartScheme W) := hs ▸ U.unop.1.obj.left.property
  have hf' : Etale (neighborhoodChartMap f) := etale_neighborhoodChartMap f
  let T : schemeNeighborhoods V E hV :=
    Functor.elementsMk _ ⟨Over.mk (ObjectProperty.homMk (neighborhoodChartMap f) :
      E.obj (neighborhoodChartScheme W) hW ⟶ E.obj (neighborhoodChartScheme V) hV), hf'⟩
      ⟨(chartGeometricPoint W).hom,
        congrArg (BigFppfOver.toScheme B S hS).map f.point_comp⟩
  obtain rfl : U = Opposite.op T := congrArg Opposite.op (boundedNeighborhood_eq E
    (neighborhoodChartScheme V) hV (chartGeometricPoint V) T U.unop hs hf hp).symm
  let C : (commonNeighborhoodProperty V E hV).FullSubcategory :=
    ⟨T, W.chart.obj.left.left.property⟩
  have h := (etaleLocalRingEquivOnCommonNeighborhoods hF V E hV).property
    (Opposite.op C) a
  change (etaleLocalRingEquivOnCommonNeighborhoods hF V E hV).val
    (etaleLocalRingGerm B S hS F x
      (Opposite.op (chartRefinement V W.chart.obj.left.left.property (neighborhoodChartMap f) hf'
        (chartGeometricPoint W).hom
        (congrArg (BigFppfOver.toScheme B S hS).map f.point_comp)).left) a) =
      schemeGerm V E hV (Opposite.op T) a at h
  rwa [chartRefinement_germ W V f hf'] at h

/-- A comparison equivalence with the two germ compatibilities of
`AlgebraicGeometry.Space.etaleLocalRingEquivChart` exists. -/
lemma etaleLocalRingEquivChart_nonempty
    (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    Nonempty { e : etaleLocalRing B S hS F x ≃+*
        _root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme V) hV
          (chartGeometricPoint V) //
      (∀ a : Γ(neighborhoodChartScheme V, ⊤),
        e (etaleLocalRingGerm B S hS F x (Opposite.op V) a) =
          structureSheafStalkFromLocalRing E (neighborhoodChartScheme V) hV
            (chartGeometricPoint V)
            ((neighborhoodChartScheme V).presheaf.germ ⊤
              ((chartGeometricPoint V).hom
                (closedPoint (chartGeometricPoint V).residueField)) trivial a)) ∧
      (∀ (W : SmallEtaleNeighborhood x) (f : W ⟶ V)
          (U : (geometricPointFiber E (neighborhoodChartScheme V) hV
            (chartGeometricPoint V)).Elementsᵒᵖ)
          (a : Γ(neighborhoodChartScheme W, ⊤))
          (hs : neighborhoodChartScheme W =
            (_root_.AlgebraicGeometry.SmallEtale.toScheme E
              (neighborhoodChartScheme V) hV).obj U.unop.1)
          (_hp : HEq (chartGeometricPoint W).hom U.unop.2.1)
          (_hf : HEq (neighborhoodChartMap f)
            (E.inclusion.map U.unop.1.obj.hom)),
        e (etaleLocalRingGerm B S hS F x (Opposite.op W) a) =
          (colimit.ι
            ((Functor.Elements.π
              (geometricPointFiber E (neighborhoodChartScheme V) hV
                (chartGeometricPoint V))).op ⋙
              (_root_.AlgebraicGeometry.SmallEtale.structureSheaf E
                (neighborhoodChartScheme V) hV).obj)
            U).hom (show Γ((_root_.AlgebraicGeometry.SmallEtale.toScheme E
              (neighborhoodChartScheme V) hV).obj U.unop.1, ⊤) from hs ▸ a)) } := by
  classical
  refine ⟨⟨(etaleLocalRingEquivOnCommonNeighborhoods hF V E hV).val, fun a ↦ ?_,
    etaleLocalRingEquivOnCommonNeighborhoods_germ hF V E hV⟩⟩
  let U : schemeNeighborhoods V E hV :=
    Functor.elementsMk _ ⟨Over.mk (𝟙 (E.obj (neighborhoodChartScheme V) hV)),
      (show Etale (𝟙 (neighborhoodChartScheme V)) from inferInstance)⟩
      ⟨(chartGeometricPoint V).hom, Category.comp_id _⟩
  rw [etaleLocalRingEquivOnCommonNeighborhoods_germ hF V E hV V (𝟙 V)
    (Opposite.op U) a rfl HEq.rfl HEq.rfl]
  symm
  apply structureSheafStalkFromLocalRing_germ E (neighborhoodChartScheme V) hV
    (chartGeometricPoint V) (Opposite.op U)
  simp [U]
  rfl

/-- The stalk of the structure sheaf of an algebraic space is canonically
the étale local ring of a scheme étale neighborhood. The comparison sends
ordinary chart germs and all common pointed étale-refinement germs to their
scheme-side germs. -/
@[stacks 04KF "identification of the two étale stalks"]
noncomputable def etaleLocalRingEquivChart
    (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V)) :
    { e : etaleLocalRing B S hS F x ≃+*
        _root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme V) hV
          (chartGeometricPoint V) //
      (∀ a : Γ(neighborhoodChartScheme V, ⊤),
        e (etaleLocalRingGerm B S hS F x (Opposite.op V) a) =
          structureSheafStalkFromLocalRing E (neighborhoodChartScheme V) hV
            (chartGeometricPoint V)
            ((neighborhoodChartScheme V).presheaf.germ ⊤
              ((chartGeometricPoint V).hom
                (closedPoint (chartGeometricPoint V).residueField)) trivial a)) ∧
      (∀ (W : SmallEtaleNeighborhood x) (f : W ⟶ V)
          (U : (geometricPointFiber E (neighborhoodChartScheme V) hV
            (chartGeometricPoint V)).Elementsᵒᵖ)
          (a : Γ(neighborhoodChartScheme W, ⊤))
          (hs : neighborhoodChartScheme W =
            (_root_.AlgebraicGeometry.SmallEtale.toScheme E
              (neighborhoodChartScheme V) hV).obj U.unop.1)
          (_hp : HEq (chartGeometricPoint W).hom U.unop.2.1)
          (_hf : HEq (neighborhoodChartMap f)
            (E.inclusion.map U.unop.1.obj.hom)),
        e (etaleLocalRingGerm B S hS F x (Opposite.op W) a) =
          (colimit.ι
            ((Functor.Elements.π
              (geometricPointFiber E (neighborhoodChartScheme V) hV
                (chartGeometricPoint V))).op ⋙
              (_root_.AlgebraicGeometry.SmallEtale.structureSheaf E
                (neighborhoodChartScheme V) hV).obj)
            U).hom (show Γ((_root_.AlgebraicGeometry.SmallEtale.toScheme E
              (neighborhoodChartScheme V) hV).obj U.unop.1, ⊤) from hs ▸ a)) } :=
  Classical.choice (etaleLocalRingEquivChart_nonempty hF V E hV)

/-- The étale local ring of the algebraic space is the strict henselization
of the local ring of a scheme étale neighborhood at the selected point. -/
@[stacks 04KF "strict-henselization identification"]
noncomputable def strictHenselizationEquivEtaleLocalRing
    (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V))
    (T : IsLocalRing.HenselizationTower
      ((neighborhoodChartScheme V).presheaf.stalk
        ((chartGeometricPoint V).hom
          (closedPoint (chartGeometricPoint V).residueField)))
      (separableClosure (ResidueField
        ((neighborhoodChartScheme V).presheaf.stalk
          ((chartGeometricPoint V).hom
            (closedPoint (chartGeometricPoint V).residueField))))
        (chartGeometricPoint V).residueField)) :
    T.strictHenselization ≃+* etaleLocalRing B S hS F x :=
  (etaleLocalRing_strictHenselization_canonical E
    (neighborhoodChartScheme V) hV (chartGeometricPoint V) T).val.trans
    (etaleLocalRingEquivChart hF V E hV).val.symm

/-- The strict-henselization comparison sends the ordinary germ of a chart
section to its germ in the algebraic-space structure sheaf. -/
@[stacks 04KF "compatibility with chart germs"]
theorem strictHenselizationEquivEtaleLocalRing_germ
    (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtaleNeighborhood x)
    (E : BigEtaleSite.{u}) (hV : E.Contains (neighborhoodChartScheme V))
    (T : IsLocalRing.HenselizationTower
      ((neighborhoodChartScheme V).presheaf.stalk
        ((chartGeometricPoint V).hom
          (closedPoint (chartGeometricPoint V).residueField)))
      (separableClosure (ResidueField
        ((neighborhoodChartScheme V).presheaf.stalk
          ((chartGeometricPoint V).hom
            (closedPoint (chartGeometricPoint V).residueField))))
        (chartGeometricPoint V).residueField))
    (a : Γ(neighborhoodChartScheme V, ⊤)) :
    (strictHenselizationEquivEtaleLocalRing hF V E hV T)
      (algebraMap _ T.strictHenselization
        ((neighborhoodChartScheme V).presheaf.germ ⊤
          ((chartGeometricPoint V).hom
            (closedPoint (chartGeometricPoint V).residueField)) trivial a)) =
      etaleLocalRingGerm B S hS F x (Opposite.op V) a := by
  let e := etaleLocalRingEquivChart hF V E hV
  let c := etaleLocalRing_strictHenselization_canonical E
    (neighborhoodChartScheme V) hV (chartGeometricPoint V) T
  change (c.val.trans e.val.symm)
    (algebraMap _ T.strictHenselization
      ((neighborhoodChartScheme V).presheaf.germ ⊤
        ((chartGeometricPoint V).hom
          (closedPoint (chartGeometricPoint V).residueField)) trivial a)) = _
  rw [RingEquiv.trans_apply, c.property.1]
  exact e.val.symm_apply_eq.mpr (e.property.1 a).symm

end AlgebraicGeometry.Space

end
