module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Étale-local properties at a point of a morphism of algebraic spaces

For a property of morphisms of scheme germs which is étale local on both source and target,
its value at a point of a morphism of algebraic spaces can be tested on every, or on one,
compatible pair of étale scheme charts. For representable spaces this agrees with the
property of the induced morphism of scheme germs.

## Main definitions

* `AlgebraicGeometry.Space.EtaleChartAtPoint` records a commutative pair of étale charts and
  a point of the source chart over the specified point of the algebraic space.
* `AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint` and
  `AlgebraicGeometry.Space.HoldsOnSomeEtaleChartAtPoint` are the two chart conditions. The
  first is **Stacks 04RE**, the definition of a morphism of algebraic spaces having an
  étale-local property of germs at a point.
* `AlgebraicGeometry.Space.etaleChartAtPointOfId` is the pointed chart on a morphism between
  represented presheaves whose two charts are the identities.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_some` identifies the two chart
  conditions.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_representable` compares them
  with the germ of a map between schemes when both spaces are representable.
* `AlgebraicGeometry.Space.chart_property_iff_of_pointedCharts` is the underlying
  chart-independence statement, which needs no algebraic-space hypothesis: any two pointed
  charts at the same point give the same truth value.
* `AlgebraicGeometry.Space.exists_etaleChartAtPoint` produces a pointed chart at every point
  of the source of a morphism of algebraic spaces; it is Tag 02X1 together with Tag 03H5.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_chartMap` reads the chart
  condition for a morphism at a point off any commuting square of étale charts over it: it
  agrees with the chart condition for the induced morphism of charts at the chart point.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart` tests the every-chart
  condition on a chart supplied as data, so it needs no algebraic-space hypothesis.

## Implementation notes

A point of a presheaf is an equivalence class of field-valued points. The chart data
therefore includes a field-valued representative of a point of its source scheme and a point
of that field spectrum. This records the equality of the chart point with the specified point
of the algebraic space without choosing a residue-field spectrum in the bounded big fppf
site.

Two `FieldValuedPoint` notions appear here: the one for a presheaf on the big fppf site
(`AlgebraicGeometry.Space.FieldValuedPoint`, Tag 03BU) and the one for a scheme
(`AlgebraicGeometry.FieldValuedPoint`, Tag 01J9). Inside the namespace the short name is the
former; the latter is written out in full. `schemeFieldValuedPoint` converts between them,
and `schemePoint_eq_of_class_eq` transports the equality of classes of Tag 03BU to equality
of the underlying scheme points via Tag 01J9.

Chart independence is proved by forming the fibre product of the two source charts and the
fibre product of the two target charts, lifting the common field-valued extension of the two
chart points into the former, and applying the étale-square clause of Tag 04NB twice. The
germ morphisms of that square are built with `AlgebraicGeometry.MorphismOfGerms.ofSchemeHom`
and `AlgebraicGeometry.MorphismOfGerms.ofSchemeHomOfEq`, whose composition and étaleness
lemmas are the ones used here; no germ-from-scheme-morphism API is re-derived locally.

## References

* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04RE](https://stacks.math.columbia.edu/tag/04RE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A commutative pair of étale scheme charts at a specified point of the source algebraic
space. The point of the source scheme is represented by a field-valued point of its Yoneda
presheaf. -/
structure EtaleChartAtPoint (f : F ⟶ G) (x : points B S hS F) where
  /-- The source chart. -/
  U : BigFppfOver B S hS
  /-- The target chart. -/
  V : BigFppfOver B S hS
  /-- The étale morphism presenting the source. -/
  a : yoneda.obj U ⟶ F
  /-- The étale morphism presenting the target. -/
  b : yoneda.obj V ⟶ G
  /-- The induced morphism of charts. -/
  h : U ⟶ V
  /-- The source chart is étale. -/
  a_etale :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a
  /-- The target chart is étale. -/
  b_etale :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b
  /-- The square of charts commutes. -/
  comm : yoneda.map h ≫ b = a ≫ f
  /-- A field-valued representative of the chosen point of the source chart. -/
  representative : FieldValuedPoint B S hS (yoneda.obj U)
  /-- A point of the spectrum of the representing field. -/
  point : Spec (.of representative.carrier)
  /-- The representative lies over the specified point of the algebraic space. -/
  maps_to : pointsMap B S hS (yoneda.obj U) a
    (representative.class B S hS (yoneda.obj U)) = x

/-- The scheme point selected by a pointed étale chart. -/
noncomputable abbrev EtaleChartAtPoint.sourcePoint {f : F ⟶ G} {x : points B S hS F}
    (c : EtaleChartAtPoint B S hS f x) : (BigFppfOver.toScheme B S hS).obj c.U :=
  ((BigFppfOver.toScheme B S hS).map c.representative.value) c.point

/-- **Stacks 04RE.** The property holds in every pair of étale charts at the point. For a
property of morphisms of germs of schemes which is étale local on the source-and-target this
is the definition of a morphism of algebraic spaces *having that property at a point*: by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_some` it is equivalent to the
some-chart condition, which is the equivalence the definition invokes. -/
@[stacks 04RE]
abbrev HoldsOnEveryEtaleChartAtPoint
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (f : F ⟶ G) (x : points B S hS F) : Prop :=
  ∀ c : EtaleChartAtPoint B S hS f x,
    Q (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS))

/-- The property holds in some pair of étale charts at the point. -/
abbrev HoldsOnSomeEtaleChartAtPoint
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (f : F ⟶ G) (x : points B S hS F) : Prop :=
  ∃ c : EtaleChartAtPoint B S hS f x,
    Q (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS))

/-- The scheme-level field-valued point (Tag 01J9) underlying a field-valued point of a
represented presheaf (Tag 03BU). -/
noncomputable def schemeFieldValuedPoint (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    _root_.AlgebraicGeometry.FieldValuedPoint ((BigFppfOver.toScheme B S hS).obj U) where
  carrier := p.carrier
  map := (BigFppfOver.toScheme B S hS).map p.value

/-- Field-valued points of a represented presheaf defining the same point of the presheaf
have the same underlying scheme point. -/
theorem schemePoint_eq_of_class_eq (U : BigFppfOver B S hS)
    (p q : FieldValuedPoint B S hS (yoneda.obj U))
    (h : p.class B S hS (yoneda.obj U) = q.class B S hS (yoneda.obj U)) :
    schemePoint B S hS U p = schemePoint B S hS U q := by
  obtain ⟨r, hrp, hrq⟩ := (FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj U) p q).mp h
  have hdom {v : FieldValuedPoint B S hS (yoneda.obj U)}
      (hv : FieldValuedPoint.Dominates B S hS (yoneda.obj U) r v) :
      _root_.AlgebraicGeometry.FieldValuedPoint.Dominates
        (schemeFieldValuedPoint B S hS U r) (schemeFieldValuedPoint B S hS U v) := by
    obtain ⟨f, hf⟩ := hv
    refine ⟨(BigFppfOver.toScheme B S hS).map f, ?_⟩
    change (BigFppfOver.toScheme B S hS).map f ≫
      (BigFppfOver.toScheme B S hS).map v.value =
      (BigFppfOver.toScheme B S hS).map r.value
    have hf' : f ≫ v.value = r.value := by
      change (yoneda.obj U).map f.op v.value = r.value at hf
      simp only [yoneda_obj_map, Quiver.Hom.unop_op] at hf
      change f ≫ v.value = r.value at hf
      exact hf
    rw [← Functor.map_comp, hf']
  exact (_root_.AlgebraicGeometry.FieldValuedPoint.hasCommonExtension_iff_point_eq
    (schemeFieldValuedPoint B S hS U p) (schemeFieldValuedPoint B S hS U q)).mp
      ⟨schemeFieldValuedPoint B S hS U r, hdom hrp, hdom hrq⟩

/-- A morphism of algebraic spaces admits a pointed pair of étale charts at every point of
its source. -/
theorem exists_etaleChartAtPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (x : points B S hS F) :
    Nonempty (EtaleChartAtPoint B S hS f x) := by
  obtain ⟨V, b, hbSurjective, hbEtale⟩ := hG.exists_atlas
  obtain ⟨U, a, α, hcomm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurjective hbEtale
  obtain ⟨y, hy⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).mp
    haSurjective x
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  exact ⟨{ U := U
           V := V
           a := a
           b := b
           h := α
           a_etale := haEtale
           b_etale := hbEtale
           comm := hcomm.symm
           representative := p
           point := IsLocalRing.closedPoint p.carrier
           maps_to := hy }⟩

/-- Étale squares transport an étale-local property of germs from the top to the bottom. -/
private theorem iff_ofSchemeHom_of_etale_square
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q)
    {U' V' W Z : Scheme.{u}} (u : W ⟶ U') (t : Z ⟶ V') (k : W ⟶ Z) (h : U' ⟶ V')
    (hu : Etale u) (ht : Etale t) (hkt : k ≫ t = u ≫ h) (w : W) :
    Q (MorphismOfGerms.ofSchemeHom h (u w)) ↔ Q (MorphismOfGerms.ofSchemeHom k w) := by
  have hpt : t (k w) = h (u w) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun g => g w) hkt
  refine hQ.iff_of_etale_square (MorphismOfGerms.ofSchemeHom u w)
    (MorphismOfGerms.ofSchemeHomOfEq t (k w) (h (u w)) hpt)
    (MorphismOfGerms.ofSchemeHom k w) (MorphismOfGerms.ofSchemeHom h (u w))
    (MorphismOfGerms.isEtale_ofSchemeHomOfEq _ _ _ _ hu)
    (MorphismOfGerms.isEtale_ofSchemeHomOfEq _ _ _ _ ht) ?_
  rw [MorphismOfGerms.ofSchemeHomOfEq_comp, MorphismOfGerms.ofSchemeHomOfEq_comp]
  congr 1

/-- If a field-valued point of `W` maps to a point dominated by `q` along `u`, the image of its
closed point under `u` is the scheme point of `q`. -/
private theorem map_closedPoint_eq_of_comp_eq (U W : BigFppfOver B S hS) (u : W ⟶ U)
    (pw : FieldValuedPoint B S hS (yoneda.obj W)) (q : FieldValuedPoint B S hS (yoneda.obj U))
    (t : Spec (.of q.carrier)) (e : pw.siteObject B S hS (yoneda.obj W) ⟶ q.siteObject B S hS _)
    (he : e ≫ q.value = pw.value ≫ u) :
    (BigFppfOver.toScheme B S hS).map u
      ((BigFppfOver.toScheme B S hS).map pw.value (IsLocalRing.closedPoint pw.carrier)) =
    (BigFppfOver.toScheme B S hS).map q.value t := by
  have hclass : (FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map u) pw).class
      B S hS (yoneda.obj U) = q.class B S hS (yoneda.obj U) := by
    apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
    exact ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) _, e, he⟩
  rw [Subsingleton.elim t (IsLocalRing.closedPoint q.carrier)]
  exact schemePoint_eq_of_class_eq B S hS U _ q hclass

/-- An étale-local property of germ morphisms takes the same value on any two pointed pairs
of étale charts at the same point. No algebraic-space hypothesis is needed. -/
theorem chart_property_iff_of_pointedCharts
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q)
    (f : F ⟶ G) (x : points B S hS F)
    (c d : EtaleChartAtPoint B S hS f x) :
    Q (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS)) ↔
    Q (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map d.h)
      (d.sourcePoint B S hS)) := by
  let T := BigFppfOver.toScheme B S hS
  have hcEtale := c.a_etale
  have hdEtale := d.a_etale
  have hcBEtale := c.b_etale
  have hdBEtale := d.b_etale
  change yoneda.relativelyRepresentable c.a ∧ _ at hcEtale
  change yoneda.relativelyRepresentable d.a ∧ _ at hdEtale
  change yoneda.relativelyRepresentable c.b ∧ _ at hcBEtale
  change yoneda.relativelyRepresentable d.b ∧ _ at hdBEtale
  let hc := hcEtale.1
  let hdb := hdBEtale.1
  let W := hc.pullback d.a
  let u : W ⟶ c.U := hc.fst' d.a
  let v : W ⟶ d.U := hc.snd d.a
  have hclasses :
      (FieldValuedPoint.map B S hS (yoneda.obj c.U) c.a c.representative).class B S hS F =
        (FieldValuedPoint.map B S hS (yoneda.obj d.U) d.a d.representative).class
          B S hS F := by
    simpa only [pointsMap_class] using c.maps_to.trans d.maps_to.symm
  obtain ⟨r, ⟨e, he⟩, ⟨e', he'⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS F _ _).mp hclasses
  let i : r.siteObject B S hS F ⟶ c.U := e ≫ c.representative.value
  let j : r.siteObject B S hS F ⟶ d.U := e' ≫ d.representative.value
  have hij : yoneda.map i ≫ c.a = yoneda.map j ≫ d.a := by
    apply (yonedaEquiv (X := r.siteObject B S hS F) (F := F)).injective
    calc
      c.a.app (Opposite.op (r.siteObject B S hS F)) i =
          F.map e.op (FieldValuedPoint.map B S hS (yoneda.obj c.U)
            c.a c.representative).value := by
        convert c.a.naturality_apply e.op c.representative.value using 1 <;> rfl
      _ = r.value := he
      _ = F.map e'.op (FieldValuedPoint.map B S hS (yoneda.obj d.U)
            d.a d.representative).value := he'.symm
      _ = d.a.app (Opposite.op (r.siteObject B S hS F)) j := by
        convert (d.a.naturality_apply e'.op d.representative.value).symm using 1 <;> rfl
  let l : r.siteObject B S hS F ⟶ W := hc.lift' i j hij
  let pw : FieldValuedPoint B S hS (yoneda.obj W) :=
    { carrier := r.carrier
      contained := r.contained
      toBase := r.toBase
      value := l }
  let wpt := T.map pw.value (IsLocalRing.closedPoint pw.carrier)
  have huw : T.map u wpt = c.sourcePoint B S hS :=
    map_closedPoint_eq_of_comp_eq B S hS c.U W u pw c.representative c.point e
      (hc.lift'_fst i j hij).symm
  have hvw : T.map v wpt = d.sourcePoint B S hS :=
    map_closedPoint_eq_of_comp_eq B S hS d.U W v pw d.representative d.point e'
      (hc.lift'_snd i j hij).symm
  have hu : Etale (T.map u) := hdEtale.2 c.a (yoneda.map v) u (hc.isPullback' d.a).flip
  have hv : Etale (T.map v) := hcEtale.2 d.a (yoneda.map u) v (hc.isPullback' d.a)
  let Z := hdb.pullback c.b
  let s : Z ⟶ d.V := hdb.fst' c.b
  let t : Z ⟶ c.V := hdb.snd c.b
  have hvTarget : Etale (T.map s) := hcBEtale.2 d.b (yoneda.map t) s (hdb.isPullback' c.b).flip
  have htTarget : Etale (T.map t) := hdBEtale.2 c.b (yoneda.map s) t (hdb.isPullback' c.b)
  have hw : yoneda.map u ≫ c.a = yoneda.map v ≫ d.a := by
    have hw' := hc.w d.a
    rw [← hc.map_fst' d.a] at hw'
    simpa [u, v, hc] using hw'
  have hcompat : yoneda.map (v ≫ d.h) ≫ d.b = yoneda.map (u ≫ c.h) ≫ c.b := by
    simp only [Functor.map_comp, Category.assoc]
    calc
      yoneda.map v ≫ yoneda.map d.h ≫ d.b = yoneda.map v ≫ d.a ≫ f := by rw [d.comm]
      _ = yoneda.map u ≫ c.a ≫ f := congrArg (fun q => q ≫ f) hw.symm
      _ = yoneda.map u ≫ yoneda.map c.h ≫ c.b := by rw [c.comm]
  let k : W ⟶ Z := hdb.lift' (v ≫ d.h) (u ≫ c.h) hcompat
  have hks : k ≫ s = v ≫ d.h := hdb.lift'_fst _ _ _
  have hkt : k ≫ t = u ≫ c.h := hdb.lift'_snd _ _ _
  rw [← huw, ← hvw]
  have hkt' := congrArg T.map hkt
  have hks' := congrArg T.map hks
  simp only [Functor.map_comp] at hkt' hks'
  exact (iff_ofSchemeHom_of_etale_square Q hQ _ _ (T.map k) (T.map c.h) hu htTarget hkt' wpt).trans
    (iff_ofSchemeHom_of_etale_square Q hQ _ _ (T.map k) (T.map d.h) hv hvTarget hks' wpt).symm

/-- **Stacks 04NC, equivalence of conditions (1) and (2).** An étale-local property of germ
morphisms holds in every pointed chart if and only if it holds in one pointed chart. -/
@[stacks 04NC "equivalence of conditions (1) and (2)"]
theorem holdsOnEveryEtaleChartAtPoint_iff_some
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (x : points B S hS F) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q f x ↔
      HoldsOnSomeEtaleChartAtPoint B S hS Q f x :=
  ⟨fun hall => (exists_etaleChartAtPoint B S hS hF hG f x).elim fun c => ⟨c, hall c⟩,
    fun ⟨c, hc⟩ d => (chart_property_iff_of_pointedCharts B S hS Q hQ f x c d).mp hc⟩

/-- **Reading an étale-local property at a point off a commuting square of charts.** Let `Q`
be a property of germ morphisms which is étale local on source and target, and let
`α : U ⟶ V` be a morphism of the site fitting into a commuting square of étale charts `a` of
`F` and `b` of `G` over `f : F ⟶ G`. A point `u` of `yoneda.obj U` lying over `x` identifies
the chart condition for `f` at `x` with the chart condition for `yoneda.map α` at `u`.

The square itself is a pointed chart for `f` at `x`, and the same square with identity charts
is a pointed chart for `yoneda.map α` at `u`; both select the same point of the scheme `U`, so
chart independence transports the property in both directions. -/
theorem holdsOnEveryEtaleChartAtPoint_iff_chartMap
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (x : points B S hS F)
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (α : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : a ≫ f = yoneda.map α ≫ b)
    (u : points B S hS (yoneda.obj U)) (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : p.class B S hS (yoneda.obj U) = u)
    (hu : pointsMap B S hS (yoneda.obj U) a u = x) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q f x ↔
      HoldsOnEveryEtaleChartAtPoint B S hS Q (yoneda.map α) u := by
  let cF : EtaleChartAtPoint B S hS f x :=
    { U := U
      V := V
      a := a
      b := b
      h := α
      a_etale := ha
      b_etale := hb
      comm := hcomm.symm
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := by simpa [hp] using hu }
  let cα : EtaleChartAtPoint B S hS (yoneda.map α) u :=
    { U := U
      V := V
      a := 𝟙 (yoneda.obj U)
      b := 𝟙 (yoneda.obj V)
      h := α
      a_etale := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj U))
      b_etale := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj V))
      comm := by simp
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := by rwa [pointsMap_id] }
  exact ⟨fun h => (holdsOnEveryEtaleChartAtPoint_iff_some B S hS Q hQ
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) (yoneda.map α) u).mpr
        ⟨cα, h cF⟩,
    fun h => (holdsOnEveryEtaleChartAtPoint_iff_some B S hS Q hQ hF hG f x).mpr ⟨cF, h cα⟩⟩

/-- An étale-local property of germ morphisms holds in every pointed chart exactly when it
holds in one given pointed chart. Unlike `holdsOnEveryEtaleChartAtPoint_iff_some`, which
produces a chart and therefore needs the two presheaves to be algebraic spaces, this
version takes the chart as data and needs no such hypothesis. -/
theorem holdsOnEveryEtaleChartAtPoint_iff_of_chart
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q)
    (f : F ⟶ G) (x : points B S hS F) (c : EtaleChartAtPoint B S hS f x) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q f x ↔
      Q (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
        (c.sourcePoint B S hS)) :=
  ⟨fun h => h c, fun hc d => (chart_property_iff_of_pointedCharts B S hS Q hQ f x c d).mp hc⟩

/-- The pointed étale chart on a morphism between represented presheaves whose two charts are
the identities. Its source point is the one determined by the given field-valued point. -/
def etaleChartAtPointOfId (U V : BigFppfOver B S hS) (h : U ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) (t : Spec (.of p.carrier)) :
    EtaleChartAtPoint B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) where
  U := U
  V := V
  a := 𝟙 _
  b := 𝟙 _
  h := h
  a_etale := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj U))
  b_etale := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj V))
  comm := by simp
  representative := p
  point := t
  maps_to := by
    change (FieldValuedPoint.map B S hS (yoneda.obj U) (𝟙 (yoneda.obj U)) p).class
      B S hS (yoneda.obj U) = p.class B S hS (yoneda.obj U)
    cases p
    rfl

/-- **Stacks 04NC, representable source and target.** For representable algebraic spaces the
chart condition is the property of the induced morphism of scheme germs at the corresponding
scheme point. -/
@[stacks 04NC "representable source and target"]
theorem holdsOnEveryEtaleChartAtPoint_iff_representable
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q)
    [F.IsRepresentable] [G.IsRepresentable] (f : F ⟶ G) (x : points B S hS F)
    (p : FieldValuedPoint B S hS (yoneda.obj F.reprX)) (t : Spec (.of p.carrier))
    (hx : pointsMap B S hS (yoneda.obj F.reprX) F.reprW.hom
      (p.class B S hS (yoneda.obj F.reprX)) = x) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q f x ↔
      Q (MorphismOfGerms.ofSchemeHom
        ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (F.reprW.hom ≫ f ≫ G.reprW.inv)))
        (((BigFppfOver.toScheme B S hS).map p.value) t)) := by
  let T := BigFppfOver.toScheme B S hS
  let f₀ := yoneda.preimage (F.reprW.hom ≫ f ≫ G.reprW.inv)
  have hcomm : yoneda.map f₀ ≫ G.reprW.hom = F.reprW.hom ≫ f := by
    dsimp [f₀]
    simp [Category.assoc]
  let c : EtaleChartAtPoint B S hS f x :=
    { U := F.reprX
      V := G.reprX
      a := F.reprW.hom
      b := G.reprW.hom
      h := f₀
      a_etale := presheaf_etale_of_iso B S hS F.reprW
      b_etale := presheaf_etale_of_iso B S hS G.reprW
      comm := hcomm
      representative := p
      point := t
      maps_to := hx }
  change HoldsOnEveryEtaleChartAtPoint B S hS Q f x ↔
    Q (MorphismOfGerms.ofSchemeHom (T.map f₀) (T.map p.value t))
  constructor
  · intro hall
    simpa [EtaleChartAtPoint.sourcePoint, c, f₀, T] using hall c
  · intro hcanonical d
    simpa [T] using (chart_property_iff_of_pointedCharts B S hS Q hQ f x d c).mpr
      (by simpa [EtaleChartAtPoint.sourcePoint, c, f₀, T] using hcanonical)

end AlgebraicGeometry.Space

end
