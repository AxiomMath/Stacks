module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint

/-!
# Étale-local properties of germs at a point of an algebraic space

Let `P` be an étale-local property of germs of schemes (Tag 04N1) and let `x` be a point of
an algebraic space `X` over `S`. Testing `P` on the germ of an étale scheme chart at a point
above `x` gives the same answer for every such chart, so the one-chart and every-chart
conditions agree. When `X` is representable the common value is `P` of the germ of the
representing scheme at the corresponding scheme point.

## Main definitions

* `AlgebraicGeometry.Space.HasPropertyAtPoint`: the property holds at some étale scheme chart
  over the given point, which for an étale-local property is what it means for it to hold at
  that point of the space.

The scheme point of a chart selected by a field-valued point of its represented presheaf is
`AlgebraicGeometry.Space.schemePoint`, already available from Tag 03BX, and the germ tested is
`⟨U, schemePoint B S hS U p⟩`.

## Main results

* `AlgebraicGeometry.Space.forall_etale_chart_iff_exists_etale_chart`: the every-chart and
  one-chart conditions agree, which is the equivalence of conditions (1) and (2).
* `AlgebraicGeometry.Space.forall_etale_chart_iff_of_representable`: for a represented
  algebraic space the every-chart condition is `P` at the point of the representing scheme.
* `AlgebraicGeometry.Space.exists_etale_chart_iff_of_representable`: the same for the
  one-chart condition.

## Implementation notes

A point of the algebraic space is an equivalence class of field-valued points (Tag 03BU), and
a point of a chart `U` is recorded as a field-valued point of `yoneda.obj U`; its image in
`|X|` is computed by `AlgebraicGeometry.Space.pointsMap`. This keeps the field extension
implicit in the equality of point classes, and the scheme point of the chart is the image of
the closed point of the field spectrum, which is exactly
`AlgebraicGeometry.Space.schemePoint`.

Chart independence is `chart_germ_property_iff` below. Given two étale charts `a : h_U ⟶ X`
and `b : h_V ⟶ X` and points of them with the same class in `|X|`, the two field-valued
points become equal in `|X|`, hence have a common field-valued extension by Tag 03BU; that
extension lifts into the fibre product `U ×_X V`, which is étale over both charts because
each of `a` and `b` is étale, and `AlgebraicGeometry.Space.schemePoint_eq_of_dominates`
identifies the two chart points with the image of the lifted point. Étale locality of `P` is
then applied twice, through the private lemma `etale_local_map`, which turns an étale
morphism of charts into an étale morphism of germs with `⊤` as its domain of definition.

The surjectivity of a chart on points, needed to produce one chart at a prescribed point, is
Tag 03H5.

## References

* [Stacks Project, Tag 04N2](https://stacks.math.columbia.edu/tag/04N2)
* [Stacks Project, Tag 04RC](https://stacks.math.columbia.edu/tag/04RC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04RC.** A property `P` of germs of schemes holds at a point `x` of an algebraic
space `F` when it holds at the germ of some étale scheme chart `yoneda.obj U ⟶ F` at some
field-valued point of `U` lying over `x`. For an étale-local property the choice of chart is
immaterial, by `AlgebraicGeometry.Space.forall_etale_chart_iff_exists_etale_chart`; stating
this one-chart condition needs neither that hypothesis nor that `F` is an algebraic space. -/
@[stacks 04RC]
abbrev HasPropertyAtPoint (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (x : points B S hS F)
    (P : GermOfScheme.{u} → Prop) : Prop :=
  ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a ∧
    ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x ∧
      P ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U p⟩

/-- An étale morphism of charts of the big fppf site identifies an étale-local property of
germs at a point of the source with the property at its image. -/
private theorem etale_local_map (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (P : GermOfScheme.{u} → Prop) (hP : GermOfScheme.IsEtaleLocal P)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f)) :
    P ⟨(BigFppfOver.toScheme B S hS).obj V,
        schemePoint B S hS V
          (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map f) p)⟩ ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U p⟩ := by
  let X : GermOfScheme := ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U p⟩
  let Y : GermOfScheme :=
    ⟨(BigFppfOver.toScheme B S hS).obj V,
      schemePoint B S hS V (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map f) p)⟩
  let r : MorphismOfGerms.Representative X Y :=
    { source := ⊤
      mem_source := by simp
      hom := X.scheme.topIso.hom ≫ (BigFppfOver.toScheme B S hS).map f
      map_point := by rfl }
  have hcomp : Etale (X.scheme.topIso.hom ≫ (BigFppfOver.toScheme B S hS).map f) := by
    have : Etale ((BigFppfOver.toScheme B S hS).map f) := hf
    have : IsIso X.scheme.topIso.hom := X.scheme.topIso.isIso_hom
    have : Etale X.scheme.topIso.hom := inferInstance
    exact Etale.etale_comp _ (f := X.scheme.topIso.hom)
  have hr : Etale r.hom := by simpa [r] using hcomp
  exact hP (MorphismOfGerms.mk r) ⟨r, rfl, hr⟩

/-- An étale-local property of germs takes the same value on any two étale scheme charts at
the same point of an algebraic space. -/
theorem chart_germ_property_iff (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ F)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (q : FieldValuedPoint B S hS (yoneda.obj V))
    (hx : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) =
      pointsMap B S hS (yoneda.obj V) b (q.class B S hS (yoneda.obj V)))
    (P : GermOfScheme.{u} → Prop) (hP : GermOfScheme.IsEtaleLocal P) :
    P ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U p⟩ ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj V, schemePoint B S hS V q⟩ := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let hArep : yoneda.relativelyRepresentable a :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := F)).mp
      hF.diagonal_representable a
  rw [pointsMap_class, pointsMap_class] at hx
  obtain ⟨s, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS F
      (FieldValuedPoint.map B S hS (yoneda.obj U) a p)
      (FieldValuedPoint.map B S hS (yoneda.obj V) b q)).mp hx
  change F.map i.op (a.app (Opposite.op (p.siteObject B S hS (yoneda.obj U))) p.value) =
    s.value at hi
  change F.map j.op (b.app (Opposite.op (q.siteObject B S hS (yoneda.obj V))) q.value) =
    s.value at hj
  let p' : FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := s.carrier
      field := s.field
      contained := s.contained
      toBase := s.toBase
      value := (yoneda.obj U).map i.op p.value }
  let q' : FieldValuedPoint B S hS (yoneda.obj V) :=
    { carrier := s.carrier
      field := s.field
      contained := s.contained
      toBase := s.toBase
      value := (yoneda.obj V).map j.op q.value }
  have hcompat : yoneda.map p'.value ≫ a = yoneda.map q'.value ≫ b := by
    apply (yonedaEquiv (X := s.siteObject B S hS F) (F := F)).injective
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using
      ((a.naturality_apply i.op p.value).trans hi).trans
        ((b.naturality_apply j.op q.value).trans hj).symm
  let W := hArep.pullback b
  let mV : W ⟶ V := hArep.snd b
  let mU : W ⟶ U := yoneda.preimage (hArep.fst b)
  have hmU : yoneda.map mU = hArep.fst b := yoneda.map_preimage _
  have hpb := hArep.isPullback b
  let t : s.siteObject B S hS F ⟶ W := hArep.lift (yoneda.map p'.value) q'.value hcompat
  have htsnd : t ≫ mV = q'.value := hArep.lift_snd (yoneda.map p'.value) q'.value hcompat
  have htmU : t ≫ mU = p'.value := Yoneda.fullyFaithful.map_injective <| by
    rw [Functor.map_comp, hmU]
    exact hArep.lift_fst (yoneda.map p'.value) q'.value hcompat
  let w : FieldValuedPoint B S hS (yoneda.obj W) :=
    { carrier := s.carrier
      field := s.field
      contained := s.contained
      toBase := s.toBase
      value := t }
  let wU := FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map mU) w
  let wV := FieldValuedPoint.map B S hS (yoneda.obj W) (yoneda.map mV) w
  have hdomU : FieldValuedPoint.Dominates B S hS (yoneda.obj U) wU p := by
    refine ⟨i, ?_⟩
    show p'.value = (yoneda.map mU).app _ t
    simpa [p', w, wU, FieldValuedPoint.map, FieldValuedPoint.siteObject] using htmU.symm
  have hdomV : FieldValuedPoint.Dominates B S hS (yoneda.obj V) wV q := by
    refine ⟨j, ?_⟩
    show q'.value = (yoneda.map mV).app _ t
    simpa [q', w, wV, mV, FieldValuedPoint.map, FieldValuedPoint.siteObject] using htsnd.symm
  have hEtU : Etale (T.map mU) :=
    hb.property a (yoneda.map mV) mU (by simpa [mV, hmU] using hpb.flip)
  have hEtV : Etale (T.map mV) :=
    ha.property b (yoneda.map mU) mV (by simpa [mV, hmU] using hpb)
  rw [← schemePoint_eq_of_dominates B S hS U hdomU,
    ← schemePoint_eq_of_dominates B S hS V hdomV]
  exact (etale_local_map B S hS mU w P hP hEtU).trans
    (etale_local_map B S hS mV w P hP hEtV).symm

/-- **Stacks 04N2, conditions (1) and (2).** An étale-local property of germs of schemes
holds at every étale scheme chart over a point of an algebraic space exactly when it holds at
some such chart. -/
@[stacks 04N2 "equivalence of chart conditions"]
theorem forall_etale_chart_iff_exists_etale_chart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (P : GermOfScheme.{u} → Prop) (hP : GermOfScheme.IsEtaleLocal P) :
    (∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a →
      ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x →
        P ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U p⟩) ↔
    (∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x ∧
        P ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U p⟩) := by
  constructor
  · intro hall
    obtain ⟨U, a, hsurj, hetale⟩ := hF.exists_atlas
    obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).mp hsurj x
    obtain ⟨p, rfl⟩ := Quot.exists_rep z
    exact ⟨U, a, hetale, p, hz, hall U a hetale p hz⟩
  · rintro ⟨U, a, ha, p, hxp, hPp⟩ V b hb q hxq
    exact (chart_germ_property_iff B S hS hF a b ha hb p q (hxp.trans hxq.symm) P hP).mp hPp

/-- A presheaf isomorphic to a represented one is an algebraic space. -/
private theorem isAlgebraicSpace_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (X : BigFppfOver B S hS)
    (e : yoneda.obj X ≅ F) : IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_relativelyRepresentable B S hS e.inv
    (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS X)

/-- **Stacks 04N2, the representable case.** For a represented algebraic space the
every-chart condition is the property of the germ of its representing scheme at the
corresponding scheme point. -/
@[stacks 04N2 "representable case"]
theorem forall_etale_chart_iff_of_representable (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (X : BigFppfOver B S hS)
    (e : yoneda.obj X ≅ F) (p : FieldValuedPoint B S hS (yoneda.obj X))
    (P : GermOfScheme.{u} → Prop) (hP : GermOfScheme.IsEtaleLocal P) :
    (∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a →
      ∀ q : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U)) =
          pointsMap B S hS (yoneda.obj X) e.hom (p.class B S hS (yoneda.obj X)) →
        P ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U q⟩) ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj X, schemePoint B S hS X p⟩ := by
  have hmain := forall_etale_chart_iff_exists_etale_chart B S hS F
    (isAlgebraicSpace_of_iso B S hS X e)
    (pointsMap B S hS (yoneda.obj X) e.hom (p.class B S hS (yoneda.obj X))) P hP
  rw [hmain]
  exact ⟨fun h => hmain.mpr h X e.hom (presheaf_etale_of_iso B S hS e) p rfl,
    fun hXp => ⟨X, e.hom, presheaf_etale_of_iso B S hS e, p, rfl, hXp⟩⟩

/-- **Stacks 04N2, the representable case.** For a represented algebraic space the one-chart
condition is the property of the germ of its representing scheme at the corresponding scheme
point. -/
@[stacks 04N2 "representable case, existential condition"]
theorem exists_etale_chart_iff_of_representable (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (X : BigFppfOver B S hS)
    (e : yoneda.obj X ≅ F) (p : FieldValuedPoint B S hS (yoneda.obj X))
    (P : GermOfScheme.{u} → Prop) (hP : GermOfScheme.IsEtaleLocal P) :
    (∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      ∃ q : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U)) =
          pointsMap B S hS (yoneda.obj X) e.hom (p.class B S hS (yoneda.obj X)) ∧
        P ⟨(BigFppfOver.toScheme B S hS).obj U, schemePoint B S hS U q⟩) ↔
      P ⟨(BigFppfOver.toScheme B S hS).obj X, schemePoint B S hS X p⟩ :=
  (forall_etale_chart_iff_exists_etale_chart B S hS F
    (isAlgebraicSpace_of_iso B S hS X e)
    (pointsMap B S hS (yoneda.obj X) e.hom (p.class B S hS (yoneda.obj X))) P hP).symm.trans
    (forall_etale_chart_iff_of_representable B S hS F X e p P hP)

end AlgebraicGeometry.Space

end
