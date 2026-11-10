module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism.SchematicLocus

/-!
# Birational morphisms of algebraic spaces: factoring charts through the schematic locus

Every schematic open chart at a generic point factors through the schematic locus by an open
immersion, and the factorization carries the chart's point to the chosen representative.
From this, any two charts at compatible points of a morphism admit compatible generic charts,
and any two charts admit a common refinement.

See `StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private theorem etalePresheaf_of_openImmersion_local
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : IsOpenImmersion B S hS f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  let QO := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let QE := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hmono : QO ≤ QE := by
    intro A C g hg
    change AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map g) at hg
    let : AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map g) := hg
    change Etale ((BigFppfOver.toScheme B S hS).map g)
    infer_instance
  change QO.presheaf f at hf
  exact MorphismProperty.relative_monotone hmono _ hf

private theorem isRepresentable_of_openImmersion_to_yoneda_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : F ⟶ yoneda.obj U)
    (hi : IsOpenImmersion B S hS i) : F.IsRepresentable := by
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have ht : (MorphismProperty.presheaf Q) i := hi
  let W := ht.rep.pullback (𝟙 (yoneda.obj U))
  have hWiso : IsIso (ht.rep.fst (𝟙 (yoneda.obj U))) :=
    (ht.rep.isPullback (𝟙 (yoneda.obj U))).isIso_fst_of_isIso
  let e : yoneda.obj W ≅ F := asIso (ht.rep.fst (𝟙 (yoneda.obj U)))
  exact isRepresentable_of_natIso (yoneda.obj W) e

private theorem openImmersion_comp_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : IsOpenImmersion B S hS f)
    (hg : IsOpenImmersion B S hS g) :
    IsOpenImmersion B S hS (f ≫ g) := by
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) := by
    infer_instance
  let : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage
      (BigFppfOver.toScheme B S hS)
  let : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  exact MorphismProperty.comp_mem P.presheaf f g hf hg

private theorem openImmersion_of_iso_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    IsOpenImmersion B S hS e.hom := by
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let Q := P.presheaf
  let : Q.ContainsIdentities := inferInstance
  let : Q.RespectsIso := inferInstance
  exact MorphismProperty.isomorphisms_le_of_containsIdentities Q e.hom (by infer_instance)

private lemma pointsRange_preimage_iff_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (V : Subfunctor G) (x : points B S hS F) :
    x ∈ Set.range (pointsMap B S hS (V.preimage f).toFunctor
      (V.preimage f).ι) ↔
    pointsMap B S hS F f x ∈
      Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  induction x using Quot.ind with
  | _ p =>
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨qrep, rfl⟩ := Quot.exists_rep q
      have hc := (FieldValuedPoint.class_eq_class_iff
        B S hS F (FieldValuedPoint.map B S hS
          (V.preimage f).toFunctor (V.preimage f).ι qrep) p).mp (by
            simpa only [pointsMap_class] using hq)
      refine ⟨pointsMap B S hS (V.preimage f).toFunctor
        (V.fromPreimage f) (qrep.class B S hS (V.preimage f).toFunctor), ?_⟩
      have hcomp : (V.preimage f).ι ≫ f = V.fromPreimage f ≫ V.ι :=
        (Subfunctor.fromPreimage_ι V f).symm
      calc
        pointsMap B S hS V.toFunctor V.ι
            (pointsMap B S hS (V.preimage f).toFunctor
              (V.fromPreimage f) qrep.class) =
            pointsMap B S hS (V.preimage f).toFunctor
              (V.fromPreimage f ≫ V.ι) qrep.class := by
                rw [pointsMap_comp]
                rfl
        _ = pointsMap B S hS (V.preimage f).toFunctor
              ((V.preimage f).ι ≫ f) qrep.class := by rw [hcomp]
        _ = pointsMap B S hS F f
              (pointsMap B S hS (V.preimage f).toFunctor
                (V.preimage f).ι qrep.class) := by
                rw [pointsMap_comp]
                rfl
        _ = pointsMap B S hS F f p.class :=
          congrArg (pointsMap B S hS F f) hq
    · rintro ⟨q, hq⟩
      obtain ⟨qrep, rfl⟩ := Quot.exists_rep q
      have heq : (FieldValuedPoint.map B S hS F f p).class B S hS G =
          (FieldValuedPoint.map B S hS V.toFunctor V.ι qrep).class
            B S hS G := by
        simpa only [pointsMap_class] using hq.symm
      obtain ⟨r, ⟨t, htp⟩, ⟨s, hsq⟩⟩ :=
        (FieldValuedPoint.class_eq_class_iff
          B S hS G (FieldValuedPoint.map B S hS F f p)
          (FieldValuedPoint.map B S hS V.toFunctor V.ι qrep)).mp heq
      let yr : FieldValuedPoint B S hS F := {
        carrier := r.carrier
        field := r.field
        contained := r.contained
        toBase := r.toBase
        value := F.map t.op p.value }
      have hobjr : yr.siteObject B S hS F = r.siteObject B S hS G := rfl
      have hobjp : p.siteObject B S hS F =
          (FieldValuedPoint.map B S hS F f p).siteObject B S hS G := rfl
      have hfval : f.app (Opposite.op (yr.siteObject B S hS F)) yr.value = r.value := by
        cases hobjr
        cases hobjp
        exact (NatTrans.naturality_apply f t.op p.value).trans htp
      have hyV : f.app (Opposite.op (yr.siteObject B S hS F)) yr.value ∈
          V.obj (Opposite.op (yr.siteObject B S hS F)) := by
        rw [hfval]
        change r.value ∈ V.obj (Opposite.op r.siteObject)
        rw [← hsq]
        exact V.map s.op qrep.value.property
      let lift : FieldValuedPoint B S hS (V.preimage f).toFunctor := {
        carrier := r.carrier
        field := r.field
        contained := r.contained
        toBase := r.toBase
        value := ⟨yr.value, hyV⟩ }
      have hclass : (FieldValuedPoint.map B S hS
          (V.preimage f).toFunctor (V.preimage f).ι lift).class B S hS F =
          p.class B S hS F := by
        apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
        refine ⟨yr, ?_, ?_⟩
        · refine ⟨𝟙 yr.siteObject, ?_⟩
          change F.map (𝟙 yr.siteObject).op lift.value.1 = yr.value
          simp [lift, yr]
        · exact ⟨t, rfl⟩
      refine ⟨lift.class B S hS (V.preimage f).toFunctor, ?_⟩
      simpa only [pointsMap_class] using hclass

noncomputable def chartFactorNatTrans
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (c : GenericChart B S hS x) :
    yoneda.obj c.U ⟶ yoneda.obj (schematicScheme B S hS hF) := by
  let R := Subfunctor.range c.immersion
  have hRopen := isOpenSubspace_range_of_isAlgebraicSpace
    B S hS (isAlgebraicSpace_yoneda B S hS c.U) c.immersion c.isOpen
  letI : Mono c.immersion :=
    AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS c.immersion c.isOpen
  letI : IsIso (Subfunctor.toRange c.immersion) := by infer_instance
  have hRrep : R.toFunctor.IsRepresentable :=
    isRepresentable_of_natIso _ (asIso (Subfunctor.toRange c.immersion))
  let Z := schematicLocus B S hS F
  have hZrep : Z.toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2
  letI : Z.toFunctor.IsRepresentable := hZrep
  let j : R.toFunctor ⟶ Z.toFunctor :=
    Subfunctor.homOfLe (le_schematicLocus B S hS F R hRopen hRrep)
  let α : yoneda.obj c.U ⟶ yoneda.obj (schematicScheme B S hS hF) :=
    Subfunctor.toRange c.immersion ≫ j ≫ Z.toFunctor.reprW.inv
  exact α

noncomputable def chartFactorHom
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (c : GenericChart B S hS x) :
    c.U ⟶ schematicScheme B S hS hF :=
  yoneda.preimage (chartFactorNatTrans B S hS hF c)

private theorem yoneda_map_chartFactorHom
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (c : GenericChart B S hS x) :
    yoneda.map (chartFactorHom B S hS hF c) =
      chartFactorNatTrans B S hS hF c :=
  yoneda.map_preimage _

theorem chartFactorHom_fac
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (c : GenericChart B S hS x) :
    yoneda.map (chartFactorHom B S hS hF c) ≫ schematicChart B S hS hF =
      c.immersion := by
  rw [yoneda_map_chartFactorHom]
  simp [chartFactorNatTrans, schematicChart, schematicScheme, Category.assoc]

private theorem isStableUnderBaseChange_openImmersion_local :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  constructor
  intro A C C' D f g f' g' hpb hg
  change AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g')
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.IsOpenImmersion.{u})
    (hpb.map (BigFppfOver.toScheme B S hS)) hg

private theorem chartFactorHom_isOpenImmersion
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (c : GenericChart B S hS x) :
    IsOpenImmersion B S hS
      (yoneda.map (chartFactorHom B S hS hF c)) := by
  let P := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let Q := P.presheaf
  let : P.IsStableUnderBaseChange := isStableUnderBaseChange_openImmersion_local B S hS
  let : Q.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange P
  have hQdiag : Q ≤ Q.diagonal := by
    intro A C f hf
    have : Mono f := by
      change IsOpenImmersion B S hS f at hf
      exact AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS f hf
    change Q (pullback.diagonal f)
    exact Q.of_isIso _
  let : MorphismProperty.HasOfPostcompProperty Q Q :=
    (MorphismProperty.hasOfPostcompProperty_iff_le_diagonal).2 hQdiag
  have hcomp : Q
      (yoneda.map (chartFactorHom B S hS hF c) ≫ schematicChart B S hS hF) := by
    rw [chartFactorHom_fac]
    exact c.isOpen
  exact MorphismProperty.of_postcomp (W := Q) (W' := Q)
    (yoneda.map (chartFactorHom B S hS hF c)) (schematicChart B S hS hF)
    (isOpenImmersion_schematicChart B S hS hF) hcomp

private theorem schemePoint_eq_of_dominates_local
    (T : BigFppfOver B S hS)
    {p q : FieldValuedPoint B S hS (yoneda.obj T)}
    (h : FieldValuedPoint.Dominates B S hS (yoneda.obj T) p q) :
    schemePoint B S hS T p = schemePoint B S hS T q := by
  obtain ⟨f, hf⟩ := h
  have hNat : yoneda.map f ≫ yonedaEquiv.symm q.value = yonedaEquiv.symm p.value := by
    rw [yonedaEquiv_symm_naturality_left]
    exact congrArg yonedaEquiv.symm hf
  let qmap := (yonedaEquiv.symm q.value).app (Opposite.op q.siteObject) (𝟙 q.siteObject)
  let pmap := (yonedaEquiv.symm p.value).app (Opposite.op p.siteObject) (𝟙 p.siteObject)
  have hqmap : yoneda.map qmap = yonedaEquiv.symm q.value := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map]
    rfl
  have hpmap : yoneda.map pmap = yonedaEquiv.symm p.value := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map]
    rfl
  have hArrow : f ≫ qmap = pmap := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hqmap, hpmap]
    exact hNat
  have hScheme := congrArg (BigFppfOver.toScheme B S hS).map hArrow
  let cp : (BigFppfOver.toScheme B S hS).obj p.siteObject :=
    IsLocalRing.closedPoint p.carrier
  have hAt := congrArg (fun g => g cp) hScheme
  have hclosed : (BigFppfOver.toScheme B S hS).map f cp =
      IsLocalRing.closedPoint q.carrier := by
    let : Field q.carrier := q.field
    let : Subsingleton (B.inclusion.obj (Over.left q.siteObject)) := by
      change Subsingleton (Spec (.of q.carrier))
      infer_instance
    change (B.inclusion.map f.left) (IsLocalRing.closedPoint p.carrier) =
      IsLocalRing.closedPoint q.carrier
    exact Subsingleton.elim _ _
  simp only [Functor.map_comp, Scheme.Hom.comp_apply] at hAt
  rw [hclosed] at hAt
  change (BigFppfOver.toScheme B S hS).map pmap
      (IsLocalRing.closedPoint p.carrier) =
    (BigFppfOver.toScheme B S hS).map qmap
      (IsLocalRing.closedPoint q.carrier)
  exact hAt.symm

private theorem schemePoint_eq_of_commonExtension_local
    (T : BigFppfOver B S hS)
    {p q : FieldValuedPoint B S hS (yoneda.obj T)}
    (h : FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj T) p q) :
    schemePoint B S hS T p = schemePoint B S hS T q := by
  obtain ⟨r, hp, hq⟩ := h
  exact (schemePoint_eq_of_dominates_local B S hS T hp).symm.trans
    (schemePoint_eq_of_dominates_local B S hS T hq)

private theorem schemePoint_eq_of_class_eq_local
    (T : BigFppfOver B S hS)
    {p q : FieldValuedPoint B S hS (yoneda.obj T)}
    (h : p.class B S hS (yoneda.obj T) = q.class B S hS (yoneda.obj T)) :
    schemePoint B S hS T p = schemePoint B S hS T q :=
  schemePoint_eq_of_commonExtension_local B S hS T
    ((FieldValuedPoint.class_eq_class_iff B S hS (yoneda.obj T) p q).mp h)

/-- Pulling a point back along an isomorphism of presheaves, at the level of field-valued
points. -/
private theorem exists_fieldValuedPoint_class_map_eq_local
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e] (q : points B S hS G) :
    ∃ p : FieldValuedPoint B S hS F, pointsMap B S hS F e (p.class B S hS F) = q := by
  obtain ⟨z, hz⟩ := pointsMap_surjective_of_isIso B S hS e q
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  exact ⟨p, hz⟩

/-- Two points are equal if they agree after a monomorphism, given a commuting square. -/
private theorem pointsMap_eq_of_mono_comm_local
    {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (u : A ⟶ C) (m : C ⟶ E) (a : A ⟶ D) (f : D ⟶ E)
    [Mono m] (hcomm : u ≫ m = a ≫ f) (p : points B S hS A) (y : points B S hS C)
    (hy : pointsMap B S hS C m y = pointsMap B S hS D f (pointsMap B S hS A a p)) :
    pointsMap B S hS A u p = y :=
  pointsMap_injective_of_mono B S hS m
    (by rw [← pointsMap_comp_apply, hcomm, pointsMap_comp_apply]; exact hy.symm)

/-- Equality of classes of points on a representable presheaf gives equality of scheme points. -/
private theorem map_schemePoint_eq_local
    {W V : BigFppfOver B S hS} (g : W ⟶ V) (p : FieldValuedPoint B S hS (yoneda.obj W))
    (q : FieldValuedPoint B S hS (yoneda.obj V))
    (h : pointsMap B S hS (yoneda.obj W) (yoneda.map g) (p.class B S hS _) =
      q.class B S hS _) :
    ((BigFppfOver.toScheme B S hS).map g) (schemePoint B S hS W p) = schemePoint B S hS V q := by
  have := schemePoint_eq_of_class_eq_local B S hS V
    (p := FieldValuedPoint.map B S hS _ (yoneda.map g) p) (q := q)
    (by simpa only [pointsMap_class] using h)
  exact this

theorem chartFactorHom_isOpenImmersion_scheme
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} (c : GenericChart B S hS x) :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map
        (chartFactorHom B S hS hF c)) := by
  let P := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let : P.IsStableUnderBaseChange := isStableUnderBaseChange_openImmersion_local B S hS
  apply (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).1
  exact chartFactorHom_isOpenImmersion B S hS hF c

theorem chartFactorHom_point_eq
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    {x : points B S hS F}
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F))
    (c : GenericChart B S hS x) :
    ((BigFppfOver.toScheme B S hS).map
      (chartFactorHom B S hS hF c)) (schemePoint B S hS c.U c.point) =
    schemePoint B S hS (schematicScheme B S hS hF)
      (schematicRepresentative B S hS hF hdense hfinite x hx) := by
  let s := schematicGenericChart B S hS hF hdense hfinite x hx
  have : Mono (schematicChart B S hS hF) :=
    AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS _
      (isOpenImmersion_schematicChart B S hS hF)
  have hpt := map_schemePoint_eq_local B S hS (chartFactorHom B S hS hF c) c.point s.point
    (pointsMap_injective_of_mono B S hS (schematicChart B S hS hF)
      (by rw [← pointsMap_comp_apply, chartFactorHom_fac, c.mapsTo]; exact s.mapsTo.symm))
  simpa [s, schematicGenericChart] using hpt

theorem exists_compatibleGenericCharts_local
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdenseX : HasDenseRepresentableOpenSubspace B S hS X)
    (hdenseY : HasDenseRepresentableOpenSubspace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    (f : X ⟶ Y) (x : points B S hS X)
    (hx : letI := pointTopology B S hS X
      x ∈ genericPoints (points B S hS X))
    (hy : letI := pointTopology B S hS Y
      pointsMap B S hS X f x ∈ genericPoints (points B S hS Y)) :
    ∃ (c : GenericChart B S hS x)
      (d : GenericChart B S hS (pointsMap B S hS X f x))
      (g : c.U ⟶ d.U),
      c.immersion ≫ f = yoneda.map g ≫ d.immersion ∧
      ((BigFppfOver.toScheme B S hS).map g)
        (schemePoint B S hS c.U c.point) =
          schemePoint B S hS d.U d.point := by
  classical
  let U := schematicScheme B S hS hX
  let qX := schematicChart B S hS hX
  let Z := schematicLocus B S hS Y
  have hZopen :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
      B S hS hY).1
  have : Z.toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
      B S hS hY).2
  let V := Z.toFunctor.reprX
  let eY := Z.toFunctor.reprW
  let chartV : yoneda.obj V ⟶ Y := eY.hom ≫ Z.ι
  have hchartVopen : IsOpenImmersion B S hS chartV :=
    openImmersion_comp_local B S hS eY.hom Z.ι
      (openImmersion_of_iso_local B S hS eY) hZopen.2
  let pX := schematicRepresentative B S hS hX hdenseX hfiniteX x hx
  let pY := schematicRepresentative B S hS hY hdenseY hfiniteY
    (pointsMap B S hS X f x) hy
  have hpX : pointsMap B S hS (yoneda.obj U) qX
      (pX.class B S hS _) = x :=
    (exists_schematicRepresentative B S hS hX hdenseX hfiniteX x hx).choose_spec
  have hpY : pointsMap B S hS (yoneda.obj V) (schematicChart B S hS hY)
      (pY.class B S hS _) = pointsMap B S hS X f x :=
    (exists_schematicRepresentative B S hS hY hdenseY hfiniteY
      (pointsMap B S hS X f x) hy).choose_spec
  let fX : yoneda.obj U ⟶ Y := qX ≫ f
  let P : Subfunctor (yoneda.obj U) := Z.preimage fX
  have hPopen : IsOpenSubspace B S hS P :=
    isOpenSubspace_preimage B S hS fX Z hY
      (isAlgebraicSpace_yoneda B S hS U) hZopen
  have : P.toFunctor.IsRepresentable :=
    isRepresentable_of_openImmersion_to_yoneda_local B S hS U P.ι hPopen.2
  let W := P.toFunctor.reprX
  let eP := P.toFunctor.reprW
  let gYoneda : yoneda.obj W ⟶ yoneda.obj V :=
    eP.hom ≫ Z.fromPreimage fX ≫ eY.inv
  let g : W ⟶ V := yoneda.preimage gYoneda
  have hg : yoneda.map g = gYoneda := yoneda.map_preimage gYoneda
  let a : yoneda.obj W ⟶ X := eP.hom ≫ P.ι ≫ qX
  have hpre : P.ι ≫ fX = Z.fromPreimage fX ≫ Z.ι :=
    (Subfunctor.fromPreimage_ι Z fX).symm
  have hcomm : a ≫ f = yoneda.map g ≫ chartV := by
    rw [hg]
    calc
      a ≫ f = eP.hom ≫ P.ι ≫ fX := by simp [a, fX, Category.assoc]
      _ = eP.hom ≫ Z.fromPreimage fX ≫ Z.ι := by
        calc
          (eP.hom ≫ P.ι) ≫ fX = eP.hom ≫ (P.ι ≫ fX) := Category.assoc _ _ _
          _ = eP.hom ≫ (Z.fromPreimage fX ≫ Z.ι) :=
            congrArg (fun k => eP.hom ≫ k) hpre
          _ = eP.hom ≫ Z.fromPreimage fX ≫ Z.ι := rfl
      _ = gYoneda ≫ chartV := by
        simp [gYoneda, chartV, Category.assoc]
  have haOpen : IsOpenImmersion B S hS a := by
    dsimp [a]
    have hfirst : IsOpenImmersion B S hS (eP.hom ≫ P.ι) :=
      openImmersion_comp_local B S hS eP.hom P.ι
        (openImmersion_of_iso_local B S hS eP) hPopen.2
    exact openImmersion_comp_local B S hS (eP.hom ≫ P.ι) qX hfirst
      (isOpenImmersion_schematicChart B S hS hX)
  let qUx := pX.class B S hS (yoneda.obj U)
  have hfx : pointsMap B S hS (yoneda.obj U) fX qUx =
      pointsMap B S hS X f x := by
    calc
      _ = pointsMap B S hS X f
          (pointsMap B S hS (yoneda.obj U) qX qUx) := by
            rw [pointsMap_comp]
            rfl
      _ = _ := congrArg (pointsMap B S hS X f) hpX
  obtain ⟨qV, hqV⟩ : pointsMap B S hS X f x ∈
      Set.range (pointsMap B S hS (yoneda.obj V) (schematicChart B S hS hY)) :=
    ⟨_, hpY⟩
  have hZrange : pointsMap B S hS X f x ∈
      Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
    refine ⟨pointsMap B S hS (yoneda.obj V) eY.hom qV, ?_⟩
    calc
      _ = pointsMap B S hS (yoneda.obj V)
          (eY.hom ≫ Z.ι) qV := by rw [pointsMap_comp]; rfl
      _ = pointsMap B S hS (yoneda.obj V)
          (schematicChart B S hS hY) qV := by
            dsimp [schematicChart, schematicScheme, V, eY]
      _ = _ := hqV
  have hPrange : qUx ∈ Set.range (pointsMap B S hS P.toFunctor P.ι) := by
    apply (pointsRange_preimage_iff_local B S hS fX Z qUx).2
    rw [hfx]
    exact hZrange
  obtain ⟨qP, hqP⟩ := hPrange
  obtain ⟨pW, hPiso⟩ := exists_fieldValuedPoint_class_map_eq_local B S hS eP.hom qP
  have hqWc : pointsMap B S hS (yoneda.obj W) a (pW.class B S hS (yoneda.obj W)) = x := by
    dsimp only [a]
    rw [pointsMap_comp_apply, pointsMap_comp_apply, hPiso, hqP, hpX]
  let c : GenericChart B S hS x := ⟨W, a, haOpen, pW, hqWc⟩
  obtain ⟨pV, hpV⟩ := Quot.exists_rep qV
  have hqVc : pointsMap B S hS (yoneda.obj V) chartV
      (pV.class B S hS (yoneda.obj V)) =
      pointsMap B S hS X f x :=
    (congrArg (pointsMap B S hS (yoneda.obj V) chartV) hpV).trans hqV
  let d : GenericChart B S hS (pointsMap B S hS X f x) :=
    ⟨V, chartV, hchartVopen, pV, hqVc⟩
  have : Mono chartV :=
    AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS chartV hchartVopen
  exact ⟨c, d, g, hcomm, map_schemePoint_eq_local B S hS g pW d.point
    (pointsMap_eq_of_mono_comm_local B S hS _ chartV _ f hcomm.symm _ _
      (d.mapsTo.trans (congrArg _ hqWc.symm)))⟩

theorem exists_commonGenericChartRefinement_local
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (c d : GenericChart B S hS x) :
    ∃ (e : GenericChart B S hS x) (u : e.U ⟶ c.U) (v : e.U ⟶ d.U),
      e.immersion = yoneda.map u ≫ c.immersion ∧
      e.immersion = yoneda.map v ≫ d.immersion ∧
      ((BigFppfOver.toScheme B S hS).map u)
        (schemePoint B S hS e.U e.point) =
          schemePoint B S hS c.U c.point ∧
      ((BigFppfOver.toScheme B S hS).map v)
        (schemePoint B S hS e.U e.point) =
          schemePoint B S hS d.U d.point := by
  classical
  let R : Subfunctor F := Subfunctor.range d.immersion
  have hRopen : IsOpenSubspace B S hS R :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS
      (isAlgebraicSpace_yoneda B S hS d.U) d.immersion d.isOpen
  let P : Subfunctor (yoneda.obj c.U) := R.preimage c.immersion
  have hPopen : IsOpenSubspace B S hS P :=
    isOpenSubspace_preimage B S hS c.immersion R hF
      (isAlgebraicSpace_yoneda B S hS c.U) hRopen
  have : P.toFunctor.IsRepresentable :=
    isRepresentable_of_openImmersion_to_yoneda_local B S hS c.U P.ι hPopen.2
  let : Mono d.immersion :=
    AlgebraicGeometry.Space.mono_of_isOpenImmersion B S hS d.immersion d.isOpen
  let W := P.toFunctor.reprX
  let eP := P.toFunctor.reprW
  let eR := asIso (Subfunctor.toRange d.immersion)
  let uYoneda : yoneda.obj W ⟶ yoneda.obj c.U := eP.hom ≫ P.ι
  let vYoneda : yoneda.obj W ⟶ yoneda.obj d.U :=
    eP.hom ≫ R.fromPreimage c.immersion ≫ eR.inv
  let u : W ⟶ c.U := yoneda.preimage uYoneda
  let v : W ⟶ d.U := yoneda.preimage vYoneda
  have hu : yoneda.map u = uYoneda := yoneda.map_preimage uYoneda
  have hv : yoneda.map v = vYoneda := yoneda.map_preimage vYoneda
  have htoRange : Subfunctor.toRange d.immersion ≫ R.ι = d.immersion :=
    Subfunctor.toRange_ι d.immersion
  have hInv : eR.inv ≫ d.immersion = R.ι := by
    calc
      eR.inv ≫ d.immersion = eR.inv ≫ (eR.hom ≫ R.ι) :=
        congrArg (fun k => eR.inv ≫ k) htoRange.symm
      _ = R.ι := by simp
  let a : yoneda.obj W ⟶ F := yoneda.map u ≫ c.immersion
  have hcomm : yoneda.map v ≫ d.immersion = a := by
    calc
      yoneda.map v ≫ d.immersion = vYoneda ≫ d.immersion :=
        congrArg (fun k => k ≫ d.immersion) hv
      _ = eP.hom ≫ R.fromPreimage c.immersion ≫ eR.inv ≫ d.immersion := rfl
      _ = eP.hom ≫ R.fromPreimage c.immersion ≫ R.ι :=
        congrArg (fun k => eP.hom ≫ R.fromPreimage c.immersion ≫ k) hInv
      _ = eP.hom ≫ P.ι ≫ c.immersion :=
        congrArg (fun k => eP.hom ≫ k) (Subfunctor.fromPreimage_ι R c.immersion)
      _ = uYoneda ≫ c.immersion := rfl
      _ = yoneda.map u ≫ c.immersion := by rw [hu]
      _ = a := rfl
  have haOpen : IsOpenImmersion B S hS a := by
    dsimp [a]
    have huOpen : IsOpenImmersion B S hS (yoneda.map u) := by
      rw [hu]
      exact openImmersion_comp_local B S hS eP.hom P.ι
        (openImmersion_of_iso_local B S hS eP) hPopen.2
    exact openImmersion_comp_local B S hS (yoneda.map u) c.immersion huOpen c.isOpen
  let qC := c.point.class B S hS (yoneda.obj c.U)
  have hRrange : pointsMap B S hS (yoneda.obj c.U) c.immersion qC ∈
      Set.range (pointsMap B S hS R.toFunctor R.ι) := by
    rw [c.mapsTo]
    refine ⟨pointsMap B S hS (yoneda.obj d.U)
      (Subfunctor.toRange d.immersion) (d.point.class B S hS (yoneda.obj d.U)), ?_⟩
    calc
      _ = pointsMap B S hS (yoneda.obj d.U)
          ((Subfunctor.toRange d.immersion) ≫ R.ι)
          (d.point.class B S hS (yoneda.obj d.U)) := by rw [pointsMap_comp]; rfl
      _ = pointsMap B S hS (yoneda.obj d.U) d.immersion
          (d.point.class B S hS (yoneda.obj d.U)) := by rw [Subfunctor.toRange_ι]
      _ = x := d.mapsTo
  have hPrange : qC ∈ Set.range (pointsMap B S hS P.toFunctor P.ι) := by
    exact (pointsRange_preimage_iff_local B S hS c.immersion R qC).2 hRrange
  obtain ⟨qP, hqP⟩ := hPrange
  obtain ⟨pW, hPiso⟩ := exists_fieldValuedPoint_class_map_eq_local B S hS eP.hom qP
  have hqWc : pointsMap B S hS (yoneda.obj W) (yoneda.map u)
      (pW.class B S hS (yoneda.obj W)) = qC := by
    rw [hu]
    dsimp only [uYoneda]
    rw [pointsMap_comp_apply, hPiso, hqP]
  have hqWd : pointsMap B S hS (yoneda.obj W) (yoneda.map v)
      (pW.class B S hS (yoneda.obj W)) = d.point.class B S hS (yoneda.obj d.U) :=
    pointsMap_eq_of_mono_comm_local B S hS _ d.immersion (yoneda.map u) c.immersion hcomm _ _
      (d.mapsTo.trans (by rw [hqWc, c.mapsTo]))
  have hmapsTo : pointsMap B S hS (yoneda.obj W) a
      (pW.class B S hS (yoneda.obj W)) = x := by
    change pointsMap B S hS _ (yoneda.map u ≫ c.immersion) _ = _
    rw [pointsMap_comp_apply, hqWc, c.mapsTo]
  let e : GenericChart B S hS x := ⟨W, a, haOpen, pW, hmapsTo⟩
  refine ⟨e, u, v, ?_, ?_, map_schemePoint_eq_local B S hS u pW c.point hqWc,
    map_schemePoint_eq_local B S hS v pW d.point hqWd⟩
  · rfl
  · dsimp [e, a]
    exact hcomm.symm

end AlgebraicGeometry.Space

end
