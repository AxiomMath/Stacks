module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.EtaleLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# An étale-local property at every point and on every étale chart (Stacks 04RF)

Let `P` be a property of morphisms of schemes which is étale local on the source and target
(Tag 04QZ), and let `Q` be the property it induces on morphisms of germs (Tag 04R6). For a
morphism `f : F ⟶ G` of algebraic spaces over `S`:

* `Q` holds at a point of `F` on every pointed étale chart exactly when some open subspace
  through that point admits a chart on which `P` holds;
* `P` holds on every étale chart of `f` exactly when `Q` holds at every point of `F`.

## Main definitions

* `AlgebraicGeometry.Space.opensSiteObject`: an open subscheme of the scheme underlying
  an object of the big fppf site over `S`, as an object of that site.
* `AlgebraicGeometry.Space.opensSiteObjectInclusion`: the inclusion of such an open
  subobject into the object it was cut out of.

## Main results

* `AlgebraicGeometry.Space.map_opensSiteObjectInclusion` and
  `AlgebraicGeometry.Space.hom_opensSiteObject`: the morphism of schemes underlying the
  inclusion of an open subobject is the inclusion of the open subscheme, and the structure
  morphism of the open subobject over `S` is that inclusion followed by the structure
  morphism of the ambient object. These are the two identifications through which every
  consumer of `opensSiteObject` computes.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_exists_open`: **Stacks 04RF**,
  part (2).
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_forall_atPoint`: **Stacks 04RF**,
  part (3).

## Implementation notes

Both directions are chart constructions in the site. Given a pointed étale chart and an open
subscheme `V` of its source through the chosen point, `V` is again an object of the big fppf
site — this is the `opensSiteObject` / `opensSiteObjectInclusion` block, the size of
an open subscheme being no larger — and its image in `F` is an open subspace by Tag 06NF,
whose points are computed by Tag 03BZ. Conversely, from an open subspace through the point one
restricts a chart to it with Tag 03IE and recognises the restriction as étale.

Part (3) assembles the pointwise statements: by Tag 03MJ it suffices to check `P` on one
surjective étale chart, and the pointed charts of Tag 04NC through the points of that chart
exhaust it. The passage between `P` on a morphism of schemes and `Q` on its germs in both
directions is Tag 04R7.

## References

* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space


/-- An open subscheme `W` of the scheme underlying an object `U` of the big fppf site over
`S`, as an object of that site over `S`: an open subscheme is no larger than its ambient
scheme, so `W` is again below the cutoff of the site, and it is viewed over `S` through the
structure morphism of `U`. -/
noncomputable def opensSiteObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    BigFppfOver B S hS := by
  let T := BigFppfOver.toScheme B S hS
  have hW : B.Contains W.toScheme := by
    change W.toScheme.size < B.cutoff
    exact (Scheme.size_coe_opens_le (T.obj U) W).trans_lt U.left.property
  let Wobj : B.Schemes := B.obj hW
  let wi : B.inclusion.obj Wobj ⟶ B.inclusion.obj U.left := W.ι
  let m : Wobj ⟶ U.left := B.inclusion.preimage (X := Wobj) (Y := U.left) wi
  exact Over.mk (m ≫ U.hom)

/-- The inclusion of `AlgebraicGeometry.Space.opensSiteObject B S hS U W` into `U`, as a
morphism of the big fppf site over `S`: the inclusion of the open subscheme `W`, which is a
morphism over `S` by the very definition of the structure morphism of `opensSiteObject`. -/
noncomputable def opensSiteObjectInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    opensSiteObject B S hS U W ⟶ U := by
  let T := BigFppfOver.toScheme B S hS
  have hW : B.Contains W.toScheme := by
    change W.toScheme.size < B.cutoff
    exact (Scheme.size_coe_opens_le (T.obj U) W).trans_lt U.left.property
  let Wobj : B.Schemes := B.obj hW
  let wi : B.inclusion.obj Wobj ⟶ B.inclusion.obj U.left := W.ι
  let m : Wobj ⟶ U.left := B.inclusion.preimage (X := Wobj) (Y := U.left) wi
  exact Over.homMk m (by simp [opensSiteObject, m, wi])

/-- An open subscheme of the scheme underlying an object of the big fppf site is below the
cutoff of the site. -/
private theorem contains_opens
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) : B.Contains W.toScheme := by
  change W.toScheme.size < B.cutoff
  exact (Scheme.size_coe_opens_le _ W).trans_lt U.left.property

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.opensSiteObjectInclusion`
is the inclusion of the open subscheme it was built from. -/
theorem map_opensSiteObjectInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map
      (opensSiteObjectInclusion B S hS U W) = W.ι := by
  let Wobj : B.Schemes := B.obj (contains_opens B S hS U W)
  let wi : B.inclusion.obj Wobj ⟶ B.inclusion.obj U.left := W.ι
  change B.inclusion.map (B.inclusion.preimage (X := Wobj) (Y := U.left) wi) = wi
  exact B.inclusion.map_preimage wi

/-- The structure morphism of `AlgebraicGeometry.Space.opensSiteObject B S hS U W` over `S`,
read as a morphism of schemes, is the inclusion of the open subscheme `W` followed by
the structure morphism of `U`. The underlying scheme of the open subobject is produced
through
the fullness of the site's inclusion functor, so this identification is not a definitional
one and consumers that need to compute with the structure morphism must go through here. -/
theorem hom_opensSiteObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (opensSiteObject B S hS U W).hom.hom = W.ι ≫ U.hom.hom := by
  rw [← Over.w (opensSiteObjectInclusion B S hS U W)]
  exact congrArg (fun k => k ≫ U.hom.hom) (map_opensSiteObjectInclusion B S hS U W)

/-- A morphism into `AlgebraicGeometry.Space.opensSiteObject B S hS U W`, followed by the
inclusion into `U`, has image inside `W`: on points it is the same morphism read in the
ambient scheme. This is the form in which consumers feed a factorisation through an open
subobject to the set-level criteria about its image. -/
theorem range_map_comp_opensSiteObjectInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T U : BigFppfOver B S hS}
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (g : T ⟶ opensSiteObject B S hS U W) :
    Set.range ((BigFppfOver.toScheme B S hS).map
        (g ≫ opensSiteObjectInclusion B S hS U W)) ⊆
      (W : Set ((BigFppfOver.toScheme B S hS).obj U)) := by
  rw [Functor.map_comp, map_opensSiteObjectInclusion]
  rintro _ ⟨x, rfl⟩
  exact (show W.toScheme from (BigFppfOver.toScheme B S hS).map g x).property

/-- The underlying morphism of `opensSiteObjectInclusion` followed by `h` is the inclusion of
the open subscheme followed by the underlying morphism of `h`. -/
private theorem map_opensSiteObjectInclusion_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS}
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) (h : U ⟶ V) :
    (BigFppfOver.toScheme B S hS).map (opensSiteObjectInclusion B S hS U W ≫ h) =
      W.ι ≫ (BigFppfOver.toScheme B S hS).map h := by
  rw [Functor.map_comp, map_opensSiteObjectInclusion]
  rfl

private theorem etale_opensSiteObjectInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yoneda.map (opensSiteObjectInclusion B S hS U W)) := by
  let T := BigFppfOver.toScheme B S hS
  let QO := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) T
  let : QO.IsStableUnderBaseChange := inverseImage_isStableUnderBaseChange B S hS
    (inferInstance :
      MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
  have hO : QO (opensSiteObjectInclusion B S hS U W) := by
    change AlgebraicGeometry.IsOpenImmersion (T.map (opensSiteObjectInclusion B S hS U W))
    rw [map_opensSiteObjectInclusion]
    exact (inferInstance : AlgebraicGeometry.IsOpenImmersion W.ι)
  have hmon : QO ≤ MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T := by
    intro A C m hm
    change AlgebraicGeometry.IsOpenImmersion (T.map m) at hm
    change AlgebraicGeometry.Etale (T.map m)
    infer_instance
  exact MorphismProperty.relative_monotone hmon _
    ((MorphismProperty.relative_map_iff (F := yoneda) (P := QO)).2 hO)

private theorem etale_restriction_opensSiteObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
        (yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ a) := by
  let Qe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let : Qe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let : Qe.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Qe
  exact MorphismProperty.comp_mem _ _ _ (etale_opensSiteObjectInclusion B S hS U W) ha

private theorem chartOpenImage_rangeOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a) :
    @IsOpen _ (pointTopology B S hS X) (Set.range (pointsMap B S hS
      (yoneda.obj (opensSiteObject B S hS U W))
      (yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ a))) := by
  let V := opensSiteObject B S hS U W
  let p : yoneda.obj V ⟶ X := yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ a
  have hp := etale_restriction_opensSiteObject B S hS U W a ha
  let : TopologicalSpace (points B S hS (yoneda.obj V)) :=
    pointTopology B S hS (yoneda.obj V)
  let : TopologicalSpace (points B S hS X) :=
    pointTopology B S hS X
  have hmap : IsOpenMap (pointsMap B S hS (yoneda.obj V) p) :=
    isOpenMap_pointsMap_of_etale B S hS hX V p hp
  have hopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj V) p)) := by
    rw [← Set.image_univ]
    exact hmap _ isOpen_univ
  exact hopen

private noncomputable def chartOpenImage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a) :
    {Z : Subfunctor X // IsOpenSubspace B S hS Z} := by
  classical
  let : TopologicalSpace (points B S hS X) :=
    pointTopology B S hS X
  let e := openSubspacesOrderIso B S hS X hX
  exact e.symm ⟨Set.range (pointsMap B S hS
    (yoneda.obj (opensSiteObject B S hS U W))
    (yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ a)),
      chartOpenImage_rangeOpen B S hS hX U a W ha⟩

private theorem chartOpenImage_points
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a) :
    Set.range (pointsMap B S hS
      (chartOpenImage B S hS hX U a W ha).1.toFunctor
      (chartOpenImage B S hS hX U a W ha).1.ι) =
      Set.range (pointsMap B S hS
        (yoneda.obj (opensSiteObject B S hS U W))
        (yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ a)) := by
  let : TopologicalSpace (points B S hS X) :=
    pointTopology B S hS X
  let e := openSubspacesOrderIso B S hS X hX
  calc
    Set.range (pointsMap B S hS
        (chartOpenImage B S hS hX U a W ha).1.toFunctor
        (chartOpenImage B S hS hX U a W ha).1.ι) =
        (e (chartOpenImage B S hS hX U a W ha)).1 :=
      (openSubspacesOrderIso_apply B S hS X hX (chartOpenImage B S hS hX U a W ha)).symm
    _ = Set.range (pointsMap B S hS
        (yoneda.obj (opensSiteObject B S hS U W))
        (yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ a)) := by
          dsimp [chartOpenImage]
          exact congrArg (fun O : TopologicalSpace.Opens _ => O.1) (e.apply_symm_apply
            ⟨_, chartOpenImage_rangeOpen B S hS hX U a W ha⟩)

/-- A field-valued point whose closed point lies in `W` factors through the open subobject. -/
private theorem exists_factorization_fieldPointOnOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hw : (BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier) ∈ W) :
    ∃ q : B.obj p.contained ⟶ B.obj (contains_opens B S hS U W),
      q ≫ B.inclusion.preimage (X := B.obj (contains_opens B S hS U W)) (Y := U.left) W.ι =
        p.value.left := by
  let α : Spec (.of p.carrier) ⟶ _ := (BigFppfOver.toScheme B S hS).map p.value
  have hsubset : Set.range α ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w (IsLocalRing.closedPoint p.carrier)]
    exact ⟨⟨_, hw⟩, rfl⟩
  refine ⟨B.inclusion.preimage (IsOpenImmersion.lift W.ι α hsubset), ?_⟩
  apply B.inclusion.map_injective
  rw [Functor.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
  exact IsOpenImmersion.lift_fac W.ι α hsubset

private noncomputable def fieldPointOnOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hw : (BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier) ∈ W) :
    FieldValuedPoint B S hS
      (yoneda.obj (opensSiteObject B S hS U W)) where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase
  value := Over.homMk (exists_factorization_fieldPointOnOpen B S hS U W p hw).choose (by
    change (_ ≫ B.inclusion.preimage _) ≫ U.hom = _
    rw [(exists_factorization_fieldPointOnOpen B S hS U W p hw).choose_spec]
    exact p.value.w)

private theorem fieldPointOnOpen_value_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hw : (BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier) ∈ W) :
    (fieldPointOnOpen B S hS U W p hw).value.left ≫
      (opensSiteObjectInclusion B S hS U W).left = p.value.left :=
  (exists_factorization_fieldPointOnOpen B S hS U W p hw).choose_spec

private theorem pointsMap_open_inclusion_fieldPointOnOpen
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hw : (BigFppfOver.toScheme B S hS).map p.value
      (IsLocalRing.closedPoint p.carrier) ∈ W) :
    pointsMap B S hS (yoneda.obj (opensSiteObject B S hS U W))
      (yoneda.map (opensSiteObjectInclusion B S hS U W))
      ((fieldPointOnOpen B S hS U W p hw).class B S hS
        (yoneda.obj (opensSiteObject B S hS U W))) = p.class B S hS (yoneda.obj U) := by
  change (FieldValuedPoint.map B S hS
      (yoneda.obj (opensSiteObject B S hS U W))
      (yoneda.map (opensSiteObjectInclusion B S hS U W))
      (fieldPointOnOpen B S hS U W p hw)).class B S hS (yoneda.obj U) = _
  let p' := FieldValuedPoint.map B S hS
      (yoneda.obj (opensSiteObject B S hS U W))
      (yoneda.map (opensSiteObjectInclusion B S hS U W))
      (fieldPointOnOpen B S hS U W p hw)
  have hval : p'.value = p.value :=
    Over.OverMorphism.ext (fieldPointOnOpen_value_comp B S hS U W p hw)
  have hrel : FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj U) p' p := by
    refine ⟨p', FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) p', ?_⟩
    refine ⟨𝟙 p'.siteObject, ?_⟩
    change (yoneda.obj U).map (𝟙 p'.siteObject).op p.value = p'.value
    simp [hval]
    rfl
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj U) hrel

private theorem pointsMap_comp_class
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (β : G ⟶ H) (p : FieldValuedPoint B S hS F) :
    pointsMap B S hS F (α ≫ β) (p.class B S hS F) =
      pointsMap B S hS G β
        (pointsMap B S hS F α (p.class B S hS F)) := by
  rw [pointsMap_class, pointsMap_class, pointsMap_class]
  rfl

private theorem exists_open_chart_factorization
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (_ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (Z : Subfunctor X) (hZ : IsOpenSubspace B S hS Z)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : pointsMap B S hS (yoneda.obj U) a
      (p.class B S hS (yoneda.obj U)) ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι)) :
    ∃ (W : ((BigFppfOver.toScheme B S hS).obj U).Opens),
      schemePoint B S hS U p ∈ W ∧
      ∃ (aZ : yoneda.obj (opensSiteObject B S hS U W) ⟶ Z.toFunctor),
        aZ ≫ Z.ι = yoneda.map (opensSiteObjectInclusion B S hS U W) ≫ a := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let : TopologicalSpace (points B S hS X) :=
    pointTopology B S hS X
  let : TopologicalSpace (points B S hS (yoneda.obj U)) :=
    pointTopology B S hS (yoneda.obj U)
  let s := Set.range (pointsMap B S hS Z.toFunctor Z.ι)
  let e := openSubspacesOrderIso B S hS X hX
  have heq : (e ⟨Z, hZ⟩).1 = s := by
    simpa [s, e] using openSubspacesOrderIso_apply
      B S hS X hX ⟨Z, hZ⟩
  have hs : @IsOpen _ (pointTopology B S hS X) s := by
    rw [← heq]
    exact (e ⟨Z, hZ⟩).2
  let pre := (pointsMap B S hS (yoneda.obj U) a) ⁻¹' s
  have hcont := continuous_pointsMap B S hS a
  have hpre : @IsOpen _ (pointTopology B S hS (yoneda.obj U)) pre :=
    hcont.isOpen_preimage s hs
  obtain ⟨W, hWopen, hWspec⟩ :=
    (isOpen_yoneda_iff_isSchemeOpen B S hS U pre).mp hpre
  have hpW : schemePoint B S hS U p ∈ W := by
    exact (hWspec p).1 (by simpa [pre, s] using hp)
  let Wo : (T.obj U).Opens := ⟨W, hWopen⟩
  let V := opensSiteObject B S hS U Wo
  let j := opensSiteObjectInclusion B S hS U Wo
  let aV : yoneda.obj V ⟶ X := yoneda.map j ≫ a
  have hsub : Set.range (pointsMap B S hS (yoneda.obj V) aV) ⊆ s := by
    intro y hy
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := Quot.exists_rep y
    let qU := FieldValuedPoint.map B S hS (yoneda.obj V)
      (yoneda.map j) q
    have hqW : schemePoint B S hS U qU ∈ W := by
      have heq : schemePoint B S hS U qU =
          (T.map j) (schemePoint B S hS V q) := by
        change T.map (q.value ≫ j) _ = (T.map j) (T.map q.value _)
        rw [Functor.map_comp]
        rfl
      rw [heq, map_opensSiteObjectInclusion]
      exact (schemePoint B S hS V q).property
    have hqpre : qU.class B S hS (yoneda.obj U) ∈ pre := (hWspec qU).2 hqW
    change pointsMap B S hS (yoneda.obj U) a
        (qU.class B S hS (yoneda.obj U)) ∈ s
    simpa [pre, qU, aV, pointsMap] using hqpre
  have hfactor := (factorsThrough_openSubspace_iff_points
      B S hS hX (isAlgebraicSpace_yoneda B S hS V) Z hZ aV).2 hsub
  obtain ⟨aZ, hfac⟩ := hfactor
  exact ⟨Wo, hpW, aZ, hfac⟩

/-- The point selected by a pointed étale chart is the image of the closed point of the
representing field. -/
private theorem sourcePoint_eq_closedPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) :
    c.sourcePoint B S hS = (BigFppfOver.toScheme B S hS).map c.representative.value
      (IsLocalRing.closedPoint c.representative.carrier) := by
  rw [← Subsingleton.elim c.point (IsLocalRing.closedPoint c.representative.carrier)]

/-- The commutativity of a chart square restricts along a factorisation through an open
subobject of the source chart. -/
private theorem yoneda_map_comp_comm
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V V' : BigFppfOver B S hS} {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (i : V' ⟶ U) (h : U ⟶ V) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (f : X ⟶ Y)
    (aZ : yoneda.obj V' ⟶ Z) (ι : Z ⟶ X) (comm : yoneda.map h ≫ b = a ≫ f)
    (hfac : aZ ≫ ι = yoneda.map i ≫ a) :
    yoneda.map (i ≫ h) ≫ b = aZ ≫ ι ≫ f := by
  rw [yoneda.map_comp, Category.assoc, comm, ← Category.assoc, ← hfac, Category.assoc]

/-- The representative of the chart morphism on the whole source chart. -/
private noncomputable def chartTopRepresentative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) :
    MorphismOfGerms.Representative
      ⟨(BigFppfOver.toScheme B S hS).obj c.U, c.sourcePoint B S hS⟩
      ⟨(BigFppfOver.toScheme B S hS).obj c.V,
        ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)⟩ where
  source := ⊤
  mem_source := by simp
  hom := ((BigFppfOver.toScheme B S hS).obj c.U).topIso.hom ≫
    (BigFppfOver.toScheme B S hS).map c.h
  map_point := rfl

add_to_stacks 04RF MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget

/-- A morphism has the germ property at a point exactly when it has the
corresponding scheme-morphism property on an open neighbourhood of that point. -/
@[stacks 04RF "part (2)"]
theorem holdsOnEveryEtaleChartAtPoint_iff_exists_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) :
    HoldsOnEveryEtaleChartAtPoint B S hS
      (MorphismOfGerms.HasRepresentativeWithProperty P) f x ↔
      ∃ (U : Subfunctor X), IsOpenSubspace B S hS U ∧
        x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
          HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f) := by
  constructor
  · intro hAt
    let Q : ∀ {A B : GermOfScheme.{u}},
        MorphismOfGerms A B → Prop :=
      MorphismOfGerms.HasRepresentativeWithProperty P
    have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q :=
      MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget P hP
    obtain ⟨c, hc⟩ :=
      (holdsOnEveryEtaleChartAtPoint_iff_some B S hS Q hQ hX hY f x).1 hAt
    let T := BigFppfOver.toScheme B S hS
    let r0 := chartTopRepresentative B S hS c
    rcases hc with ⟨r, hr, hPr⟩
    have hmk : MorphismOfGerms.mk r =
        MorphismOfGerms.ofSchemeHom (T.map c.h) (c.sourcePoint B S hS) := hr
    have hagree : r.AgreeNear r0 := by
      apply MorphismOfGerms.mk_eq_mk_iff.mp
      show MorphismOfGerms.mk r =
        MorphismOfGerms.mk r0
      rw [hmk]
      rfl
    rcases hagree with ⟨W, hxW, hWr, hWr0, hEq⟩
    have hEt : AlgebraicGeometry.Etale ((T.obj c.U).homOfLE hWr) := by
      infer_instance
    have hPW : P ((T.obj c.U).homOfLE hWr ≫ r.hom) :=
      hP.precomp.precomp ((T.obj c.U).homOfLE hWr) hEt r.hom hPr
    have hPW' : P ((T.obj c.U).homOfLE hWr0 ≫ r0.hom) := by
      rw [← hEq]
      exact hPW
    let aW : yoneda.obj (opensSiteObject B S hS c.U W) ⟶ X :=
      yoneda.map (opensSiteObjectInclusion B S hS c.U W) ≫ c.a
    let hW : opensSiteObject B S hS c.U W ⟶ c.V :=
      opensSiteObjectInclusion B S hS c.U W ≫ c.h
    have haW : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) T)) aW :=
      etale_restriction_opensSiteObject B S hS c.U W c.a c.a_etale
    have hImage := chartOpenImage_points B S hS hX c.U c.a W c.a_etale
    let O := chartOpenImage B S hS hX c.U c.a W c.a_etale
    let V := opensSiteObject B S hS c.U W
    let aO := factorThroughEtaleImage B S hS hX V aW O.1 O.2 hImage
    have hfac : aO ≫ O.1.ι = aW :=
      factorThroughEtaleImage_comp B S hS hX V aW O.1 O.2 hImage
    have haO := etale_factor_through_etaleImage
      (B := B) (S := S) (hS := hS) (U := V) (f := aW)
      (X' := O.1) (hX' := O.2) haW aO hfac
    have hsurj := surjective_factor_through_etaleImage
      (B := B) (S := S) (hS := hS) (U := V) (f := aW)
      (X' := O.1) (hX' := O.2) (hX'image := hImage) aO hfac
    have hcomm : yoneda.map hW ≫ c.b = aO ≫ O.1.ι ≫ f :=
      yoneda_map_comp_comm B S hS _ c.h c.a c.b f aO O.1.ι c.comm hfac
    have hPchart : P (T.map hW) := by
      have h0 : P ((T.obj c.U).homOfLE hWr0 ≫ r0.hom) := hPW'
      -- The restricted representative is the restriction of the chart morphism.
      have heq : (T.obj c.U).homOfLE hWr0 ≫ r0.hom = T.map hW := by
        have hh : T.map hW = W.ι ≫ T.map c.h := map_opensSiteObjectInclusion_comp B S hS W c.h
        dsimp [r0, chartTopRepresentative]
        rw [hh, Scheme.topIso_hom, ← Category.assoc]
        erw [Scheme.homOfLE_ι]
        rfl
      rw [← heq]
      exact h0
    have hGlobal : HoldsOnEveryEtaleChart B S hS P
        (O.1.ι ≫ f) := by
      apply (holdsOnEveryEtaleChart_iff_surjectiveChart
        B S hS P hP O.2.1 hY (O.1.ι ≫ f)).2
      exact ⟨opensSiteObject B S hS c.U W, c.V, aO, c.b, hW,
        haO, c.b_etale, hsurj, hcomm, hPchart⟩
    have hclosed : T.map c.representative.value
        (IsLocalRing.closedPoint c.representative.carrier) ∈ W := by
      rw [← sourcePoint_eq_closedPoint B S hS c]
      exact hxW
    let pOpen := fieldPointOnOpen B S hS c.U W c.representative hclosed
    have hclass : pointsMap B S hS
        (yoneda.obj (opensSiteObject B S hS c.U W)) aW
        (pOpen.class B S hS (yoneda.obj (opensSiteObject B S hS c.U W))) = x := by
      rw [pointsMap_comp_class]
      rw [pointsMap_open_inclusion_fieldPointOnOpen B S hS c.U W
        c.representative hclosed]
      exact c.maps_to
    refine ⟨O.1, O.2, ?_, hGlobal⟩
    rw [hImage]
    exact ⟨pOpen.class B S hS (yoneda.obj (opensSiteObject B S hS c.U W)), hclass⟩
  · rintro ⟨Uo, hUo, hxU, hGlobal⟩
    let Q : ∀ {A B : GermOfScheme.{u}},
        MorphismOfGerms A B → Prop :=
      MorphismOfGerms.HasRepresentativeWithProperty P
    change HoldsOnEveryEtaleChartAtPoint B S hS Q f x
    intro c
    let T := BigFppfOver.toScheme B S hS
    have hp : pointsMap B S hS (yoneda.obj c.U) c.a
        (c.representative.class B S hS (yoneda.obj c.U)) ∈
          Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := by
      rw [c.maps_to]
      exact hxU
    obtain ⟨W, hW, aO, hfac⟩ := exists_open_chart_factorization
      B S hS hX c.U c.a c.a_etale Uo hUo c.representative hp
    let V := opensSiteObject B S hS c.U W
    let aW : yoneda.obj V ⟶ X :=
      yoneda.map (opensSiteObjectInclusion B S hS c.U W) ≫ c.a
    have haW : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) T)) aW :=
      etale_restriction_opensSiteObject B S hS c.U W c.a c.a_etale
    have hpb : IsPullback (𝟙 (yoneda.obj V)) aO aW Uo.ι := by
      apply IsPullback.of_horiz_isIso_mono
      exact ⟨by simpa using hfac.symm⟩
    have haO : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) T)) aO :=
      by
        let Qe := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
        let : PreservesLimitsOfShape WalkingCospan T := inferInstance
        let : Qe.IsStableUnderBaseChange := {
          of_isPullback := by
            intro A C C' D f g f' g' sq hg
            change AlgebraicGeometry.Etale (T.map g) at hg
            change AlgebraicGeometry.Etale (T.map g')
            exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
              (sq.map T) hg }
        let : Qe.presheaf.IsStableUnderBaseChange :=
          MorphismProperty.relative_isStableUnderBaseChange Qe
        exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := Qe.presheaf) hpb haW
    let hW' : V ⟶ c.V := opensSiteObjectInclusion B S hS c.U W ≫ c.h
    have hcomm : yoneda.map hW' ≫ c.b = aO ≫ Uo.ι ≫ f :=
      yoneda_map_comp_comm B S hS _ c.h c.a c.b f aO Uo.ι c.comm hfac
    have hP : P (T.map hW') := hGlobal V c.V aO c.b hW' haO c.b_etale hcomm
    have hsourceW : c.sourcePoint B S hS ∈ W := by
      rw [sourcePoint_eq_closedPoint B S hS c]
      exact hW
    let r : MorphismOfGerms.Representative
        ⟨T.obj c.U, c.sourcePoint B S hS⟩
        ⟨T.obj c.V, (T.map c.h) (c.sourcePoint B S hS)⟩ := {
      source := W
      mem_source := hsourceW
      hom := T.map hW'
      map_point := by
        change (T.map hW') ⟨c.sourcePoint B S hS, hsourceW⟩ =
          (T.map c.h) (c.sourcePoint B S hS)
        dsimp [hW']
        rw [map_opensSiteObjectInclusion_comp]
        rfl }
    let r0 := chartTopRepresentative B S hS c
    have hagree : r.AgreeNear r0 := by
      refine ⟨W, r.mem_source, le_rfl, le_top, ?_⟩
      have hh : T.map hW' = W.ι ≫ T.map c.h := map_opensSiteObjectInclusion_comp B S hS W c.h
      simp [r, r0, chartTopRepresentative, hh]
      rfl
    change MorphismOfGerms.HasRepresentativeWithProperty P
      (MorphismOfGerms.ofSchemeHom (T.map c.h) (c.sourcePoint B S hS))
    refine ⟨r, ?_, hP⟩
    change MorphismOfGerms.mk r =
      MorphismOfGerms.mk r0
    exact MorphismOfGerms.mk_eq_mk_iff.mpr hagree

/-- A morphism of algebraic spaces has an étale-local property if and only if
its germ has the associated property at every source point. -/
@[stacks 04RF "part (3)"]
theorem holdsOnEveryEtaleChart_iff_forall_atPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    HoldsOnEveryEtaleChart B S hS P f ↔
      ∀ x : points B S hS X,
        HoldsOnEveryEtaleChartAtPoint B S hS
          (MorphismOfGerms.HasRepresentativeWithProperty P) f x := by
  -- `hX` and `hY` are not needed: both directions go through the chart data itself, not
  -- through an atlas. They are part of the statement's signature and the lemmas above this one
  -- supply them, so they are kept and discharged here.
  have _ := hX
  have _ := hY
  let T := BigFppfOver.toScheme B S hS
  constructor
  · intro hglobal x c
    exact (AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_forall_hasRepresentativeWithProperty
      P hP (T.map c.h)).1 (hglobal c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm)
      (c.sourcePoint B S hS)
  · intro hAt U V a b h ha hb comm
    apply (AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_forall_hasRepresentativeWithProperty
      P hP (T.map h)).2
    intro y
    let p := schemePointRepresentative B S hS U y
    let x := pointsMap B S hS (yoneda.obj U) a
      (p.class B S hS (yoneda.obj U))
    let c : EtaleChartAtPoint B S hS f x := {
      U := U
      V := V
      a := a
      b := b
      h := h
      a_etale := ha
      b_etale := hb
      comm := comm
      representative := p
      point := IsLocalRing.closedPoint (((T.obj U).residueField y))
      maps_to := rfl }
    have hsource : c.sourcePoint B S hS = y := by
      change (T.map p.value) (IsLocalRing.closedPoint ((T.obj U).residueField y)) = y
      exact schemePointRepresentative_point B S hS U y
    exact hsource ▸ hAt x c

end AlgebraicGeometry.Space

end
