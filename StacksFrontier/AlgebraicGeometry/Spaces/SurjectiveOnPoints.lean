module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Surjectivity of a morphism of algebraic spaces, tested on points

Let `F` and `G` be presheaves on the big fppf site of a scheme `S` and let `f : F ⟶ G` be a
relatively representable morphism. Then every base change of `f` by a scheme over `G` is a
surjective morphism of schemes if and only if the induced map `|F| → |G|` on points is
surjective, that is, `AlgebraicGeometry.Space.IsSurjective` holds. Surjectivity on points is
stable under base change.

## Main definitions

* `AlgebraicGeometry.Space.toSchemeFieldValuedPoint`: a field-valued point of a represented
  presheaf, read as a field-valued point of the representing scheme.
* `AlgebraicGeometry.Space.schemePointRepresentative`: the canonical field-valued
  representative of a point of the representing scheme.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`: a morphism of presheaves
  surjective after every represented base change is surjective on points.
* `AlgebraicGeometry.Space.presheafSurjective_of_isSurjective`: the converse, for a
  relatively representable morphism.
* `AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective`: the criterion for a
  relatively representable morphism of algebraic spaces.
* `AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`: the criterion for a
  morphism from a scheme to an algebraic space.
* `AlgebraicGeometry.Space.surjective_yonedaMap_iff_surjective_pointsMap`: the criterion for a
  morphism of the site.
* `AlgebraicGeometry.Space.isSurjective_of_isPullback`: a base change of a morphism of
  algebraic spaces surjective on points is surjective on points.

## References

* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of a represented presheaf -/

/-- A field-valued point of the presheaf represented by `U`, read as a field-valued point of
the scheme underlying `U`: the same field, with the section of the represented presheaf
regarded as a morphism of schemes. -/
noncomputable def toSchemeFieldValuedPoint (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    AlgebraicGeometry.FieldValuedPoint ((BigFppfOver.toScheme B S hS).obj U) where
  carrier := p.carrier
  field := p.field
  map := B.inclusion.map p.value.left

/-- The map `pointsToScheme` from points of a represented presheaf to points of the
representing scheme is natural. -/
theorem pointsToScheme_pointsMap {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (x : points B S hS (yoneda.obj U)) :
    pointsToScheme B S hS V (pointsMap B S hS (yoneda.obj U) (yoneda.map f) x) =
      (BigFppfOver.toScheme B S hS).map f (pointsToScheme B S hS U x) := by
  refine Quot.inductionOn x ?_
  intro p
  rw [pointsMap_class]
  rfl

/-- The canonical field-valued point of the presheaf represented by `T` above a point `x` of
the scheme underlying `T`: the residue field at `x`, with the canonical morphism
`Spec κ(x) ⟶ T`. -/
noncomputable def schemePointRepresentative (T : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    FieldValuedPoint B S hS (yoneda.obj T) := by
  let Z := (BigFppfOver.toScheme B S hS).obj T
  let hK : B.Contains (Spec (Z.residueField x)) :=
    B.residueField_spec_contains T.left.property x
  let kobj : B.Schemes := B.obj hK
  let f : kobj ⟶ T.left :=
    B.inclusion.preimage (X := kobj) (Y := T.left) (Z.fromSpecResidueField x)
  refine ⟨Z.residueField x, hK, B.inclusion.map (f ≫ T.hom), ?_⟩
  change (Over.mk (f ≫ T.hom) : BigFppfOver B S hS) ⟶ T
  exact Over.homMk f

/-- The canonical representative of a point of the representing scheme does lie above that
point. -/
theorem schemePointRepresentative_point (T : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    schemePoint B S hS T (schemePointRepresentative B S hS T x) = x := by
  let Z := (BigFppfOver.toScheme B S hS).obj T
  let kobj : B.Schemes := B.obj (B.residueField_spec_contains T.left.property x)
  show (B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := T.left)
    (Z.fromSpecResidueField x))) _ = x
  rw [B.inclusion.map_preimage]
  exact Scheme.fromSpecResidueField_apply x _

/-- The canonical representative above the image of a field-valued point represents the same
point of the presheaf. -/
theorem schemePointRepresentative_class (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    (schemePointRepresentative B S hS U
        ((BigFppfOver.toScheme B S hS).map p.value
          (IsLocalRing.closedPoint p.carrier))).class B S hS (yoneda.obj U) =
      p.class B S hS (yoneda.obj U) := by
  let X := (BigFppfOver.toScheme B S hS).obj U
  let x := (BigFppfOver.toScheme B S hS).map p.value (IsLocalRing.closedPoint p.carrier)
  let hp := toSchemeFieldValuedPoint B S hS U p
  have hpx : hp.point = x := rfl
  have hcx : (AlgebraicGeometry.FieldValuedPoint.canonical X x).point = x :=
    Scheme.fromSpecResidueField_apply x _
  obtain ⟨φ, hφ, -⟩ :=
    (AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest x) hp (hpx.trans hcx.symm)
  let q := schemePointRepresentative B S hS U x
  have hqmap : B.inclusion.map q.value.left =
      (AlgebraicGeometry.FieldValuedPoint.canonical X x).map := by
    let kobj : B.Schemes := B.obj (B.residueField_spec_contains U.left.property x)
    show B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left)
      (X.fromSpecResidueField x)) = X.fromSpecResidueField x
    rw [B.inclusion.map_preimage]
  let φ' : B.inclusion.obj (p.siteObject B S hS (yoneda.obj U)).left ⟶
      B.inclusion.obj (q.siteObject B S hS (yoneda.obj U)).left := by
    show Spec (.of p.carrier) ⟶ Spec (.of q.carrier)
    exact φ
  let fbase : (p.siteObject B S hS (yoneda.obj U)).left ⟶
      (q.siteObject B S hS (yoneda.obj U)).left := B.inclusion.preimage φ'
  have hmapbase : B.inclusion.map fbase = φ' := B.inclusion.map_preimage φ'
  have hleftScheme : B.inclusion.map fbase ≫ B.inclusion.map q.value.left =
      B.inclusion.map p.value.left := by
    rw [hmapbase, hqmap]
    exact hφ
  have hleft : fbase ≫ q.value.left = p.value.left :=
    B.inclusion.map_injective hleftScheme
  have hbase₀ (r : FieldValuedPoint B S hS (yoneda.obj U)) :
      B.inclusion.map r.value.left ≫ B.inclusion.map U.hom = r.toBase := by
    rw [← Functor.map_comp]
    simp
  have hbase : fbase ≫ (q.siteObject B S hS (yoneda.obj U)).hom =
      (p.siteObject B S hS (yoneda.obj U)).hom := by
    apply B.inclusion.map_injective
    show B.inclusion.map fbase ≫ q.toBase = p.toBase
    rw [← hbase₀ q, ← hbase₀ p]
    exact congrArg (fun k ↦ k ≫ B.inclusion.map U.hom) hleftScheme
  have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj U) p q :=
    ⟨Over.homMk fbase hbase, Over.OverMorphism.ext hleft⟩
  exact (FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj U)
    ⟨p, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) p, hdom⟩).symm

/-- If a point of the representing scheme of `V` lifts along a morphism `h : U ⟶ V` of the site,
then the corresponding point of the represented presheaf lifts along `yoneda.map h`. -/
private theorem exists_pointsMap_eq_of_scheme_map {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (y : points B S hS (yoneda.obj V)) (x : (BigFppfOver.toScheme B S hS).obj U)
    (hx : (BigFppfOver.toScheme B S hS).map h x = pointsToScheme B S hS V y) :
    ∃ z, pointsMap B S hS (yoneda.obj U) (yoneda.map h) z = y := by
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS U x
  refine ⟨z, injective_pointsToScheme B S hS V ?_⟩
  rw [pointsToScheme_pointsMap, hz, hx]

/-- A family of morphisms of the site which is jointly surjective on the points of the
representing schemes has Yoneda images which are jointly surjective on points. -/
theorem jointlySurjective_yoneda_of_scheme {I : Type v} {T : BigFppfOver B S hS}
    (U : I → BigFppfOver B S hS) (f : ∀ i, U i ⟶ T)
    (h : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, ∃ y : (BigFppfOver.toScheme B S hS).obj (U i),
        (BigFppfOver.toScheme B S hS).map (f i) y = x) :
    (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (U i)) (yoneda.map (f i)))) = Set.univ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  obtain ⟨i, y, hy⟩ := h (pointsToScheme B S hS T p)
  exact Set.mem_iUnion.mpr ⟨i, exists_pointsMap_eq_of_scheme_map B S hS (f i) p y hy⟩

/-! ### From relatively representable surjectivity to surjectivity on points -/

/-- A morphism of presheaves on the big fppf site of `S` which is surjective after every
represented base change is surjective on points. -/
theorem isSurjective_of_presheafSurjective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsSurjective B S hS f := by
  intro y
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  set A : BigFppfOver B S hS := FieldValuedPoint.siteObject B S hS G q
  set g : yoneda.obj A ⟶ G := yonedaEquiv.symm q.value with hg
  have hgv : yonedaEquiv g = q.value := by rw [hg, Equiv.apply_symm_apply]
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map (hf.rep.snd g)) :=
    hf.property_snd g
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj A) :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of q.carrier)))
  obtain ⟨z, -⟩ := hsurj.surj (Classical.arbitrary _)
  obtain ⟨Ω, instΩ, hΩ, ρ, -⟩ :=
    exists_fieldSpec_at_point B (hf.rep.pullback g).left.2 z
  set W : BigFppfOver B S hS :=
    Over.mk (⟨ρ ≫ (hf.rep.pullback g).hom.hom⟩ : B.obj hΩ ⟶ B.obj hS)
  set σ : W ⟶ hf.rep.pullback g :=
    Over.homMk (⟨ρ⟩ : B.obj hΩ ⟶ (hf.rep.pullback g).left) (by ext; rfl)
  refine ⟨FieldValuedPoint.class B S hS F
      { carrier := Ω, contained := hΩ, toBase := ρ ≫ (hf.rep.pullback g).hom.hom
        value := yonedaEquiv (yoneda.map σ ≫ hf.rep.fst g) }, ?_⟩
  rw [pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G
    ⟨_, FieldValuedPoint.dominates_refl B S hS G _, ⟨σ ≫ hf.rep.snd g, ?_⟩⟩
  have hw : (yoneda.map σ ≫ hf.rep.fst g) ≫ f = yoneda.map (σ ≫ hf.rep.snd g) ≫ g := by
    rw [Functor.map_comp, Category.assoc, Category.assoc, hf.rep.w]
  show G.map (σ ≫ hf.rep.snd g).op q.value =
    f.app _ (yonedaEquiv (yoneda.map σ ≫ hf.rep.fst g))
  rw [← yonedaEquiv_comp, hw, ← hgv, yonedaEquiv_naturality]

/-! ### From surjectivity on points to relatively representable surjectivity -/

/-- A relatively representable morphism of presheaves on the big fppf site of `S` which is
surjective on points is surjective after every represented base change. -/
theorem presheafSurjective_of_isSurjective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hrep : yoneda.relativelyRepresentable f) (hf : IsSurjective B S hS f) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hrep fun a g => ?_
  refine ⟨fun x => ?_⟩
  obtain ⟨K, instK, hK, ρ, hρ⟩ := exists_fieldSpec_at_point B a.left.2 x
  set W : BigFppfOver B S hS := Over.mk (⟨ρ ≫ a.hom.hom⟩ : B.obj hK ⟶ B.obj hS)
  set σ : W ⟶ a := Over.homMk (⟨ρ⟩ : B.obj hK ⟶ a.left) (by ext; rfl)
  obtain ⟨w, hw⟩ := hf (FieldValuedPoint.class B S hS G
    { carrier := K, contained := hK, toBase := ρ ≫ a.hom.hom
      value := yonedaEquiv (yoneda.map σ ≫ g) })
  obtain ⟨m, rfl⟩ := Quot.exists_rep w
  rw [pointsMap_class, FieldValuedPoint.class_eq_class_iff] at hw
  obtain ⟨r, hrm, hrp⟩ := hw
  obtain ⟨R, Wm, v, α, β, val, ⟨t⟩, hα, hβ⟩ :
      ∃ (R Wm : BigFppfOver B S hS) (v : F.obj (Opposite.op Wm)) (α : R ⟶ Wm) (β : R ⟶ W)
        (val : G.obj (Opposite.op R)),
        Nonempty ((BigFppfOver.toScheme B S hS).obj R) ∧
        G.map α.op (f.app (Opposite.op Wm) v) = val ∧
        G.map β.op (yonedaEquiv (yoneda.map σ ≫ g)) = val :=
    ⟨_, _, m.value, hrm.choose, hrp.choose, r.value,
      inferInstanceAs (Nonempty (Spec (CommRingCat.of r.carrier))),
      hrm.choose_spec, hrp.choose_spec⟩
  have hA : yonedaEquiv (yonedaEquiv.symm (F.map α.op v) ≫ f) = val := by
    rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, NatTrans.naturality_apply]
  have hBe : yonedaEquiv (yoneda.map β ≫ yoneda.map σ ≫ g) = val := by
    rwa [← yonedaEquiv_naturality (yoneda.map σ ≫ g) β]
  have hsq : yonedaEquiv.symm (F.map α.op v) ≫ f = yoneda.map (β ≫ σ) ≫ g := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    exact yonedaEquiv.injective (hA.trans hBe.symm)
  have hfac := hrep.lift_snd (yonedaEquiv.symm (F.map α.op v)) (β ≫ σ) hsq
  have hcomp : (BigFppfOver.toScheme B S hS).map
        (hrep.lift (yonedaEquiv.symm (F.map α.op v)) (β ≫ σ) hsq) ≫
      (BigFppfOver.toScheme B S hS).map (hrep.snd g) =
      (BigFppfOver.toScheme B S hS).map β ≫ ρ := by
    rw [← Functor.map_comp, hfac]
    rfl
  refine ⟨(BigFppfOver.toScheme B S hS).map
    (hrep.lift (yonedaEquiv.symm (F.map α.op v)) (β ≫ σ) hsq) t, ?_⟩
  rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply, hρ]

/-! ### Tags 03MD and 03H5 -/

/-- A relatively representable morphism of algebraic spaces over `S` is surjective, in the sense
that every represented base change of it is a surjective morphism of schemes, if and only if the
induced map on points is surjective. -/
theorem presheafSurjective_iff_isSurjective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : IsAlgebraicSpace B S hS F) (_hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hrep : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔ IsSurjective B S hS f :=
  ⟨isSurjective_of_presheafSurjective B S hS f,
    presheafSurjective_of_isSurjective B S hS f hrep⟩

/-- A morphism from a scheme over `S` to an algebraic space over `S` is surjective, in the sense
that every represented base change of it is a surjective morphism of schemes, if and only if the
induced map on points is surjective. -/
@[stacks 03H5]
theorem presheafSurjective_iff_isSurjective_yoneda (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ F) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔ IsSurjective B S hS f :=
  ⟨isSurjective_of_presheafSurjective B S hS f,
    presheafSurjective_of_isSurjective B S hS f (hF.diagonal_representable.of_diag f)⟩

/-- `AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective`, with the point-set side
spelled out as `Function.Surjective`. -/
theorem surjective_iff_pointsMap_surjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Function.Surjective (pointsMap B S hS F f) :=
  presheafSurjective_iff_isSurjective B S hS hF hG f hf

/-- `AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`, with the point-set
side spelled out as `Function.Surjective`. -/
theorem surjective_iff_surjective_pointsMap
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ F) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔
      Function.Surjective (pointsMap B S hS (yoneda.obj T) f) :=
  presheafSurjective_iff_isSurjective_yoneda B S hS F hF T f

/-! ### The represented case, and stability under base change -/

/-- Surjectivity of a morphism of schemes, pulled back along the forgetful functor to
schemes, is stable under base change in the big fppf site over `S`. -/
private instance surjectiveProperty_isStableUnderBaseChange :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨by
    intro X Y Y' Z f g f' g' hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Surjective) (hs.map (BigFppfOver.toScheme B S hS)) hg⟩

/-- The Yoneda image of a morphism of the big fppf site over `S` is surjective after every base
change exactly when it is surjective on the points of the represented presheaves. -/
theorem surjective_yonedaMap_iff_surjective_pointsMap {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map h) ↔
      Function.Surjective (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) := by
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  refine (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).trans ?_
  refine (AlgebraicGeometry.surjective_iff ((BigFppfOver.toScheme B S hS).map h)).trans ?_
  constructor
  · intro hsurj y
    obtain ⟨x, hx⟩ := hsurj (pointsToScheme B S hS V y)
    exact exists_pointsMap_eq_of_scheme_map B S hS h y x hx
  · intro hsurj y
    obtain ⟨z, hz⟩ := hsurj ((schemePointRepresentative B S hS V y).class B S hS (yoneda.obj V))
    refine ⟨pointsToScheme B S hS U z, ?_⟩
    rw [← pointsToScheme_pointsMap, hz]
    exact schemePointRepresentative_point B S hS V y

/-- The Yoneda image of a morphism of the site whose underlying morphism of schemes is surjective
is surjective on points. -/
theorem isSurjective_yoneda_map {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map h)) :
    IsSurjective B S hS (yoneda.map h) :=
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  (surjective_yonedaMap_iff_surjective_pointsMap B S hS h).mp
    ((MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).mpr hh)

/-- A base change of a morphism of algebraic spaces surjective on points is surjective on
points. -/
@[stacks 03MH]
theorem isSurjective_of_isPullback {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f) (hg : IsSurjective B S hS g.hom) :
    IsSurjective B S hS q.hom := by
  intro x
  obtain ⟨z, hz⟩ := hg (pointsMap B S hS X.1 f.hom x)
  obtain ⟨w, -, hwq⟩ := exists_point_of_isPullback B S hS sq z x hz
  exact ⟨w, hwq⟩

end AlgebraicGeometry.Space

end
