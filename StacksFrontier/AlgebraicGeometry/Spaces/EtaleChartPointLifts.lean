module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeEnoughFields
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# Points of an algebraic space through its étale charts

Let `F` be an algebraic space over `S`. Every point of `|F|` lies in the image of some étale
chart of `F`, and for a morphism `f : F ⟶ G` and an étale chart `V` of `G` whose image contains
`f(y)`, the point `y` lies in the image of an étale chart of `F` mapping to `V` over `f`.

This gives the point-set description of the coverings of the small étale site of `F`
(Stacks 03ED): a family of étale charts covers the final object exactly when the images of
its members cover `|F|`; moreover every geometric point of `F` lifts, over the same field,
through some member of a covering family.

## Main results

* `AlgebraicGeometry.Space.exists_smallEtale_mem_range`: every point of `|F|` is in the
  image of an étale chart.
* `AlgebraicGeometry.Space.exists_smallEtale_chart_lift`: lifting an étale chart of `G`
  through a point of `F` along `f : F ⟶ G`.
* `AlgebraicGeometry.Space.SmallEtale.coversTop_of_forall_mem_range`,
  `AlgebraicGeometry.Space.SmallEtale.exists_mem_range_of_coversTop` and
  `AlgebraicGeometry.Space.SmallEtale.coversTop_iff_forall_mem_range`: a family of étale
  charts covers the final object if and only if its images cover `|F|`.
* `AlgebraicGeometry.Space.SmallEtale.exists_geometricPoint_lift_of_coversTop`: a geometric
  point lifts through a member of a covering family, without extending its field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every point of an algebraic space lies in the image of an étale chart. -/
theorem exists_smallEtale_mem_range {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    ∃ A : SmallEtale B S hS F,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj A.1.left) A.1.hom) :=
  (exists_surjective_smallEtale_chart B S hS F hF).imp fun _ hA => hA x

/-- Pulling back an étale chart `V` of `G` along a map from a representable gives a pullback square
of representables whose projection to the representable is étale. -/
private theorem exists_isPullback_etale_snd {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : SmallEtale B S hS G) {X : BigFppfOver B S hS} (g : yoneda.obj X ⟶ G) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ V.1.left) (q : P ⟶ X),
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        IsPullback (yoneda.map p) (yoneda.map q) V.1.hom g := by
  have hrep : yoneda.relativelyRepresentable V.1.hom := V.property.rep
  refine ⟨_, hrep.fst' g, hrep.snd g,
    V.property.property g (hrep.fst g) (hrep.snd g) (hrep.isPullback g), ?_⟩
  rw [Functor.relativelyRepresentable.map_fst']
  exact hrep.isPullback g

/-- Let `f : F ⟶ G` be a morphism from an algebraic space, `V` an étale chart of `G` and `y` a
point of `F` with `f(y)` in the image of `V`. Then `y` lies in the image of an étale chart `T`
of `F` together with a morphism `T ⟶ V` of schemes over `f`. -/
theorem exists_smallEtale_chart_lift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G) (V : SmallEtale B S hS G)
    (y : points B S hS F)
    (hy : pointsMap B S hS F f y ∈
      Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom)) :
    ∃ (T : SmallEtale B S hS F) (h : T.1.left ⟶ V.1.left),
      y ∈ Set.range (pointsMap B S hS (yoneda.obj T.1.left) T.1.hom) ∧
        yoneda.map h ≫ V.1.hom = T.1.hom ≫ f := by
  obtain ⟨A, a, rfl⟩ := exists_smallEtale_mem_range B S hS hF y
  obtain ⟨v, hv⟩ := hy
  obtain ⟨P, p, q, hqEtale, hsq⟩ := exists_isPullback_etale_snd B S hS V (A.1.hom ≫ f)
  obtain ⟨r, hr₁, hr₂⟩ := exists_points_of_isPullback B S hS hsq v a
    (by rw [hv, pointsMap_comp_apply])
  refine ⟨⟨CostructuredArrow.mk (yoneda.map q ≫ A.1.hom),
    etale_comp_of_scheme B S hS q A.1.hom hqEtale A.property⟩, p, ⟨r, ?_⟩, ?_⟩
  · change pointsMap B S hS _ (yoneda.map q ≫ A.1.hom) r = _
    rw [pointsMap_comp_apply, hr₂]
  · change yoneda.map p ≫ V.1.hom = (yoneda.map q ≫ A.1.hom) ≫ f
    rw [hsq.w, Category.assoc]

namespace SmallEtale

/-- A family of étale charts of an algebraic space whose images cover the points of the space
covers the final object of the small étale site. -/
theorem coversTop_of_forall_mem_range {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {ι : Type*} {V : ι → SmallEtale B S hS F}
    (hV : ∀ x : points B S hS F, ∃ i,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj (V i).1.left) (V i).1.hom)) :
    (SmallEtale.topology B S hS F).CoversTop V := by
  intro W
  refine smallEtale_sieve_of_pointwise_covering B S hS F W _ fun z => ?_
  set w := (pointsEquivScheme B S hS W.1.left).symm z
  obtain ⟨i, v, hv⟩ := hV (pointsMap B S hS _ W.1.hom w)
  obtain ⟨P, p, q, hqEtale, hsq⟩ := exists_isPullback_etale_snd B S hS (V i) W.1.hom
  obtain ⟨r, -, hr₂⟩ := exists_points_of_isPullback B S hS hsq v w hv
  let Vc : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map q ≫ W.1.hom),
      etale_comp_of_scheme B S hS q W.1.hom hqEtale W.property⟩
  let a : Vc ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk q rfl)
  let b : Vc ⟶ V i := ObjectProperty.homMk (CostructuredArrow.homMk p hsq.w)
  refine ⟨Vc, a, ⟨i, ⟨b⟩⟩, pointsToScheme B S hS _ r, ?_⟩
  change (BigFppfOver.toScheme B S hS).map q (pointsToScheme B S hS _ r) = z
  rw [← pointsToScheme_pointsMap_yoneda, hr₂]
  exact (pointsEquivScheme B S hS W.1.left).apply_symm_apply z

/-- A geometric point of an algebraic space lifts, over the same algebraically closed field,
through some member of any family of étale charts covering the final object of the small
étale site. -/
theorem exists_geometricPoint_lift_of_coversTop {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {ι : Type*} {V : ι → SmallEtale B S hS F}
    (hV : (SmallEtale.topology B S hS F).CoversTop V) (t : GeometricPoint B S hS F) :
    ∃ i, ∃ t' : GeometricPoint B S hS (yoneda.obj (V i).1.left),
      FieldValuedPoint.map B S hS _ (V i).1.hom t'.val = t.val := by
  obtain ⟨A, a, ha⟩ := exists_smallEtale_mem_range B S hS hF t.image
  obtain ⟨abar, -, habar⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (isAlgebraicSpace_yoneda B S hS A.1.left) hF A.1.hom
    ((isEtale_iff_presheaf_of_yoneda B S hS A.1.hom).2 A.property) t a ha
  obtain ⟨t, ht⟩ := t
  obtain ⟨abar, habar'⟩ := abar
  subst habar
  obtain ⟨Y, -, ⟨i, ⟨k⟩⟩, ⟨y, hy⟩, -⟩ := (etaleSitePoint B S hS F
    ⟨_, ht⟩ hF).jointly_surjective _ (hV A) ⟨abar.value, rfl⟩
  let t' : FieldValuedPoint B S hS (yoneda.obj (V i).1.left) :=
    { abar with value := y ≫ (SmallEtale.toOver B S hS F).map k }
  refine ⟨i, ⟨t', ht⟩, ?_⟩
  have hk : yoneda.map ((SmallEtale.toOver B S hS F).map k) ≫ (V i).1.hom = Y.1.hom :=
    ((SmallEtale.inclusion B S hS F).map k).w
  change FieldValuedPoint.map B S hS _ (V i).1.hom t' =
    FieldValuedPoint.map B S hS _ A.1.hom abar
  simp only [FieldValuedPoint.map]
  congr 1
  exact Eq.trans (by rw [← hk]; rfl) hy

/-- The images of the members of a family of étale charts covering the final object of the small
étale site of an algebraic space cover the points of the space. -/
theorem exists_mem_range_of_coversTop {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {ι : Type*} {V : ι → SmallEtale B S hS F}
    (hV : (SmallEtale.topology B S hS F).CoversTop V) (x : points B S hS F) :
    ∃ i, x ∈ Set.range (pointsMap B S hS (yoneda.obj (V i).1.left) (V i).1.hom) := by
  obtain ⟨t, rfl⟩ := (geometricPoints_large_enough B S hS F F hF hF).1 x
  obtain ⟨i, t', ht'⟩ := exists_geometricPoint_lift_of_coversTop B S hS hF hV t
  exact ⟨i, t'.image, by rw [pointsMap_class, ht']⟩

/-- A family of étale charts of an algebraic space covers the final object of the small étale
site if and only if the images of its members cover the points of the space. -/
theorem coversTop_iff_forall_mem_range {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {ι : Type*} (V : ι → SmallEtale B S hS F) :
    (SmallEtale.topology B S hS F).CoversTop V ↔ ∀ x : points B S hS F, ∃ i,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj (V i).1.left) (V i).1.hom) :=
  ⟨fun hV => exists_mem_range_of_coversTop B S hS hF hV,
    coversTop_of_forall_mem_range B S hS⟩

end SmallEtale

end AlgebraicGeometry.Space

end
