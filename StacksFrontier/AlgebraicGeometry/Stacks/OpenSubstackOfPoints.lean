module

public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange

/-!
# The open substack with a prescribed open set of points (Stacks 06FJ)

Let `𝒳` be an algebraic stack over `S`. **Stacks 06FJ** says that `𝒰 ↦ |𝒰|` is a bijection from
the open substacks of `𝒳` onto the open subsets of `|𝒳|`. This file proves its surjectivity in the
explicit form a consumer needs: for an open `Ω ⊆ |𝒳|`, the objects of `𝒳` every point seen by
which lies in `Ω` form an open substack, `AlgebraicGeometry.Stack.openSubstackOfPoints`, whose
point set is `Ω`.

## Main definitions

* `AlgebraicGeometry.Stack.openSubstackOfPoints`: the open substack cut out by an open set of
  points.
* `AlgebraicGeometry.Stack.schemeSlicePoint`: the point of the scheme `U` underlying a point of
  the big fppf site of `U` read as a category fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.openSubstackOfPoints_property` and
  `AlgebraicGeometry.Stack.pointSet_openSubstackOfPoints`: its objects and its points.
* `AlgebraicGeometry.Stack.pointsWithin_obj_iff`: the points seen by the image of an object along
  a 1-morphism are the images of the points seen by the object.
* `AlgebraicGeometry.Stack.exists_openSubstack_property_eq`: a property of objects inherited
  along morphisms which is cut out, along every scheme-valued point, by an open subscheme of the
  base is the property of an open substack.

## Implementation notes

Along a scheme-valued point `y` of `𝒳` with values in `U`, the base change of the inclusion of
the full subcategory `AlgebraicGeometry.Stack.pointsWithin 𝒳 Ω` is the subfunctor of `yoneda U`
of `AlgebraicGeometry.Stack.nonempty_equivalenceOver_fullSubcategoryBaseChange`. That subfunctor
is the functor of points of the open subscheme `V ⊆ U` lying over `Ω`: `V` is open because `Ω`
pulled back along `y` is open (**Stacks 04XL**, continuity) and the big fppf site of `U` is
represented by `U` (`AlgebraicGeometry.Stack.exists_isOpen_mem_iff_schemeSlicePoint_mem`), and an
object of the site of `U` maps into `V` exactly when every point it sees lies over `Ω`
(`AlgebraicGeometry.Stack.exists_isOpen_pointsWithin_iff`). Representability by algebraic spaces
and the open-immersion condition of **Stacks 04XB** follow, since every algebraic space
representing the base change is isomorphic to `V`; the full subcategory is then an algebraic
stack by **Stacks 05UM**.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Points of the big fppf site of a scheme, read as a category fibred in groupoids -/

section SchemeSlicePoint

variable (U : BigFppfOver B S hS)

/-- The point of the scheme underlying `U` determined by a field-valued point of the big fppf
site of `U`, viewed as a category fibred in groupoids over the big fppf site of `S`: the image of
the closed point of the field spectrum under the structure morphism of the object. -/
noncomputable def schemeSlicePointOfField
    (p : FieldValuedPoint B S hS (schemeSlice B S hS U).val) :
    (BigFppfOver.toScheme B S hS).obj U :=
  B.inclusion.map p.obj.hom
    (((BigFppfOver.toScheme B S hS).mapIso (eqToIso p.over) ≪≫ p.isSpec).inv
      (IsLocalRing.closedPoint p.carrier))

/-- A morphism between the objects of two field-valued points of the big fppf site of `U` does
not move the underlying scheme point: the source field spectrum is a one-point space. -/
theorem schemeSlicePointOfField_eq_of_hom
    (p q : FieldValuedPoint B S hS (schemeSlice B S hS U).val) (a : p.obj ⟶ q.obj) :
    schemeSlicePointOfField U p = schemeSlicePointOfField U q := by
  let T := BigFppfOver.toScheme B S hS
  let e : T.obj ((schemeSlice B S hS U).val.p.obj q.obj) ≅ Spec (.of q.carrier) :=
    T.mapIso (eqToIso q.over) ≪≫ q.isSpec
  have : Subsingleton (T.obj ((schemeSlice B S hS U).val.p.obj q.obj)) :=
    ⟨fun x y => e.schemeIsoToHomeo.injective (Subsingleton.elim _ _)⟩
  unfold schemeSlicePointOfField
  have hw : B.inclusion.map a.left ≫ B.inclusion.map q.obj.hom =
      B.inclusion.map p.obj.hom := by
    rw [← B.inclusion.map_comp, Over.w a]
  rw [← hw]
  exact congrArg (B.inclusion.map q.obj.hom) (Subsingleton.elim (α := T.obj
    ((schemeSlice B S hS U).val.p.obj q.obj)) _ _)

/-- The point of the scheme underlying `U` determined by a point of the big fppf site of `U`,
viewed as a category fibred in groupoids over the big fppf site of `S`. -/
noncomputable def schemeSlicePoint :
    points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property →
      (BigFppfOver.toScheme B S hS).obj U :=
  Quotient.lift (schemeSlicePointOfField U) (by
    rintro p q ⟨r, ⟨a⟩, ⟨b⟩⟩
    exact (schemeSlicePointOfField_eq_of_hom U r p a).symm.trans
      (schemeSlicePointOfField_eq_of_hom U r q b))

/-- The chart of the big fppf site of `U` by the presheaf `U` represents. -/
noncomputable abbrev schemeSliceChart :
    (fibredCategory B S hS (yoneda.obj U)).val ⥤ᵇ (schemeSlice B S hS U).val :=
  (representingEquivalence B S hS (yoneda.obj U) (schemeSlice B S hS U)
    (schemeSliceEquivalenceOver B S hS U)).functor

/-- The scheme point of the point of the big fppf site of `U` charted by a field-valued point of
the presheaf `U` represents is that field-valued point's scheme point. -/
theorem schemeSlicePoint_spacePointMap (p : Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    schemeSlicePoint U (spacePointMap B S hS (yoneda.obj U) (schemeSlice B S hS U)
      (schemeSliceChart U) (p.class B S hS (yoneda.obj U))) = Space.schemePoint B S hS U p := by
  rw [spacePointMap_class]
  show schemeSlicePointOfField U _ = _
  simp only [schemeSlicePointOfField, Iso.trans_inv, Functor.mapIso_inv, eqToIso.inv,
    BigFppfOver.toScheme, Functor.comp_map, BigFppfOver.forget, Over.forget_map,
    Over.eqToHom_left]
  rfl

/-- **An open set of points of the big fppf site of `U` is cut out by an open subset of the
scheme `U`.** -/
theorem exists_isOpen_mem_iff_schemeSlicePoint_mem
    (Ω : Set (points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property))
    (hΩ : @IsOpen _ (pointTopology B S hS (schemeSlice B S hS U)) Ω) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsOpen V ∧
      ∀ z, z ∈ Ω ↔ schemeSlicePoint U z ∈ V := by
  have hW := (isOpen_pointTopology_iff B S hS (schemeSlice B S hS U) Ω).1 hΩ
    ⟨⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩, schemeSliceChart U⟩
  obtain ⟨V, hV, hVW⟩ := (Space.isOpen_yoneda_iff_isSchemeOpen B S hS U _).1 hW
  refine ⟨V, hV, fun z => ?_⟩
  obtain ⟨w, rfl⟩ := (bijective_spacePointMap_representing B S hS (yoneda.obj U)
    (schemeSlice B S hS U) (schemeSliceEquivalenceOver B S hS U)).2 z
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  rw [show Quot.mk _ p = p.class B S hS (yoneda.obj U) from rfl,
    schemeSlicePoint_spacePointMap]
  exact hVW p

end SchemeSlicePoint

/-! ### The property cut out by a set of points, read along a 1-morphism -/

/-- **The points seen by the image of an object along a 1-morphism.** For a 1-morphism
`F : 𝒜 ⟶ 𝒳` of categories fibred in groupoids into an algebraic stack and an object `a` of `𝒜`,
every point of `|𝒳|` seen by `F a` lies in `Ω` exactly when the image under `F` of every point
seen by `a` does: a field-valued point of `𝒳` with a morphism to `F a` is, up to a common
refinement, the image of a field-valued point of `𝒜` with a morphism to `a`, obtained by lifting
the underlying morphism of the site. -/
theorem pointsWithin_obj_iff
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : 𝒜.val ⥤ᵇ 𝒳.val.val)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property)) (a : 𝒜.val.obj) :
    pointsWithin 𝒳 Ω (F.obj a) ↔
      ∀ (r : FieldValuedPoint B S hS 𝒜.val) (_ : r.obj ⟶ a),
        pointsMap B S hS 𝒜.val 𝒜.property 𝒳.val.property F
          (pointClass B S hS 𝒜.val 𝒜.property r) ∈ Ω := by
  constructor
  · intro h r ψ
    exact h (fieldValuedPointMap B S hS 𝒜.val F r) (F.map ψ)
  · intro h q φ
    let f₀ : q.base ⟶ 𝒜.val.p.obj a :=
      eqToHom q.over.symm ≫ 𝒳.val.val.p.map φ ≫ eqToHom (F.w_obj a)
    obtain ⟨y, ψ, hψ⟩ := 𝒜.property.exists_lift f₀ a rfl
    have hy : 𝒜.val.p.obj y = q.base := IsHomLift.domain_eq 𝒜.val.p f₀ ψ
    let r : FieldValuedPoint B S hS 𝒜.val :=
      { carrier := q.carrier
        base := q.base
        isSpec := q.isSpec
        obj := y
        «over» := hy }
    have hFψ : 𝒳.val.val.p.IsHomLift f₀ (F.map ψ) := inferInstance
    obtain ⟨χ, -, -⟩ := 𝒳.val.property.unique_lift (F.map ψ) φ
      (eqToHom (q.over.trans (hy.symm.trans (F.w_obj y).symm))) (by
        rw [IsHomLift.fac' 𝒳.val.val.p f₀ (F.map ψ)]
        simp [f₀])
    convert h r ψ using 1
    exact (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2 ⟨q, ⟨𝟙 _⟩, ⟨χ⟩⟩

/-- **The points of the big fppf site of `U` seen by an object, read on the scheme.** For an
object `T` of the big fppf site of `U`, every point of the big fppf site of `U` seen by `T` lies
in a set `Ω` cut out by an open `V` of the scheme `U` exactly when the structure morphism of `T`
lands in `V`. -/
theorem forall_mem_of_hom_iff_range_subset {U : BigFppfOver B S hS}
    {Ω : Set (points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property)}
    {V : Set ((BigFppfOver.toScheme B S hS).obj U)}
    (hΩV : ∀ z, z ∈ Ω ↔ schemeSlicePoint U z ∈ V) (T : BigFppfOver B U.left.1 U.left.2) :
    (∀ (r : FieldValuedPoint B S hS (schemeSlice B S hS U).val) (_ : r.obj ⟶ T),
        pointClass B S hS _ (schemeSlice B S hS U).property r ∈ Ω) ↔
      Set.range (B.inclusion.map T.hom) ⊆ V := by
  constructor
  · rintro h _ ⟨t, rfl⟩
    obtain ⟨p, hp⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS
      ((Over.map U.hom).obj T) t
    let o : BigFppfOver B U.left.1 U.left.2 := Over.mk (p.value.left ≫ T.hom)
    let r : FieldValuedPoint B S hS (schemeSlice B S hS U).val :=
      { carrier := p.carrier
        base := (Over.map U.hom).obj o
        isSpec := Iso.refl _
        obj := o
        «over» := rfl }
    have hr := (hΩV _).1 (h r (Over.homMk p.value.left rfl))
    rw [← hp]
    exact hr
  · intro h r ψ
    refine (hΩV _).2 (h ?_)
    refine ⟨B.inclusion.map ψ.left (((BigFppfOver.toScheme B S hS).mapIso
      (eqToIso r.over) ≪≫ r.isSpec).inv (IsLocalRing.closedPoint r.carrier)), ?_⟩
    show _ = schemeSlicePointOfField U r
    unfold schemeSlicePointOfField
    rw [← Over.w ψ, B.inclusion.map_comp]
    rfl

/-- **The scheme-valued points along which every point seen lies in an open set.** Let `Ω` be an
open set of points of an algebraic stack `𝒳` and let `y` be a scheme-valued point of `𝒳` with
values in `U`. There is an open `V` of the scheme `U` such that, for every object `T` of the big
fppf site of `U`, every point of `|𝒳|` seen by `y T` lies in `Ω` exactly when the structure
morphism of `T` lands in `V`. -/
theorem exists_isOpen_pointsWithin_iff (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsOpen V ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        pointsWithin 𝒳 Ω (y.obj T) ↔ Set.range (B.inclusion.map T.hom) ⊆ V := by
  let F : (schemeSlice B S hS U).val ⥤ᵇ 𝒳.val.val := ⟨y, hy⟩
  let := pointTopology B S hS (schemeSlice B S hS U)
  let := pointTopology B S hS 𝒳.val
  have hΩ' := (continuous_pointsMap B S hS (schemeSlice B S hS U) 𝒳.val F).isOpen_preimage Ω hΩ
  obtain ⟨V, hV, hΩV⟩ := exists_isOpen_mem_iff_schemeSlicePoint_mem U _ hΩ'
  refine ⟨V, hV, fun T => ?_⟩
  rw [← forall_mem_of_hom_iff_range_subset hΩV T]
  exact pointsWithin_obj_iff 𝒳 F Ω T

/-! ### The open substack cut out by an open locus -/

/-- **A full subcategory cut out by open loci is an open substack.** Let `P` be a property of
the objects of an algebraic stack `𝒳` inherited along morphisms, such that along every
scheme-valued point `y` of `𝒳` with values in `U` there is an open subscheme `V ⊆ U` through
which an object `T` of the big fppf site of `U` maps exactly when `P` holds at `y T`. Then `P`
is the property of an open substack of `𝒳`.

The base change of the inclusion along `y` is the category of elements of a subfunctor of
`yoneda U` (`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fullSubcategoryBaseChange`), which
is the open subscheme `V`: both take subsingleton values and have the same support. That gives
representability by algebraic spaces and the open-immersion condition; the full subcategory is
then an algebraic stack by **Stacks 05UM**. -/
theorem exists_openSubstack_property_eq (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj) (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
    (hopen : ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj),
      y ⋙ 𝒳.val.val.p = Over.map U.hom →
        ∃ V : BigFppfOver B U.left.1 U.left.2, _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom ∧
          ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ P (y.obj T)) :
    ∃ W : OpenSubstack 𝒳, W.property = P := by
  have hiso : ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj),
      y ⋙ 𝒳.val.val.p = Over.map U.hom →
        ∃ V : BigFppfOver B U.left.1 U.left.2, _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom ∧
          Nonempty ((fullSubcategoryBaseChangeSubfunctor 𝒳 hP y).toFunctor ≅ yoneda.obj V) := by
    intro U y hy
    obtain ⟨V, hV, hVP⟩ := hopen U y hy
    refine ⟨V, hV, nonempty_iso_of_subsingleton _ _
      (subsingleton_fullSubcategoryBaseChangeSubfunctor 𝒳 hP y)
      (fun T => subsingleton_hom_of_isOpenImmersion B S hS U V hV T.unop) fun T => ?_⟩
    rw [hVP T.unop]
    exact ⟨fun ⟨s⟩ => s.2, fun h => ⟨⟨Over.mkIdTerminal.from T.unop, h⟩⟩⟩
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (fullSubcategoryBasedInclusion 𝒳 P) :=
    isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion 𝒳 hP fun U y hy => by
      obtain ⟨V, -, ⟨e⟩⟩ := hiso U y hy
      exact (isAlgebraicSpace_yoneda B U.left.1 U.left.2 V).of_iso e.symm
  let 𝒳P : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P)
      (isFiberedInGroupoids_fullSubcategoryBased 𝒳 hP)
  let j : 𝒳P ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedInclusion 𝒳 P)
  have halg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P) :=
    isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces.{u, w} B S hS j hrep 𝒳.property
  refine ⟨⟨P, ⟨fun e h => hP e.inv h⟩, halg, hrep, fun U y hy F hF he => ?_⟩, rfl⟩
  obtain ⟨V, hV, ⟨e⟩⟩ := hiso U y hy
  exact isOpenImmersion_algebraicSpaceMap_of_iso_yoneda B S hS U F hF V
    (PresheafOfCategories.isoOfEquivalenceOver he.some
      (nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳 hP y hy).some ≪≫ e) hV

/-- **The open locus of a set of points along a scheme-valued point.** For an open set `Ω` of
points of an algebraic stack `𝒳` and a scheme-valued point `y` of `𝒳` with values in `U`, there
is an open subscheme `V ⊆ U` through which an object `T` of the big fppf site of `U` maps exactly
when every point of `|𝒳|` seen by `y T` lies in `Ω`. -/
theorem exists_isOpenImmersion_pointsWithin_iff (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2, _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ pointsWithin 𝒳 Ω (y.obj T) := by
  obtain ⟨V₀, hV₀, hV₀T⟩ := exists_isOpen_pointsWithin_iff 𝒳 Ω hΩ U y hy
  obtain ⟨V, i, hi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver
    (Over.mk (𝟙 (B.obj U.left.2)) : BigFppfOver B U.left.1 U.left.2) ⟨V₀, hV₀⟩
  have hVhom : V.hom = i.left := by simpa using (Over.w i).symm
  refine ⟨V, by rwa [hVhom], fun T => ?_⟩
  rw [hV₀T T]
  constructor
  · rintro ⟨h⟩
    have hT : T.hom = h.left ≫ V.hom := (Over.w h).symm
    rw [hT, hVhom, B.inclusion.map_comp]
    rintro _ ⟨t, rfl⟩
    have : B.inclusion.map i.left (B.inclusion.map h.left t) ∈
        Set.range ((BigFppfOver.toScheme B U.left.1 U.left.2).map i) := ⟨_, rfl⟩
    rwa [hirange] at this
  · intro hT
    obtain ⟨h, -⟩ := hiuniv (Over.homMk T.hom (by simp) :
      T ⟶ (Over.mk (𝟙 (B.obj U.left.2)) : BigFppfOver B U.left.1 U.left.2)) hT
    exact ⟨h⟩

/-- **The open substack with a prescribed open set of points (Stacks 06FJ, surjectivity).** For
an open set `Ω` of points of an algebraic stack `𝒳`, the objects of `𝒳` every point seen by which
lies in `Ω` form an open substack. -/
theorem exists_openSubstack_property_eq_pointsWithin (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    ∃ W : OpenSubstack 𝒳, W.property = pointsWithin 𝒳 Ω :=
  exists_openSubstack_property_eq 𝒳 (pointsWithin 𝒳 Ω) (fun f => pointsWithin_of_hom 𝒳 Ω f)
    (exists_isOpenImmersion_pointsWithin_iff 𝒳 Ω hΩ)

/-- The open substack of an algebraic stack whose objects are those every point seen by which
lies in a given open set of points. -/
noncomputable def openSubstackOfPoints (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) : OpenSubstack 𝒳 :=
  Classical.choose (exists_openSubstack_property_eq_pointsWithin 𝒳 Ω hΩ)

/-- The objects of `AlgebraicGeometry.Stack.openSubstackOfPoints` are those every point seen by
which lies in the given open set. -/
theorem openSubstackOfPoints_property (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    (openSubstackOfPoints 𝒳 Ω hΩ).property = pointsWithin 𝒳 Ω :=
  Classical.choose_spec (exists_openSubstack_property_eq_pointsWithin 𝒳 Ω hΩ)

/-- **The set of points of `AlgebraicGeometry.Stack.openSubstackOfPoints` is the given open
set.** A point in the open set is represented by a field-valued point whose object sees only
points with the same class. -/
theorem pointSet_openSubstackOfPoints (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) :
    (openSubstackOfPoints 𝒳 Ω hΩ).pointSet B S hS = Ω := by
  ext x
  rw [OpenSubstack.mem_pointSet_iff, openSubstackOfPoints_property]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp p (𝟙 _)
  · intro hx
    obtain ⟨p, rfl⟩ := Quotient.exists_rep x
    refine ⟨p, fun q φ => ?_, rfl⟩
    have hqp : pointClass B S hS 𝒳.val.val 𝒳.val.property q =
        pointClass B S hS 𝒳.val.val 𝒳.val.property p :=
      (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2 ⟨q, ⟨𝟙 _⟩, ⟨φ⟩⟩
    rwa [hqp]

end AlgebraicGeometry.Stack

end
