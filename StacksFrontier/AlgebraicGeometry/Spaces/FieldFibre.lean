module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The fibre of a morphism of algebraic spaces over a field-valued point

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` and let `p` be a
field-valued point of `Y` in the sense of Tag 03BU, so `p` is a section of `Y` over the
spectrum of a field `k` in the site. There are two fibres attached to this data: the
*set-theoretic fibre* `f^{-1}({y}) ⊂ |X|` over the point `y = p.class` represented by `p`,
and the *field fibre* `X_k = X ×_Y Spec(k)`, an object of the same category as `X` and `Y`.

The comparison map `|X_k| → |X|` has image exactly the set-theoretic fibre. Hence
`f^{-1}({y})` is finite when `|X_k|` is, which is condition (4) ⟹ condition (1) of Tag 0ACK.

## Main definitions

* `AlgebraicGeometry.Space.setFibre` is the set-theoretic fibre `f^{-1}({y}) ⊂ |X|` over the
  point represented by a field-valued point of `Y`.
* `AlgebraicGeometry.Space.fieldFibre` is the field fibre `X ×_Y Spec(k)`.
* `AlgebraicGeometry.Space.FieldValuedPoint.tautological` is the field-valued point of
  `Spec(k)`, viewed as a representable presheaf, given by the identity section.

## Main results

* `AlgebraicGeometry.Space.subsingleton_points_yoneda_siteObject`: the point set of the
  spectrum of a field, viewed as a representable presheaf on the site, is a subsingleton —
  every field-valued point of it is equivalent to the tautological one.
* `AlgebraicGeometry.Space.range_pointsMap_fst_fieldFibre`: the image of `|X_k| → |X|` is
  exactly the set-theoretic fibre.
* `AlgebraicGeometry.Space.finite_setFibre_of_finite_fieldFibre` is Tag 0ACK, condition (4)
  implies condition (1): if `|X_k|` is finite then so is `f^{-1}({y})`.

## References

* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The two fibres -/

/-- The set-theoretic fibre `f^{-1}({y}) ⊂ |X|` of `f : X ⟶ Y` over the point `y` of `|Y|`
represented by a field-valued point `p`. -/
abbrev setFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    Set (points B S hS X) :=
  {x | pointsMap B S hS X f x = p.class B S hS Y}

/-- The field fibre `X_k = X ×_Y Spec(k)` of `f : X ⟶ Y` over a field-valued point `p` of
`Y` with field of definition `k`. -/
noncomputable abbrev fieldFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback f (yonedaEquiv.symm p.value)

/-! ### The point set of the spectrum of a field -/

/-- The tautological field-valued point of `Spec(k)` viewed as a representable presheaf,
where `k` is the field of definition of a field-valued point `p`: it has the same field,
containment witness and structure morphism as `p`, and the identity as its section. -/
noncomputable def FieldValuedPoint.tautological (p : FieldValuedPoint B S hS Y) :
    FieldValuedPoint B S hS (yoneda.obj p.siteObject) where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase
  value := 𝟙 _

/-- Every field-valued point of `Spec(k)`, viewed as a representable presheaf, dominates the
tautological one. -/
theorem FieldValuedPoint.dominates_tautological (p : FieldValuedPoint B S hS Y)
    (r : FieldValuedPoint B S hS (yoneda.obj p.siteObject)) :
    Dominates B S hS (yoneda.obj p.siteObject) r (tautological B S hS p) :=
  ⟨r.value, Category.comp_id r.value⟩

/-- Every field-valued point of `Spec(k)`, viewed as a representable presheaf, represents the
same point as the tautological one. -/
theorem FieldValuedPoint.class_eq_class_tautological (p : FieldValuedPoint B S hS Y)
    (r : FieldValuedPoint B S hS (yoneda.obj p.siteObject)) :
    r.class B S hS _ = (tautological B S hS p).class B S hS _ :=
  class_eq_class_of_hasCommonExtension B S hS _
    ⟨r, dominates_refl B S hS _ r, dominates_tautological B S hS p r⟩

/-- The point set of the spectrum of a field, viewed as a representable presheaf on the site,
is a subsingleton: it is the single point represented by
`AlgebraicGeometry.Space.FieldValuedPoint.tautological`. -/
theorem subsingleton_points_yoneda_siteObject (p : FieldValuedPoint B S hS Y) :
    Subsingleton (points B S hS (yoneda.obj p.siteObject)) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a using Quot.ind with | _ a =>
  induction b using Quot.ind with | _ b =>
  exact (FieldValuedPoint.class_eq_class_tautological B S hS p a).trans
    (FieldValuedPoint.class_eq_class_tautological B S hS p b).symm

/-- The tautological field-valued point of `Spec(k)` is carried to `p` itself by the section
`p`, read as a morphism `Spec(k) ⟶ Y` of presheaves. -/
theorem FieldValuedPoint.map_tautological (p : FieldValuedPoint B S hS Y) :
    map B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value)
      (tautological B S hS p) = p := by
  have hv := yonedaEquiv.apply_symm_apply p.value
  rw [yonedaEquiv_apply] at hv
  cases p with | _ K hK tb v => exact congrArg _ hv

/-- The morphism `Spec(k) ⟶ Y` given by a field-valued point `p` sends the unique point of
`|Spec(k)|` to the point represented by `p`. -/
theorem FieldValuedPoint.pointsMap_class_tautological (p : FieldValuedPoint B S hS Y) :
    pointsMap B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value)
      ((tautological B S hS p).class B S hS _) = p.class B S hS Y := by
  rw [pointsMap_class, map_tautological]

/-- Any point of `|Spec(k)|` is sent to the point represented by `p` by the morphism
`Spec(k) ⟶ Y` given by `p`. -/
theorem FieldValuedPoint.pointsMap_eq_class (p : FieldValuedPoint B S hS Y)
    (z : points B S hS (yoneda.obj p.siteObject)) :
    pointsMap B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value) z =
      p.class B S hS Y := by
  rw [(subsingleton_points_yoneda_siteObject B S hS p).elim z
    ((tautological B S hS p).class B S hS _)]
  exact pointsMap_class_tautological B S hS p

/-- Every point of the representable presheaf on the site object of a field-valued point `p` is
sent by the section of `p` to the point represented by `p`. -/
theorem FieldValuedPoint.pointsMap_class_eq_class (p : FieldValuedPoint B S hS Y)
    (q : FieldValuedPoint B S hS (yoneda.obj p.siteObject)) :
    pointsMap B S hS (yoneda.obj p.siteObject) (yonedaEquiv.symm p.value)
        (q.class B S hS (yoneda.obj p.siteObject)) = p.class B S hS Y :=
  pointsMap_eq_class B S hS p _

/-! ### The comparison map from the field fibre -/

/-- For a morphism `f : X ⟶ Y` of presheaves and a field-valued point `p` of `Y` with field of
definition `k`, the projection `X_k = X ×_Y Spec(k) ⟶ X` has image on points exactly
`f^{-1}({y})`, where `y` is the point represented by `p`. -/
theorem range_pointsMap_fst_fieldFibre (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    Set.range (pointsMap B S hS (fieldFibre B S hS f p)
        (pullback.fst f (yonedaEquiv.symm p.value))) =
      setFibre B S hS f p := by
  have hp := FieldValuedPoint.pointsMap_eq_class B S hS p
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    change pointsMap B S hS X f _ = _
    rw [pointsMap_apply_comm B S hS (pullback.condition (f := f)
      (g := yonedaEquiv.symm p.value)) w]
    exact hp _
  · obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback f (yonedaEquiv.symm p.value)) x
      ((FieldValuedPoint.tautological B S hS p).class B S hS _)
      (hx.trans (hp _).symm)
    exact ⟨w, hw⟩

/-- The comparison map `|X_k| → f^{-1}({y})` is surjective. -/
theorem exists_points_fieldFibre_of_mem_setFibre (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) {x : points B S hS X} (hx : x ∈ setFibre B S hS f p) :
    ∃ w : points B S hS (fieldFibre B S hS f p),
      pointsMap B S hS (fieldFibre B S hS f p)
        (pullback.fst f (yonedaEquiv.symm p.value)) w = x := by
  rwa [← range_pointsMap_fst_fieldFibre B S hS f p] at hx

/-- If the point set of the field fibre `X_k` of a morphism `f : X ⟶ Y` of algebraic spaces is
finite, then the set-theoretic fibre `f^{-1}({y}) ⊂ |X|` is finite. -/
@[stacks 0ACK "condition (4) implies condition (1)"]
theorem finite_setFibre_of_finite_fieldFibre
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hfinite : (Set.univ : Set (points B S hS (fieldFibre B S hS f p))).Finite) :
    (setFibre B S hS f p).Finite := by
  rw [← range_pointsMap_fst_fieldFibre B S hS f p, ← Set.image_univ]
  exact hfinite.image _

end AlgebraicGeometry.Space

end
