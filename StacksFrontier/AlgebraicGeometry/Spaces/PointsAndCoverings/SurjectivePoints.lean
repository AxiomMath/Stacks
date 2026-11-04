module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints

/-!
# Surjective morphisms of presheaves are surjective on points

A morphism of presheaves on the big fppf site of `S` out of a representable presheaf which is
surjective after every representable base change induces a surjection on points. For a
morphism between representable presheaves this is the statement that a surjective morphism of
schemes in the site is surjective on the points of the presheaves they represent.

## Main results

* `AlgebraicGeometry.Space.surjective_pointsMap_yoneda_map`: a surjective morphism of schemes
  in the big fppf site of `S` induces a surjection on the points of the represented presheaves.
* `AlgebraicGeometry.Space.surjective_pointsMap_of_presheaf_surjective`: a morphism out of a
  representable presheaf which is surjective after every representable base change induces a
  surjection on points.

## Implementation notes

Only the implication from relative surjectivity to surjectivity on points is established here.
The converse rests on the description of the points of a cartesian square of algebraic spaces
and is not used by either statement.

Neither statement uses the algebraic-space axioms. The second needs only representability of
the morphism, which is part of `CategoryTheory.MorphismProperty.presheaf`; so it applies to an
arbitrary presheaf as target.

A point of a representable presheaf is represented by a morphism of schemes from the spectrum
of a field in the site, so lifting it along `σ : U ⟶ V` means producing a point of the fibre
product of that field spectrum with the scheme underlying `U`. Surjectivity makes the fibre
product nonempty, its size lies below the site's cutoff by Stacks 000R (1), and the residue
field at any of its points therefore gives a field in the site through which the lift
factors.

For a general target the morphism is first base changed along the morphism out of a field
spectrum which classifies the given point; the base change is representable, so the
representable case applies to it, and the resulting point of the base change is pushed forward
along the projection.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A field-valued point of the presheaf represented by `U`, compatible along `σ : U ⟶ V` with
a given field-valued point of the presheaf represented by `V`, is sent by `|σ|` to the point
that the latter represents. -/
theorem pointsMap_yoneda_map_siteFieldPointOfSchemeMap {U V : BigFppfOver B S hS} (σ : U ⟶ V)
    (q : FieldValuedPoint B S hS (yoneda.obj V))
    {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (ρ : Spec (.of K) ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (c : Spec (.of K) ⟶ Spec (.of q.carrier))
    (hc : c ≫ B.inclusion.map q.value.left = ρ ≫ (BigFppfOver.toScheme B S hS).map σ) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map σ)
        ((siteFieldPointOfSchemeMap B S hS U hK ρ).class B S hS (yoneda.obj U)) =
      q.class B S hS (yoneda.obj V) := by
  rw [pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj V)
    ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj V) _,
      dominates_of_scheme_map B S hS V _ q c ?_⟩
  have hval : B.inclusion.map (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map σ)
        (siteFieldPointOfSchemeMap B S hS U hK ρ)).value.left =
      B.inclusion.map (siteFieldPointOfSchemeMap B S hS U hK ρ).value.left ≫
        (BigFppfOver.toScheme B S hS).map σ :=
    B.inclusion.map_comp _ _
  rw [hval, map_siteFieldPointOfSchemeMap_value_left]
  exact hc

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is surjective
induces a surjection on the points of the represented presheaves. -/
theorem surjective_pointsMap_yoneda_map {U V : BigFppfOver B S hS} (σ : U ⟶ V)
    (hσ : Surjective ((BigFppfOver.toScheme B S hS).map σ)) :
    Function.Surjective (pointsMap B S hS (yoneda.obj U) (yoneda.map σ)) := by
  classical
  intro y
  induction y using Quot.ind with | _ q => ?_
  have hfst : Surjective (pullback.fst (B.inclusion.map q.value.left)
      ((BigFppfOver.toScheme B S hS).map σ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective.{u})
      (IsPullback.of_hasPullback _ _).flip hσ
  obtain ⟨w, -⟩ := hfst.surj (Classical.arbitrary (Spec (CommRingCat.of q.carrier)))
  have hW : B.Contains (pullback (B.inclusion.map q.value.left)
      ((BigFppfOver.toScheme B S hS).map σ)) :=
    Scheme.size_pullback_lt _ _ q.contained U.left.property
  have hc : (Scheme.fromSpecResidueField _ w ≫ pullback.fst (B.inclusion.map q.value.left)
        ((BigFppfOver.toScheme B S hS).map σ)) ≫ B.inclusion.map q.value.left =
      (Scheme.fromSpecResidueField _ w ≫ pullback.snd (B.inclusion.map q.value.left)
        ((BigFppfOver.toScheme B S hS).map σ)) ≫ (BigFppfOver.toScheme B S hS).map σ := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  exact ⟨_, pointsMap_yoneda_map_siteFieldPointOfSchemeMap B S hS σ q
    (B.residueField_spec_contains hW w) _ _ hc⟩

/-- A point of a presheaf lying in the image of a morphism out of a representable presheaf
which is surjective after a prescribed representable base change is in the image of the
induced map on points. -/
private theorem exists_pointsMap_eq_of_isPullback
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    (f : yoneda.obj T ⟶ F) (q : FieldValuedPoint B S hS F)
    (P : BigFppfOver B S hS) (a : yoneda.obj P ⟶ yoneda.obj T)
    (b : P ⟶ FieldValuedPoint.siteObject B S hS F q)
    (hsq : IsPullback a (yoneda.map b) f (yonedaEquiv.symm q.value))
    (hb : Surjective ((BigFppfOver.toScheme B S hS).map b)) :
    ∃ z, pointsMap B S hS (yoneda.obj T) f z = q.class B S hS F := by
  classical
  obtain ⟨w, -⟩ := hb.surj (Classical.arbitrary (Spec (CommRingCat.of q.carrier)))
  refine ⟨pointsMap B S hS (yoneda.obj P) a
    ((canonicalSiteFieldPoint B S hS P w).class B S hS (yoneda.obj P)), ?_⟩
  have h1 : pointsMap B S hS (yoneda.obj T) f
        (pointsMap B S hS (yoneda.obj P) a
          ((canonicalSiteFieldPoint B S hS P w).class B S hS (yoneda.obj P))) =
      pointsMap B S hS (yoneda.obj P) (a ≫ f)
        ((canonicalSiteFieldPoint B S hS P w).class B S hS (yoneda.obj P)) :=
    (congrFun (pointsMap_comp B S hS (yoneda.obj P) a f) _).symm
  have h2 : pointsMap B S hS (yoneda.obj P) (yoneda.map b ≫ yonedaEquiv.symm q.value)
        ((canonicalSiteFieldPoint B S hS P w).class B S hS (yoneda.obj P)) =
      pointsMap B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS F q))
        (yonedaEquiv.symm q.value)
        (pointsMap B S hS (yoneda.obj P) (yoneda.map b)
          ((canonicalSiteFieldPoint B S hS P w).class B S hS (yoneda.obj P))) :=
    congrFun (pointsMap_comp B S hS (yoneda.obj P) (yoneda.map b)
      (yonedaEquiv.symm q.value)) _
  rw [h1, hsq.w, h2, pointsMap_class, pointsMap_class]
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
    ⟨_, FieldValuedPoint.dominates_refl B S hS F _,
      ⟨(canonicalSiteFieldPoint B S hS P w).value ≫ b, rfl⟩⟩

/-- A morphism out of a representable presheaf on the big fppf site of `S` which is surjective
after every representable base change induces a surjection on points. -/
theorem surjective_pointsMap_of_presheaf_surjective
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ F)
    (hf : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    Function.Surjective (pointsMap B S hS (yoneda.obj T) f) := by
  classical
  intro y
  induction y using Quot.ind with | _ q => ?_
  exact exists_pointsMap_eq_of_isPullback B S hS f q _
    (hf.rep.fst (yonedaEquiv.symm q.value)) (hf.rep.snd (yonedaEquiv.symm q.value))
    (hf.rep.isPullback (yonedaEquiv.symm q.value))
    (hf.property_snd (yonedaEquiv.symm q.value))

end AlgebraicGeometry.Space

end
