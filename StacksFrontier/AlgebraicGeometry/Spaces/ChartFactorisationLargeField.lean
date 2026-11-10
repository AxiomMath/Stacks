module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria

/-!
# Enlarging the field of a point so that it factors through a scheme chart

Let `Y` be a presheaf on the big fppf site of `S` with a scheme chart `q : V ⟶ Y` which is
surjective after every represented base change, let `Spec k ⟶ Y` be a point of `Y` with `k` a
field in the site, and let `F` be a presheaf over `Spec k`. Given a point `z` of `F` in the sense
of Stacks 03BU, there are an algebraically closed field `k'` in the site, an extension
`Spec k' ⟶ Spec k`, a section of `F` over `Spec k'` representing `z`, and a factorisation of the
composite `Spec k' ⟶ Y` through the chart `V`.

## Main results

* `AlgebraicGeometry.Space.nonempty_geometricPoint_yoneda`: a nonempty object of the big fppf
  site of `S` carries a geometric point of the presheaf it represents.
* `AlgebraicGeometry.Space.exists_geometricPoint_factorThroughChart_dominates`: every
  field-valued point of `F` is dominated by a geometric point `z'` of `F` whose field spectrum
  maps to `Y` through the chart `V`.
* `AlgebraicGeometry.Space.exists_geometricPoint_factorThroughChart`: every point of `|F|` is the
  image of a geometric point of `F` whose field spectrum maps to `Y` through the chart `V`.
* `AlgebraicGeometry.Space.exists_points_pullback_fst_eq`: a section of `F` over `Spec k'` whose
  image in `Spec k` is `c` gives a point of `F ×_{Spec k} Spec k'` above the point of `F` it
  represents.
* `AlgebraicGeometry.Space.exists_geometricPoint_pullback_fst_eq`: a geometric point of `F` over
  `Spec k'` whose image in `Spec k` is `c` is the image under the first projection of a
  geometric point of `F ×_{Spec k} Spec k'`.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object `U` of the big fppf site with a point `x` of its underlying scheme carries a
geometric point of the presheaf it represents. -/
theorem nonempty_geometricPoint_yoneda (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    Nonempty (GeometricPoint B S hS (yoneda.obj U)) := by
  have hk' : B.Contains (Spec (.of (AlgebraicClosure
      ↥(((BigFppfOver.toScheme B S hS).obj U).residueField x)))) :=
    contains_specAlgebraicClosure B _ (B.residueField_spec_contains U.left.property x)
  exact ⟨⟨siteFieldPointOfSchemeMap B S hS U hk'
      (Spec.map (CommRingCat.ofHom (algebraMap
        ↥(((BigFppfOver.toScheme B S hS).obj U).residueField x)
        (AlgebraicClosure ↥(((BigFppfOver.toScheme B S hS).obj U).residueField x)))) ≫
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x),
    (inferInstance : IsAlgClosed (AlgebraicClosure
      ↥(((BigFppfOver.toScheme B S hS).obj U).residueField x)))⟩⟩

/-- Let `q : V ⟶ Y` be a scheme chart of a presheaf `Y` on the big fppf site of `S` which is
surjective after every represented base change, let `Spec k ⟶ Y` be a point `t` of `Y` with `k` a
field in the site, and let `π : F ⟶ Spec k` be a presheaf over `Spec k`. Then every field-valued
point `p` of `F` is dominated, by `d`, by a geometric point `z'` of `F` whose field spectrum
`Spec k'` carries, besides the structure morphism `c : Spec k' ⟶ Spec k` induced by `π`, a
morphism `ρ : Spec k' ⟶ V` with `ρ ≫ q = c ≫ t`. -/
theorem exists_geometricPoint_factorThroughChart_dominates
    {F Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y)
    (hq : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (t : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ Y)
    (π : F ⟶ yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))
    (p : FieldValuedPoint B S hS F) :
    ∃ (z' : GeometricPoint B S hS F)
      (c : z'.val.siteObject ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS))
      (ρ : z'.val.siteObject ⟶ V)
      (d : z'.val.siteObject ⟶ p.siteObject),
      π.app (Opposite.op z'.val.siteObject) z'.val.value = c ∧
      yoneda.map ρ ≫ q = yoneda.map c ≫ t ∧
      F.map d.op p.value = z'.val.value := by
  classical
  let η : yoneda.obj p.siteObject ⟶ Y := yonedaEquiv.symm p.value ≫ π ≫ t
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map (hq.rep.snd η)) :=
    hq.property_snd η
  have hsq : IsPullback (hq.rep.fst η) (yoneda.map (hq.rep.snd η)) q η := hq.rep.isPullback η
  let x₀ : ↥((BigFppfOver.toScheme B S hS).obj p.siteObject) := by
    change ↥(Spec (CommRingCat.of p.carrier)); exact IsLocalRing.closedPoint p.carrier
  obtain ⟨r, -⟩ := hsurj.surj x₀
  obtain ⟨g⟩ := nonempty_geometricPoint_yoneda B S hS (hq.rep.pullback η) r
  let m : g.val.siteObject ⟶ hq.rep.pullback η := g.val.value
  let w : F.obj (Opposite.op g.val.siteObject) := F.map (m ≫ hq.rep.snd η).op p.value
  let p' : FieldValuedPoint B S hS F :=
    { carrier := g.val.carrier, field := g.val.field, contained := g.val.contained
      toBase := g.val.toBase, value := w }
  let rVsite : hq.rep.pullback η ⟶ V := yoneda.preimage (hq.rep.fst η)
  have hrV : yoneda.map rVsite = hq.rep.fst η := yoneda.map_preimage _
  refine ⟨⟨p', g.property⟩, π.app (Opposite.op g.val.siteObject) w, m ≫ rVsite,
    m ≫ hq.rep.snd η, rfl, ?_, rfl⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
  have hw := congrArg (fun α : yoneda.obj (hq.rep.pullback η) ⟶ Y =>
    α.app (Opposite.op g.val.siteObject) m) hsq.w
  simp only [NatTrans.comp_app, types_comp_apply] at hw
  calc q.app (Opposite.op g.val.siteObject) (m ≫ rVsite)
      = q.app (Opposite.op g.val.siteObject)
          ((hq.rep.fst η).app (Opposite.op g.val.siteObject) m) := by rw [← hrV]; rfl
    _ = η.app (Opposite.op g.val.siteObject) (m ≫ hq.rep.snd η) := hw
    _ = t.app (Opposite.op g.val.siteObject)
          (π.app (Opposite.op g.val.siteObject) w) := rfl

/-- In the situation of
`AlgebraicGeometry.Space.exists_geometricPoint_factorThroughChart_dominates`, every point `z` of
`|F|` is the image of a geometric point `z'` of `F` whose field spectrum `Spec k'` carries, besides
the structure morphism `c : Spec k' ⟶ Spec k` induced by `π`, a morphism `ρ : Spec k' ⟶ V` with
`ρ ≫ q = c ≫ t`. -/
theorem exists_geometricPoint_factorThroughChart
    {F Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y)
    (hq : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (t : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ Y)
    (π : F ⟶ yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))
    (z : points B S hS F) :
    ∃ (z' : GeometricPoint B S hS F)
      (c : z'.val.siteObject ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS))
      (ρ : z'.val.siteObject ⟶ V),
      π.app (Opposite.op z'.val.siteObject) z'.val.value = c ∧
      yoneda.map ρ ≫ q = yoneda.map c ≫ t ∧ z'.image = z := by
  classical
  obtain ⟨p, hp⟩ := Quot.exists_rep z
  obtain ⟨z', c, ρ, d, hc, hρ, hd⟩ := exists_geometricPoint_factorThroughChart_dominates
    B S hS V q hq hk b t π p
  refine ⟨z', c, ρ, hc, hρ, ?_⟩
  rw [← hp]
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
    ⟨z'.val, FieldValuedPoint.dominates_refl B S hS F z'.val, ⟨d, hd⟩⟩

/-- A section `x` of `F` over `U` whose image under `π : F ⟶ T` is `c : U ⟶ T` lifts to a section
of the fibre product `F ×_T U` whose image under the first projection is `x`. -/
private theorem exists_pullback_fst_app_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T U : BigFppfOver B S hS} (π : F ⟶ yoneda.obj T) (x : F.obj (Opposite.op U)) (c : U ⟶ T)
    (hc : π.app (Opposite.op U) x = c) :
    ∃ v : (pullback π (yoneda.map c)).obj (Opposite.op U),
      (pullback.fst π (yoneda.map c)).app (Opposite.op U) v = x := by
  have h : yonedaEquiv.symm x ≫ π = 𝟙 (yoneda.obj U) ≫ yoneda.map c := by
    rw [Category.id_comp]
    apply yonedaEquiv.injective
    rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
  exact ⟨yonedaEquiv (pullback.lift (yonedaEquiv.symm x) (𝟙 _) h), by
    rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]⟩

/-- A field-valued point `p` of `F` whose image under `π : F ⟶ T` is a morphism `c` from its
field spectrum `T'` determines a point of the fibre product `F ×_T T'` lying over the point of
`F` represented by `p`. -/
theorem exists_points_pullback_fst_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (π : F ⟶ yoneda.obj T)
    (p : FieldValuedPoint B S hS F) (c : p.siteObject ⟶ T)
    (hc : π.app (Opposite.op p.siteObject) p.value = c) :
    ∃ w : points B S hS (pullback π (yoneda.map c)),
      pointsMap B S hS (pullback π (yoneda.map c)) (pullback.fst π (yoneda.map c)) w =
        p.class B S hS F := by
  obtain ⟨v, hv⟩ := exists_pullback_fst_app_eq B S hS π p.value c hc
  refine ⟨(⟨p.carrier, p.contained, p.toBase, v⟩ :
      FieldValuedPoint B S hS (pullback π (yoneda.map c))).class B S hS _, ?_⟩
  rw [pointsMap_class]
  exact congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
    FieldValuedPoint B S hS F).class B S hS F) hv

/-- A geometric point `z` of `F` whose image under `π : F ⟶ T` is a morphism `c` from its field
spectrum `T'` determines a geometric point `w` of the fibre product `F ×_T T'`, over the same
field, whose image under the first projection is `z`. -/
theorem exists_geometricPoint_pullback_fst_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver B S hS} (π : F ⟶ yoneda.obj T)
    (z : GeometricPoint B S hS F) (c : z.val.siteObject ⟶ T)
    (hc : π.app (Opposite.op z.val.siteObject) z.val.value = c) :
    ∃ w : GeometricPoint B S hS (pullback π (yoneda.map c)),
      geometricPointMap (pullback.fst π (yoneda.map c)) w = z := by
  classical
  obtain ⟨v, hv⟩ := exists_pullback_fst_app_eq B S hS π z.val.value c hc
  exact ⟨⟨⟨z.val.carrier, z.val.contained, z.val.toBase, v⟩, z.property⟩,
    Subtype.ext (congrArg (fun v => (⟨z.val.carrier, z.val.contained, z.val.toBase, v⟩ :
      FieldValuedPoint B S hS F)) hv)⟩

end AlgebraicGeometry.Space

end
