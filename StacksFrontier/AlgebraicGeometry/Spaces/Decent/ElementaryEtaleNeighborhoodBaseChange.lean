module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Base change of an elementary étale neighborhood along a morphism of spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `x` be a point of `X` and let
`V` be an elementary étale neighborhood of the image of `x` in `Y`. The fibre product
`V ×_Y X` is an algebraic space, its projection to `X` is étale, and — as soon as `X` is
decent — it carries exactly one point lying above both `x` and the distinguished point of `V`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_point_over_elementaryEtaleNeighborhood`: the unique
  point of the fibre product above the two distinguished points.

Algebraicity of the fibre product is `AlgebraicGeometry.isAlgebraicSpace_pullback` and
étaleness of its projection to `X` is `AlgebraicGeometry.Space.isEtale_of_isPullback`, both of
which hold for any morphism of algebraic spaces.

## References

* [Stacks Project, Tag 0EPL](https://stacks.math.columbia.edu/tag/0EPL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 0EPL "the fibre product is an algebraic space"
  AlgebraicGeometry.isAlgebraicSpace_pullback
add_to_stacks 0EPL "the projection to the source is étale"
  AlgebraicGeometry.Space.isEtale_of_isPullback

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` with `X` decent, let `x` be a point
of `X` and let `V` be an elementary étale neighborhood of the image of `x`. The fibre product
`V ×_Y X` has exactly one point lying above the distinguished point of `V` and above `x`. -/
@[stacks 0EPL "the unique point above the two distinguished points"]
theorem existsUnique_point_over_elementaryEtaleNeighborhood
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hX : IsDecentSpace B S hS X.1)
    (x : points B S hS X.1)
    (V : ElementaryEtaleNeighborhood B S hS Y.1 Y.property
      (pointsMap B S hS X.1 f.hom x)) :
    ∃! x' : points B S hS (pullback V.toSpace f.hom),
      pointsMap B S hS (pullback V.toSpace f.hom) (pullback.fst V.toSpace f.hom) x' =
          presheafPoint B S hS V.scheme V.point V.residueField_contained ∧
        pointsMap B S hS (pullback V.toSpace f.hom) (pullback.snd V.toSpace f.hom) x' = x := by
  classical
  let q0 : FieldValuedPoint B S hS (yoneda.obj V.scheme) :=
    { carrier := V.scheme.left.1.residueField V.point
      contained := V.residueField_contained
      toBase := V.scheme.left.1.fromSpecResidueField V.point ≫ V.scheme.hom.1
      value := residueFieldMap B S hS V.scheme V.point V.residueField_contained }
  let q0V : q0.siteObject B S hS (yoneda.obj V.scheme) ⟶ V.scheme :=
    residueFieldMap B S hS V.scheme V.point V.residueField_contained
  let qY : FieldValuedPoint B S hS Y.1 :=
    { carrier := q0.carrier
      field := q0.field
      contained := q0.contained
      toBase := q0.toBase
      value := V.toSpace.app (Opposite.op q0.siteObject) q0.value }
  have hq0val : q0.value = yonedaEquiv (yoneda.map q0V) := by
    simpa only [q0, q0V] using (yonedaEquiv_yoneda_map q0V).symm
  have hqYarrow : yonedaEquiv.symm qY.value = yoneda.map q0V ≫ V.toSpace := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, ← hq0val]
    rfl
  have hqYmono : Mono (yonedaEquiv.symm qY.value) := by
    rw [hqYarrow]; exact V.mono_residueField
  obtain ⟨p, hpclass, hpmono⟩ :=
    IsDecentSpace.hasMonomorphicFieldRepresentative B S hS X.1 hX x
  have : Mono (yonedaEquiv.symm p.value) := hpmono
  let pY : FieldValuedPoint B S hS Y.1 :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := f.hom.app (Opposite.op p.siteObject) p.value }
  have hq0class : q0.class B S hS (yoneda.obj V.scheme) =
    presheafPoint B S hS V.scheme V.point V.residueField_contained := rfl
  have hpYqY : qY.class B S hS Y.1 = pY.class B S hS Y.1 := by
    change pointsMap B S hS (yoneda.obj V.scheme) V.toSpace
        (q0.class B S hS (yoneda.obj V.scheme)) =
      pointsMap B S hS X.1 f.hom (p.class B S hS X.1)
    rw [hq0class, V.map_point, ← hpclass]
  obtain ⟨e, he⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
    B S hS Y.1 Y.property qY pY hpYqY
  let e0 : p.siteObject B S hS X.1 ⟶ q0.siteObject B S hS (yoneda.obj V.scheme) := by
    change pY.siteObject B S hS Y.1 ⟶ qY.siteObject B S hS Y.1; exact e
  let eV := e0 ≫ q0V
  let gV : yoneda.obj (p.siteObject B S hS X.1) ⟶ yoneda.obj V.scheme := yoneda.map eV
  let gX : yoneda.obj (p.siteObject B S hS X.1) ⟶ X.1 := yonedaEquiv.symm p.value
  have hcompat : gV ≫ V.toSpace = gX ≫ f.hom := by
    calc gV ≫ V.toSpace = yoneda.map e0 ≫ yoneda.map q0V ≫ V.toSpace := by
          change yoneda.map (e0 ≫ q0V) ≫ V.toSpace = _
          rw [yoneda.map_comp, Category.assoc]
      _ = yoneda.map e ≫ yonedaEquiv.symm qY.value := by rw [← hqYarrow]; rfl
      _ = yonedaEquiv.symm pY.value := by
          apply yonedaEquiv.injective
          rw [← yonedaEquiv_naturality (yonedaEquiv.symm qY.value) e]
          simpa using he.1
      _ = yonedaEquiv.symm p.value ≫ f.hom := by
          simpa [pY] using
            (yonedaEquiv_symm_naturality_right p.siteObject f.hom p.value).symm
      _ = gX ≫ f.hom := rfl
  let l : yoneda.obj (p.siteObject B S hS X.1) ⟶ pullback V.toSpace f.hom :=
    pullback.lift gV gX hcompat
  let t : FieldValuedPoint B S hS (pullback V.toSpace f.hom) :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := yonedaEquiv l }
  refine ⟨t.class B S hS _, ⟨?_, ?_⟩, ?_⟩
  · let tV : FieldValuedPoint B S hS (yoneda.obj V.scheme) :=
      FieldValuedPoint.map B S hS (pullback V.toSpace f.hom) (pullback.fst V.toSpace f.hom) t
    change tV.class B S hS (yoneda.obj V.scheme) = q0.class B S hS _
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
      ⟨tV, FieldValuedPoint.dominates_refl B S hS _ tV, e0, ?_⟩
    have htVval : (yoneda.obj V.scheme).map e0.op q0.value = tV.value := by
      rw [hq0val]
      have hArrow : yoneda.map e0 ≫ yoneda.map q0V = l ≫ pullback.fst V.toSpace f.hom := by
        dsimp [l, gV, eV]
        rw [pullback.lift_fst, ← yoneda.map_comp]
      rw [yonedaEquiv_naturality, hArrow]
      simpa [tV, t, FieldValuedPoint.map, FieldValuedPoint.siteObject] using
        yonedaEquiv_comp l (pullback.fst V.toSpace f.hom)
    exact htVval
  · let tX : FieldValuedPoint B S hS X.1 :=
      { carrier := p.carrier
        field := p.field
        contained := p.contained
        toBase := p.toBase
        value := (pullback.snd V.toSpace f.hom).app (Opposite.op p.siteObject) (yonedaEquiv l) }
    have hmap : FieldValuedPoint.map B S hS (pullback V.toSpace f.hom)
        (pullback.snd V.toSpace f.hom) t = tX := rfl
    have htXval : tX.value = p.value := by
      change (pullback.snd V.toSpace f.hom).app (Opposite.op p.siteObject) (yonedaEquiv l) =
        p.value
      rw [← yonedaEquiv_comp l (pullback.snd V.toSpace f.hom), pullback.lift_snd]
      simp [gX]
    have htXclass : tX.class B S hS X.1 = p.class B S hS X.1 := by
      refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS X.1
        ⟨p, ⟨𝟙 (p.siteObject B S hS X.1), ?_⟩,
          FieldValuedPoint.dominates_refl B S hS X.1 p⟩
      rw [htXval]
      exact Functor.map_id_apply X.1 (Opposite.op (p.siteObject B S hS X.1)) p.value
    change pointsMap B S hS (pullback V.toSpace f.hom) (pullback.snd V.toSpace f.hom)
      (t.class B S hS _) = x
    rw [pointsMap_class, hmap]
    exact htXclass.trans hpclass
  · intro z hz
    obtain ⟨q, rfl⟩ := Quot.exists_rep z
    let qV : FieldValuedPoint B S hS (yoneda.obj V.scheme) :=
      { carrier := q.carrier
        field := q.field
        contained := q.contained
        toBase := q.toBase
        value := (pullback.fst V.toSpace f.hom).app (Opposite.op q.siteObject) q.value }
    let qX : FieldValuedPoint B S hS X.1 :=
      { carrier := q.carrier
        field := q.field
        contained := q.contained
        toBase := q.toBase
        value := (pullback.snd V.toSpace f.hom).app (Opposite.op q.siteObject) q.value }
    have hqVmap : qV = FieldValuedPoint.map B S hS (pullback V.toSpace f.hom)
      (pullback.fst V.toSpace f.hom) q := rfl
    have hqXmap : qX = FieldValuedPoint.map B S hS (pullback V.toSpace f.hom)
      (pullback.snd V.toSpace f.hom) q := rfl
    have hqVclass : qV.class B S hS (yoneda.obj V.scheme) =
        q0.class B S hS (yoneda.obj V.scheme) := by
      rw [hqVmap, ← pointsMap_class, hz.1, ← hq0class]
    have hqXclass : qX.class B S hS X.1 = p.class B S hS X.1 := by
      rw [hqXmap, ← pointsMap_class]
      exact hz.2.trans hpclass.symm
    have hq0mono' : Mono (yoneda.map q0V) := by
      have : Mono (yoneda.map q0V ≫ V.toSpace) := by rw [← hqYarrow]; exact hqYmono
      exact mono_of_mono _ V.toSpace
    have hq0mono : Mono (yonedaEquiv.symm q0.value) := by
      rw [hq0val]
      simpa only [Equiv.symm_apply_apply] using hq0mono'
    obtain ⟨b, hb, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
      B S hS (yoneda.obj V.scheme) (isAlgebraicSpace_yoneda B S hS V.scheme) q0 qV
      hqVclass.symm
    obtain ⟨a, ha, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
      B S hS X.1 X.property p qX hqXclass.symm
    have hqpair : V.toSpace.app (Opposite.op q.siteObject) qV.value =
        f.hom.app (Opposite.op q.siteObject) qX.value := by
      simpa [qV, qX, FieldValuedPoint.map, FieldValuedPoint.siteObject, types_comp_apply] using
        congrArg (fun k : pullback V.toSpace f.hom ⟶ Y.1 ↦
          k.app (Opposite.op q.siteObject) q.value)
          (pullback.condition (f := V.toSpace) (g := f.hom))
    have hby : Y.1.map b.op qY.value = Y.1.map (a ≫ e0).op qY.value := by
      calc Y.1.map b.op qY.value =
            V.toSpace.app (Opposite.op qV.siteObject)
              ((yoneda.obj V.scheme).map b.op q0.value) := by
            simpa [qY] using (V.toSpace.naturality_apply b.op q0.value).symm
        _ = V.toSpace.app (Opposite.op qV.siteObject) qV.value :=
            congrArg (V.toSpace.app (Opposite.op qV.siteObject)) hb
        _ = f.hom.app (Opposite.op qX.siteObject) qX.value := hqpair
        _ = f.hom.app (Opposite.op qX.siteObject) (X.1.map a.op p.value) := congrArg _ ha.symm
        _ = Y.1.map a.op pY.value := by simp [pY]
        _ = Y.1.map a.op (Y.1.map e0.op qY.value) :=
            congrArg (Y.1.map a.op) (by simpa [e0] using he.1.symm)
        _ = Y.1.map (a ≫ e0).op qY.value := by
            simp only [CategoryTheory.op_comp, Functor.map_comp, types_comp_apply]
    have hbyArrow : yoneda.map b ≫ yonedaEquiv.symm qY.value =
        yoneda.map (a ≫ e0) ≫ yonedaEquiv.symm qY.value := by
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
      exact hby
    have hab : b = a ≫ e0 :=
      yoneda.map_injective ((cancel_mono (yonedaEquiv.symm qY.value)).mp hbyArrow)
    have hbArrow : yonedaEquiv.symm qV.value = yoneda.map b ≫ yonedaEquiv.symm q0.value := by
      simpa only [hb] using
        (yonedaEquiv_symm_naturality_left b (yoneda.obj V.scheme) q0.value).symm
    have haArrow : yonedaEquiv.symm qX.value = yoneda.map a ≫ yonedaEquiv.symm p.value := by
      simpa only [ha] using (yonedaEquiv_symm_naturality_left a X.1 p.value).symm
    have hfst : yonedaEquiv.symm q.value ≫ pullback.fst V.toSpace f.hom =
        yoneda.map a ≫ gV := by
      calc yonedaEquiv.symm q.value ≫ pullback.fst V.toSpace f.hom =
            yonedaEquiv.symm qV.value :=
            yonedaEquiv_symm_naturality_right q.siteObject (pullback.fst V.toSpace f.hom) q.value
        _ = yoneda.map b ≫ yonedaEquiv.symm q0.value := hbArrow
        _ = yoneda.map a ≫ gV := by
            rw [hab, hq0val]
            dsimp [gV, eV]
            simp [yoneda.map_comp, Category.assoc]
    have hsnd : yonedaEquiv.symm q.value ≫ pullback.snd V.toSpace f.hom =
        yoneda.map a ≫ gX :=
      (yonedaEquiv_symm_naturality_right q.siteObject (pullback.snd V.toSpace f.hom)
        q.value).trans haArrow
    have hqArrow : yonedaEquiv.symm q.value = yoneda.map a ≫ l := by
      refine pullback.hom_ext ?_ ?_
      · simpa only [l, Category.assoc, pullback.lift_fst] using hfst
      · simpa only [l, Category.assoc, pullback.lift_snd] using hsnd
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
      ⟨q, FieldValuedPoint.dominates_refl B S hS _ q, a, ?_⟩
    calc (pullback V.toSpace f.hom).map a.op t.value = yonedaEquiv (yoneda.map a ≫ l) := by
          change (pullback V.toSpace f.hom).map a.op (yonedaEquiv l) = _
          exact yonedaEquiv_naturality l a
      _ = yonedaEquiv (yonedaEquiv.symm q.value) := congrArg yonedaEquiv hqArrow.symm
      _ = q.value := Equiv.apply_symm_apply yonedaEquiv q.value

end AlgebraicGeometry.Space

end
