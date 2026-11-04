module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints

/-!
# Every point of a presheaf on the big fppf site has a geometric representative

A point of a presheaf on the big fppf site over `S` is an equivalence class of field-valued points,
and it is always represented by one whose field is algebraically closed, that is by a geometric
point.

## Main definitions

* `AlgebraicGeometry.Space.canonicalGeometricPoint`: a chosen geometric point over a given point.

## Main results

* `AlgebraicGeometry.Space.exists_geometricRepresentative`: every point of a presheaf on the big
  fppf site over `S` is the image point of a geometric point.

## References

* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-- As `k` ranges over all algebraically closed fields over `S` the geometric points `ȳ ∈ G(k)`
cover all of `|G|`: a point of a presheaf on the big fppf site over `S`, that is an equivalence
class of field-valued points, is the image point of a geometric point. -/
theorem exists_geometricRepresentative
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (y : points B S hS G) :
    ∃ p : GeometricPoint B S hS G, p.image = y := by
  classical
  obtain ⟨p₀, hp₀⟩ := Quot.exists_rep y
  let K := AlgebraicClosure p₀.carrier
  have hKsite : B.Contains (Spec (.of K)) := by
    have hk : (Spec (.of p₀.carrier)).size < B.cutoff := p₀.contained
    rw [Scheme.size_Spec] at hk
    show (Spec (.of K)).size < B.cutoff
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff ((Algebra.IsAlgebraic.cardinalMk_le_max p₀.carrier K).trans_lt
      (max_lt ((le_max_right _ _).trans_lt hk) B.aleph0_lt_cutoff))
  let a : p₀.carrier →+* K := algebraMap p₀.carrier K
  let g : Spec (.of K) ⟶ Spec (.of p₀.carrier) :=
    Scheme.Spec.map (CommRingCat.ofHom a).op
  let b : Spec (.of K) ⟶ S := g ≫ p₀.toBase
  let e : B.obj hKsite ⟶ B.obj p₀.contained := B.inclusion.preimage
    (show B.inclusion.obj (B.obj hKsite) ⟶ B.inclusion.obj (B.obj p₀.contained) from g)
  let eOver : Over.mk (⟨b⟩ : B.obj hKsite ⟶ B.obj hS) ⟶ p₀.siteObject :=
    Over.homMk e (by
      apply B.inclusion.map_injective
      show B.inclusion.map e ≫ B.inclusion.map p₀.siteObject.hom = b
      rw [Functor.map_preimage]
      simp [FieldValuedPoint.siteObject, b])
  let q : FieldValuedPoint B S hS G :=
    { carrier := K
      contained := hKsite
      toBase := b
      value := G.map eOver.op p₀.value }
  exact ⟨⟨q, inferInstance⟩, (FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G
    ⟨q, FieldValuedPoint.dominates_refl B S hS G q, ⟨eOver, rfl⟩⟩).trans hp₀⟩

open Classical in
/-- A canonical choice of geometric representative of a point of a presheaf on the big fppf site
over `S`, obtained from `exists_geometricRepresentative` by choice. -/
noncomputable def canonicalGeometricPoint
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : points B S hS G) :
    GeometricPoint B S hS G :=
  (exists_geometricRepresentative B S hS G p).choose

/-- The canonical geometric representative of a point `p` lies over `p`. -/
@[simp]
theorem canonicalGeometricPoint_image
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : points B S hS G) :
    (canonicalGeometricPoint B S hS G p).image = p :=
  (exists_geometricRepresentative B S hS G p).choose_spec

end AlgebraicGeometry.Space

end
