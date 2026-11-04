module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood

/-!
# The residue-field point of an elementary étale neighborhood

An elementary étale neighborhood `(U, u)` of a point `x` of an algebraic space `X` carries a
field-valued point of `X`, namely the residue field `κ(u)` mapping to `X`, and that field-valued
point represents `x`. A morphism of elementary étale neighborhoods induces a morphism of the
residue-field objects of the big site over the morphism of neighborhoods.

## Main definitions

* `AlgebraicGeometry.Space.neighborhoodFieldPoint` is the field-valued point of `X` attached to
  an elementary étale neighborhood.
* `AlgebraicGeometry.Space.pointedResidueFieldMap` is the morphism of residue-field objects
  induced by a morphism of the big site carrying a chosen point to a chosen point, and
  `AlgebraicGeometry.Space.neighborhoodResidueFieldMap` is its value on a morphism of
  elementary étale neighborhoods.

## Main results

* `AlgebraicGeometry.Space.neighborhoodFieldPoint_class`: the field-valued point attached to an
  elementary étale neighborhood of `x` represents `x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
  (x : points B S hS X)

/-- The field-valued point of the algebraic space carried by an elementary étale
neighborhood: the residue field of its distinguished point, mapping to the space. -/
def neighborhoodFieldPoint (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    FieldValuedPoint B S hS X where
  carrier := U.scheme.left.1.residueField U.point
  contained := U.residueField_contained
  toBase := U.scheme.left.1.fromSpecResidueField U.point ≫ U.scheme.hom.1
  value := yonedaEquiv
    (yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫ U.toSpace)

/-- The morphism into the algebraic space attached to the field-valued point of an elementary
étale neighborhood is the residue-field morphism of the neighborhood. -/
theorem neighborhoodFieldPoint_morphism (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    yonedaEquiv.symm (neighborhoodFieldPoint B S hS X hX x U).value =
      yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫
        U.toSpace :=
  yonedaEquiv.symm_apply_apply _

/-- The field-valued point attached to an elementary étale neighborhood represents the point of
the algebraic space of which it is a neighborhood. -/
theorem neighborhoodFieldPoint_class (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    (neighborhoodFieldPoint B S hS X hX x U).class B S hS X = x := by
  convert U.map_point using 1
  congr 1

/-- The morphism of residue-field points of the big site induced by a morphism of objects of
the site carrying a chosen point to a chosen point. -/
def pointedResidueFieldMap {V W : BigFppfOver B S hS} (f : V ⟶ W)
    (v : V.left.1) (w : W.left.1) (hf : f.left.1 v = w)
    (hv : B.Contains (Spec (.of (V.left.1.residueField v))))
    (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) :
    residueFieldObject B S hS V v hv ⟶ residueFieldObject B S hS W w hw := by
  let rV := residueFieldMap B S hS V v hv
  let rW := residueFieldMap B S hS W w hw
  let φ := Spec.map ((W.left.1.residueFieldCongr hf).inv ≫ f.left.1.residueFieldMap v)
  have hφ : φ ≫ W.left.1.fromSpecResidueField w =
      V.left.1.fromSpecResidueField v ≫ f.left.1 := by
    dsimp [φ]
    rw [Spec.map_comp, Category.assoc]
    simp
  let k₀ : (residueFieldObject B S hS V v hv).left ⟶
      (residueFieldObject B S hS W w hw).left := ⟨φ⟩
  have hleft : k₀ ≫ rW.left = rV.left ≫ f.left := B.inclusion.map_injective hφ
  exact Over.homMk k₀ (by rw [← rW.w, ← Category.assoc, hleft, Category.assoc, f.w, rV.w])

/-- The morphism of residue-field points induced by a pointed morphism lies over that
morphism. -/
theorem pointedResidueFieldMap_comp {V W : BigFppfOver B S hS} (f : V ⟶ W)
    (v : V.left.1) (w : W.left.1) (hf : f.left.1 v = w)
    (hv : B.Contains (Spec (.of (V.left.1.residueField v))))
    (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) :
    pointedResidueFieldMap B S hS f v w hf hv hw ≫ residueFieldMap B S hS W w hw =
      residueFieldMap B S hS V v hv ≫ f := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show Spec.map ((W.left.1.residueFieldCongr hf).inv ≫ f.left.1.residueFieldMap v) ≫
    W.left.1.fromSpecResidueField w = V.left.1.fromSpecResidueField v ≫ f.left.1
  rw [Spec.map_comp, Category.assoc]
  simp

/-- The morphism of residue-field points of the big site induced by a morphism of elementary
étale neighborhoods. -/
def neighborhoodResidueFieldMap {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    residueFieldObject B S hS V.scheme V.point V.residueField_contained ⟶
      residueFieldObject B S hS U.scheme U.point U.residueField_contained :=
  pointedResidueFieldMap B S hS f.hom V.point U.point f.map_point
    V.residueField_contained U.residueField_contained

/-- The morphism of residue-field points induced by a morphism of elementary étale
neighborhoods lies over that morphism. -/
theorem neighborhoodResidueFieldMap_comp
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U) :
    neighborhoodResidueFieldMap B S hS X hX x f ≫
        residueFieldMap B S hS U.scheme U.point U.residueField_contained =
      residueFieldMap B S hS V.scheme V.point V.residueField_contained ≫ f.hom :=
  pointedResidueFieldMap_comp B S hS f.hom V.point U.point f.map_point
    V.residueField_contained U.residueField_contained

end AlgebraicGeometry.Space

end
