module

public import StacksFrontier.Algebra.Homology.DoubleMappingCone

/-!
# The projection of a two-term complex onto its shifted degree `i₀` term is natural

A two-term complex `HomologicalComplex.double f`, with `f : X₀ ⟶ X₁` in degrees `i₀` and
`i₁ = i₀ + 1`, sits in the distinguished triangle

`X₀[i₁] ⟶ X₁[i₁] ⟶ double f ⟶ (X₀[i₁])⟦1⟧`

of `CochainComplex.doubleTriangleQ_distinguished`, whose third map is
`CochainComplex.doubleProjQ`. This file proves that this third map is *natural*: a morphism of
cochain complexes `double f ⟶ double g` whose two nonzero components are `p : X₀ ⟶ Y₀` and
`q : X₁ ⟶ Y₁` commutes with the two projections, up to `p` on the shifted degree `i₀` terms.

## Main results

* `CochainComplex.double_hom_comm`: the two components of a morphism of two-term complexes
  commute with the two differentials.
* `CochainComplex.doubleToMappingCone_naturality`: the identification of a two-term complex with
  the mapping cone of its differential is natural.
* `CochainComplex.doubleProjQ_naturality`: the projection onto the shifted degree `i₀` term is
  natural.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated HomologicalComplex

universe w v u

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) {i₀ i₁ : ℤ}
  (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁) (h : i₀ ≠ i₁) (p : X₀ ⟶ Y₀) (q : X₁ ⟶ Y₁)

omit [HasBinaryBiproducts C] in
/-- **The two components of a morphism of two-term complexes commute with the differentials.**
If a morphism `double f ⟶ double g` has components `p : X₀ ⟶ Y₀` and `q : X₁ ⟶ Y₁` in degrees
`i₀` and `i₁`, then `f ≫ q = p ≫ g`. -/
theorem double_hom_comm (φ : double f hi₀₁ ⟶ double g hi₀₁)
    (hφ₀ : φ.f i₀ = (doubleXIso₀ f hi₀₁).hom ≫ p ≫ (doubleXIso₀ g hi₀₁).inv)
    (hφ₁ : φ.f i₁ = (doubleXIso₁ f hi₀₁ h).hom ≫ q ≫ (doubleXIso₁ g hi₀₁ h).inv) :
    f ≫ q = p ≫ g := by
  have hc := φ.comm i₀ i₁
  rw [double_d f hi₀₁ h, double_d g hi₀₁ h, hφ₀, hφ₁] at hc
  simpa using hc.symm

/-- **The identification of a two-term complex with the mapping cone of its differential is
natural.** The square relating `CochainComplex.doubleToMappingCone` for `f` and for `g`, the
morphism of two-term complexes with components `p` and `q`, and the morphism of mapping cones
induced by the same square of single complexes, commutes. -/
theorem doubleToMappingCone_naturality
    (comm : (single C (ComplexShape.up ℤ) i₁).map f ≫ (single C (ComplexShape.up ℤ) i₁).map q =
      (single C (ComplexShape.up ℤ) i₁).map p ≫ (single C (ComplexShape.up ℤ) i₁).map g)
    (φ : double f hi₀₁ ⟶ double g hi₀₁)
    (hφ₀ : φ.f i₀ = (doubleXIso₀ f hi₀₁).hom ≫ p ≫ (doubleXIso₀ g hi₀₁).inv)
    (hφ₁ : φ.f i₁ = (doubleXIso₁ f hi₀₁ h).hom ≫ q ≫ (doubleXIso₁ g hi₀₁ h).inv) :
    doubleToMappingCone f hi₀₁ ≫
        mappingCone.map ((single C (ComplexShape.up ℤ) i₁).map f)
          ((single C (ComplexShape.up ℤ) i₁).map g)
          ((single C (ComplexShape.up ℤ) i₁).map p)
          ((single C (ComplexShape.up ℤ) i₁).map q) comm =
      φ ≫ doubleToMappingCone g hi₀₁ := by
  refine from_double_hom_ext ?_ ?_ <;> rw [comp_f, comp_f]
  · rw [hφ₀]
    simp [doubleToMappingCone, mappingCone.map, single_map_f_self]
  · rw [hφ₁]
    simp [doubleToMappingCone, mappingCone.map, single_map_f_self]

end

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) {i₀ i₁ : ℤ}
  (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁) (h : i₀ ≠ i₁) (p : X₀ ⟶ Y₀) (q : X₁ ⟶ Y₁)

/-- **The projection of a two-term complex onto the shift of its degree `i₀` term is natural.**
A morphism `double f ⟶ double g` of two-term complexes with components `p : X₀ ⟶ Y₀` and
`q : X₁ ⟶ Y₁` carries the projection of `double g` back to the projection of `double f`
followed by the shift of `p`. -/
theorem doubleProjQ_naturality (φ : double f hi₀₁ ⟶ double g hi₀₁)
    (hφ₀ : φ.f i₀ = (doubleXIso₀ f hi₀₁).hom ≫ p ≫ (doubleXIso₀ g hi₀₁).inv)
    (hφ₁ : φ.f i₁ = (doubleXIso₁ f hi₀₁ h).hom ≫ q ≫ (doubleXIso₁ g hi₀₁ h).inv) :
    DerivedCategory.Q.map φ ≫ doubleProjQ g hi₀₁ =
      doubleProjQ f hi₀₁ ≫ ((DerivedCategory.singleFunctor C i₁).map p)⟦(1 : ℤ)⟧' := by
  have comm : (single C (ComplexShape.up ℤ) i₁).map f ≫
      (single C (ComplexShape.up ℤ) i₁).map q =
      (single C (ComplexShape.up ℤ) i₁).map p ≫ (single C (ComplexShape.up ℤ) i₁).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, double_hom_comm f g hi₀₁ h p q φ hφ₀ hφ₁]
  have hsq : DerivedCategory.Q.map (doubleToMappingCone f hi₀₁) ≫
      DerivedCategory.Q.map (mappingCone.map ((single C (ComplexShape.up ℤ) i₁).map f)
        ((single C (ComplexShape.up ℤ) i₁).map g) ((single C (ComplexShape.up ℤ) i₁).map p)
        ((single C (ComplexShape.up ℤ) i₁).map q) comm) =
      DerivedCategory.Q.map φ ≫ DerivedCategory.Q.map (doubleToMappingCone g hi₀₁) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      doubleToMappingCone_naturality f g hi₀₁ h p q comm φ hφ₀ hφ₁]
  have htri : DerivedCategory.Q.map (mappingCone.map
          ((single C (ComplexShape.up ℤ) i₁).map f) ((single C (ComplexShape.up ℤ) i₁).map g)
          ((single C (ComplexShape.up ℤ) i₁).map p)
          ((single C (ComplexShape.up ℤ) i₁).map q) comm) ≫
        (DerivedCategory.Q.mapTriangle.obj
          (mappingCone.triangle ((single C (ComplexShape.up ℤ) i₁).map g))).mor₃ =
      (DerivedCategory.Q.mapTriangle.obj
          (mappingCone.triangle ((single C (ComplexShape.up ℤ) i₁).map f))).mor₃ ≫
        ((DerivedCategory.singleFunctor C i₁).map p)⟦(1 : ℤ)⟧' :=
    ((DerivedCategory.Q.mapTriangle.map
      (mappingCone.triangleMap ((single C (ComplexShape.up ℤ) i₁).map f)
        ((single C (ComplexShape.up ℤ) i₁).map g) ((single C (ComplexShape.up ℤ) i₁).map p)
        ((single C (ComplexShape.up ℤ) i₁).map q) comm)).comm₃).symm
  have ef : (DerivedCategory.Q.mapIso (doubleIsoMappingCone f hi₀₁)).hom =
      DerivedCategory.Q.map (doubleToMappingCone f hi₀₁) := rfl
  have eg : (DerivedCategory.Q.mapIso (doubleIsoMappingCone g hi₀₁)).hom =
      DerivedCategory.Q.map (doubleToMappingCone g hi₀₁) := rfl
  rw [doubleProjQ, doubleProjQ, eg, ef]
  refine ((reassoc_of% hsq) _).symm.trans ?_
  exact (congrArg _ htri).trans (assoc _ _ _).symm

end Derived

end CochainComplex

end
