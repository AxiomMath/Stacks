module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Double
public import StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso

/-!
# A two-term complex is the cone on its differential

Let `f : X₀ ⟶ X₁` be a morphism in an additive category and let `i₀`, `i₁` be two degrees with
`i₁ = i₀ + 1`. The cochain complex `HomologicalComplex.double f` is `f` placed in degrees `i₀`
and `i₁` and zero elsewhere. On the other hand the single complexes `X₀` and `X₁` in degree `i₁`
are related by `(single i₁).map f`, whose mapping cone is `X₀` in degree `i₀` and `X₁` in degree
`i₁`. Those two complexes are canonically isomorphic, so `double f` fits into the standard
triangle of a mapping cone: in any triangulated category receiving the cochain complexes,

`X₁[i₁] ⟶ double f ⟶ (X₀[i₁])⟦1⟧`

extends the map `X₀[i₁] ⟶ X₁[i₁]` induced by `f` to a distinguished triangle.

## Main definitions

* `CochainComplex.doubleToMappingCone`: the comparison morphism
  `double f ⟶ mappingCone ((single i₁).map f)`, built from the two inclusions of the cone.
* `CochainComplex.doubleIsoMappingCone`: that morphism as an isomorphism.
* `CochainComplex.doubleInclh` and `CochainComplex.doubleProjh`: the two remaining maps of the
  triangle, in the homotopy category of cochain complexes.
* `CochainComplex.doubleInclQ` and `CochainComplex.doubleProjQ`: the same in the derived
  category of an abelian category.

## Main results

* `CochainComplex.isIso_doubleToMappingCone`: the comparison morphism is an isomorphism.
* `CochainComplex.doubleTriangleh_distinguished`: the triangle
  `X₀[i₁] ⟶ X₁[i₁] ⟶ double f ⟶ (X₀[i₁])⟦1⟧` is distinguished in the homotopy category.
* `CochainComplex.doubleTriangleQ_distinguished`: it is distinguished in the derived category,
  where the two single complexes are the values of `DerivedCategory.singleFunctor`. This is the
  form in which a consumer sees `double f` as an extension of its degree `0` term by a shift of
  its degree `-1` term, for instance for the two-term naive cotangent complex, which is built
  with `HomologicalComplex.double` in degrees `-1` and `0`.
* `CategoryTheory.Pretriangulated.mk_mem_distTriang_of_iso_obj₃`: an auxiliary statement, that a
  distinguished triangle stays distinguished when its third object is replaced by an isomorphic
  one.

## Implementation notes

The comparison morphism is produced by `HomologicalComplex.mkHomFromDouble`, so the only data to
supply are its two nonzero components: in degree `i₀` the degree `(i₁, i₀)` component of
`CochainComplex.mappingCone.inl`, and in degree `i₁` the degree `i₁` component of
`CochainComplex.mappingCone.inr`. It is an isomorphism degreewise: in the two degrees `i₀` and
`i₁` by `CochainComplex.mappingCone.isIso_inl_v` and
`CochainComplex.mappingCone.isIso_inr_f`, one of the two summands of the cone being zero there,
and in every other degree because both complexes vanish.

The two maps completing the triangle are the transports of `mappingCone.inr` and of the third
map of `CochainComplex.mappingCone.triangle` along that isomorphism; the triangle is then
distinguished because the triangle of a mapping cone is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated HomologicalComplex

universe w v u

namespace CategoryTheory.Pretriangulated

/-- **A distinguished triangle may have its third object replaced by an isomorphic one.** If
`T` is distinguished and `e : Z ≅ T.obj₃`, then the triangle obtained from `T` by composing its
second map with `e.inv` and its third map with `e.hom` is distinguished. -/
theorem mk_mem_distTriang_of_iso_obj₃ {A : Type*} [Category A] [HasZeroObject A] [HasShift A ℤ]
    [Preadditive A] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (T : Triangle A) (hT : T ∈ distTriang A) {Z : A} (e : Z ≅ T.obj₃) :
    Triangle.mk T.mor₁ (T.mor₂ ≫ e.inv) (e.hom ≫ T.mor₃) ∈ distTriang A :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e (by simp) (by simp) (by simp))

end CategoryTheory.Pretriangulated

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {X₀ X₁ : C} (f : X₀ ⟶ X₁) {i₀ i₁ : ℤ}
  (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁)

/-- The comparison morphism from the two-term complex `HomologicalComplex.double f`, with `f` in
degrees `i₀` and `i₁ = i₀ + 1`, to the mapping cone of the map of single complexes in degree
`i₁` induced by `f`. In degree `i₀` it is the inclusion of the shifted source of the cone and in
degree `i₁` the inclusion of its target. -/
def doubleToMappingCone :
    double f hi₀₁ ⟶ mappingCone ((single C (ComplexShape.up ℤ) i₁).map f) :=
  mkHomFromDouble hi₀₁ (by have h : i₀ + 1 = i₁ := hi₀₁; omega)
    ((singleObjXSelf (ComplexShape.up ℤ) i₁ X₀).inv ≫
      (mappingCone.inl _).v i₁ i₀ (by have h : i₀ + 1 = i₁ := hi₀₁; omega))
    ((singleObjXSelf (ComplexShape.up ℤ) i₁ X₁).inv ≫ (mappingCone.inr _).f i₁)
    (by
      have h : i₀ + 1 = i₁ := hi₀₁
      rw [assoc, mappingCone.inl_v_d _ i₁ i₀ (i₁ + 1) (by omega) (by omega)]
      have hd : ((single C (ComplexShape.up ℤ) i₁).obj X₀).d i₁ (i₁ + 1) = 0 := rfl
      rw [hd, zero_comp, sub_zero, single_map_f_self]
      simp)
    (fun k hk => by
      have h : i₀ + 1 = i₁ := hi₀₁
      have hk' : i₁ + 1 = k := hk
      refine (?_ : IsZero ((mappingCone ((single C (ComplexShape.up ℤ) i₁).map f)).X k)).eq_of_tgt
        _ _
      rw [mappingCone.isZero_X_iff]
      exact ⟨isZero_single_obj_X _ _ _ _ (by omega), isZero_single_obj_X _ _ _ _ (by omega)⟩)

/-- **A two-term complex is the cone on its differential.** The comparison morphism from
`HomologicalComplex.double f` to the mapping cone of the induced map of single complexes in
degree `i₁` is an isomorphism. -/
theorem isIso_doubleToMappingCone : IsIso (doubleToMappingCone f hi₀₁) := by
  have h : i₀ + 1 = i₁ := hi₀₁
  have e₀ : IsIso ((doubleToMappingCone f hi₀₁).f i₀) := by
    have h1 : IsIso ((mappingCone.inl ((single C (ComplexShape.up ℤ) i₁).map f)).v i₁ i₀
        (by omega)) :=
      mappingCone.isIso_inl_v _ _ _ _ (isZero_single_obj_X _ _ _ _ (by omega))
    rw [doubleToMappingCone, mkHomFromDouble_f₀]
    infer_instance
  have e₁ : IsIso ((doubleToMappingCone f hi₀₁).f i₁) := by
    have h1 : IsIso ((mappingCone.inr ((single C (ComplexShape.up ℤ) i₁).map f)).f i₁) :=
      mappingCone.isIso_inr_f _ _ (isZero_single_obj_X _ _ _ _ (by omega))
    rw [doubleToMappingCone, mkHomFromDouble_f₁]
    infer_instance
  have : ∀ n, IsIso ((doubleToMappingCone f hi₀₁).f n) := by
    intro n
    by_cases h₀ : n = i₀
    · rw [h₀]; exact e₀
    by_cases h₁ : n = i₁
    · rw [h₁]; exact e₁
    have hz : IsZero ((double f hi₀₁).X n) := isZero_double_X f hi₀₁ n h₀ h₁
    have hz' : IsZero ((mappingCone ((single C (ComplexShape.up ℤ) i₁).map f)).X n) := by
      rw [mappingCone.isZero_X_iff]
      exact ⟨isZero_single_obj_X _ _ _ _ (by omega), isZero_single_obj_X _ _ _ _ (by omega)⟩
    have hn : (doubleToMappingCone f hi₀₁).f n = (hz.iso hz').hom := hz.eq_of_src _ _
    rw [hn]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The identification of the two-term complex `HomologicalComplex.double f`, with `f` in degrees
`i₀` and `i₁ = i₀ + 1`, with the mapping cone of the map of single complexes in degree `i₁`
induced by `f`. -/
def doubleIsoMappingCone :
    (double f hi₀₁ : CochainComplex C ℤ) ≅
      mappingCone ((single C (ComplexShape.up ℤ) i₁).map f) :=
  have := isIso_doubleToMappingCone f hi₀₁
  asIso (doubleToMappingCone f hi₀₁)

/-- The inclusion, in the homotopy category of cochain complexes, of the degree `i₁` term of the
two-term complex `HomologicalComplex.double f`: the inclusion of the target in the mapping cone,
read through `CochainComplex.doubleIsoMappingCone`. -/
def doubleInclh :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((single C (ComplexShape.up ℤ) i₁).obj X₁) ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (double f hi₀₁) :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (mappingCone.inr ((single C (ComplexShape.up ℤ) i₁).map f)) ≫
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso
      (doubleIsoMappingCone f hi₀₁)).inv

/-- The projection, in the homotopy category of cochain complexes, of the two-term complex
`HomologicalComplex.double f` onto the shift of its degree `i₀` term: the third map of the
triangle of the mapping cone, read through `CochainComplex.doubleIsoMappingCone`. -/
def doubleProjh :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (double f hi₀₁) ⟶
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((single C (ComplexShape.up ℤ) i₁).obj X₀))⟦(1 : ℤ)⟧ :=
  ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso
      (doubleIsoMappingCone f hi₀₁)).hom ≫
    (mappingCone.triangleh ((single C (ComplexShape.up ℤ) i₁).map f)).mor₃

/-- **The two-term complex on `f : X₀ ⟶ X₁` is an extension of `X₁` by a shift of `X₀`.** In the
homotopy category of cochain complexes, the single complexes on `X₀` and `X₁` in degree `i₁`, the
complex `HomologicalComplex.double f` with `f` in degrees `i₀` and `i₁ = i₀ + 1`, and the maps
induced by `f`, by the inclusion of the degree `i₁` term and by the projection onto the shifted
degree `i₀` term, form a distinguished triangle. -/
theorem doubleTriangleh_distinguished :
    Triangle.mk ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((single C (ComplexShape.up ℤ) i₁).map f))
      (doubleInclh f hi₀₁) (doubleProjh f hi₀₁) ∈
        distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
  mk_mem_distTriang_of_iso_obj₃ _
    (HomotopyCategory.mappingCone_triangleh_distinguished
      ((single C (ComplexShape.up ℤ) i₁).map f))
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso (doubleIsoMappingCone f hi₀₁))

end

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X₀ X₁ : C} (f : X₀ ⟶ X₁) {i₀ i₁ : ℤ} (hi₀₁ : (ComplexShape.up ℤ).Rel i₀ i₁)

/-- The inclusion, in the derived category, of the degree `i₁` term of the two-term complex
`HomologicalComplex.double f`: the inclusion of the target in the mapping cone, read through
`CochainComplex.doubleIsoMappingCone`. -/
def doubleInclQ : (DerivedCategory.singleFunctor C i₁).obj X₁ ⟶
    DerivedCategory.Q.obj (double f hi₀₁) :=
  DerivedCategory.Q.map (mappingCone.inr ((single C (ComplexShape.up ℤ) i₁).map f)) ≫
    (DerivedCategory.Q.mapIso (doubleIsoMappingCone f hi₀₁)).inv

/-- The projection, in the derived category, of the two-term complex
`HomologicalComplex.double f` onto the shift of its degree `i₀` term: the third map of the
triangle of the mapping cone, read through `CochainComplex.doubleIsoMappingCone`. -/
def doubleProjQ : DerivedCategory.Q.obj (double f hi₀₁) ⟶
    ((DerivedCategory.singleFunctor C i₁).obj X₀)⟦(1 : ℤ)⟧ :=
  (DerivedCategory.Q.mapIso (doubleIsoMappingCone f hi₀₁)).hom ≫
    (DerivedCategory.Q.mapTriangle.obj
      (mappingCone.triangle ((single C (ComplexShape.up ℤ) i₁).map f))).mor₃

/-- **The two-term complex on `f : X₀ ⟶ X₁` is an extension of `X₁` by a shift of `X₀`.** In the
derived category of an abelian category, the objects `X₀` and `X₁` in degree `i₁`, the complex
`HomologicalComplex.double f` with `f` in degrees `i₀` and `i₁ = i₀ + 1`, and the maps induced by
`f`, by the inclusion of the degree `i₁` term and by the projection onto the shifted degree `i₀`
term, form a distinguished triangle. -/
theorem doubleTriangleQ_distinguished :
    Triangle.mk ((DerivedCategory.singleFunctor C i₁).map f) (doubleInclQ f hi₀₁)
      (doubleProjQ f hi₀₁) ∈ distTriang (DerivedCategory C) :=
  mk_mem_distTriang_of_iso_obj₃ _
    (DerivedCategory.mappingCone_triangle_distinguished
      ((single C (ComplexShape.up ℤ) i₁).map f))
    (DerivedCategory.Q.mapIso (doubleIsoMappingCone f hi₀₁))

end Derived

end CochainComplex

end
