module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The action of an exact functor on `Ext` into a complex

Let `Φ : 𝒜 ⥤ 𝒜'` be an exact functor of abelian categories, `E` an object of `D(𝒜)` and `C` a
cochain complex in `𝒜`.  A class `e ∈ Ext^i(E, C) = Hom(E, C[i])` is carried by `Φ` to a class
`Φ(e) ∈ Ext^i(Φ E, Φ C)`, read in the complex `Φ C` obtained by applying `Φ` termwise.  This
file records that this action is additive, natural in `C`, compatible with precomposition, and
compatible with the boundary maps `Ext^i(E, C₃) ⟶ Ext^{i+1}(E, C₁)` attached to a short exact
sequence of complexes `0 ⟶ C₁ ⟶ C₂ ⟶ C₃ ⟶ 0` (Mathlib's `DerivedCategory.map_triangleOfSESδ`).

## Main definitions

* `DerivedCategory.shiftedHomMapComplex`.

## Main results

* `DerivedCategory.shiftedHomMapComplex_naturality`.
* `DerivedCategory.shiftedHomMapComplex_comp_triangleOfSESδ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t t' v v' u u'

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {𝒜' : Type u'} [Category.{v'} 𝒜'] [Abelian 𝒜']
  [HasDerivedCategory.{t} 𝒜] [HasDerivedCategory.{t'} 𝒜']
  (Φ : 𝒜 ⥤ 𝒜') [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- **The action of an exact functor on `Ext` into a complex**: `e ↦ Φ(e)`, read in the complex
obtained by applying `Φ` termwise. -/
def shiftedHomMapComplex (E : DerivedCategory 𝒜) (C : CochainComplex 𝒜 ℤ) (i : ℤ) :
    ShiftedHom E (Q.obj C) i →+
      ShiftedHom (Φ.mapDerivedCategory.obj E) (Q.obj ((Φ.mapHomologicalComplex _).obj C)) i where
  toFun e := e.map Φ.mapDerivedCategory ≫ (Φ.mapDerivedCategoryFactors.hom.app C)⟦i⟧'
  map_zero' := by simp
  map_add' _ _ := by simp [Preadditive.add_comp]

/-- `shiftedHomMapComplex Φ E C i e` is `Φ(e)`, followed by the commutation of `Φ` with the shift
and by the comparison `Φ(Q C) ≅ Q(Φ C)` shifted by `i`. -/
theorem shiftedHomMapComplex_apply (E : DerivedCategory 𝒜) (C : CochainComplex 𝒜 ℤ) (i : ℤ)
    (e : ShiftedHom E (Q.obj C) i) :
    shiftedHomMapComplex Φ E C i e =
      Φ.mapDerivedCategory.map e ≫ (Φ.mapDerivedCategory.commShiftIso i).hom.app (Q.obj C) ≫
        (Φ.mapDerivedCategoryFactors.hom.app C)⟦i⟧' := by
  simp [shiftedHomMapComplex, ShiftedHom.map]

/-- The action of `Φ` commutes with precomposition. -/
theorem shiftedHomMapComplex_precomp {E' E : DerivedCategory 𝒜} (α : E' ⟶ E)
    (C : CochainComplex 𝒜 ℤ) (i : ℤ) (e : ShiftedHom E (Q.obj C) i) :
    shiftedHomMapComplex Φ E' C i (α ≫ e) =
      Φ.mapDerivedCategory.map α ≫ shiftedHomMapComplex Φ E C i e := by
  simp [shiftedHomMapComplex_apply]

/-- **The action of `Φ` is natural in the complex.** -/
theorem shiftedHomMapComplex_naturality (E : DerivedCategory 𝒜) {C C' : CochainComplex 𝒜 ℤ}
    (φ : C ⟶ C') (i : ℤ) (e : ShiftedHom E (Q.obj C) i) :
    shiftedHomMapComplex Φ E C' i (e ≫ (Q.map φ)⟦i⟧') =
      shiftedHomMapComplex Φ E C i e ≫ (Q.map ((Φ.mapHomologicalComplex _).map φ))⟦i⟧' := by
  simp only [shiftedHomMapComplex_apply, Functor.map_comp, Category.assoc]
  congr 1
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp,
    Φ.mapDerivedCategoryFactors_hom_naturality]

/-- **The action of `Φ` is compatible with the boundary maps of short exact sequences of
complexes**: the image of `e` followed by the boundary map of `0 ⟶ C₁ ⟶ C₂ ⟶ C₃ ⟶ 0` is the
image of `e` followed by the boundary map of `0 ⟶ ΦC₁ ⟶ ΦC₂ ⟶ ΦC₃ ⟶ 0`. -/
theorem shiftedHomMapComplex_comp_triangleOfSESδ (E : DerivedCategory 𝒜)
    {S : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact) (i : ℤ)
    (e : ShiftedHom E (Q.obj S.X₃) i) :
    shiftedHomMapComplex Φ E S.X₁ (i + 1) (e.comp (triangleOfSESδ hS) (add_comm 1 i)) =
      (shiftedHomMapComplex Φ E S.X₃ i e).comp
        (triangleOfSESδ (hS.map_of_exact (Φ.mapHomologicalComplex _))) (add_comm 1 i) := by
  have hδ : Φ.mapDerivedCategory.map (triangleOfSESδ hS) ≫
        (Φ.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) =
      Φ.mapDerivedCategoryFactors.hom.app S.X₃ ≫
        triangleOfSESδ (hS.map_of_exact (Φ.mapHomologicalComplex _)) ≫
          (Φ.mapDerivedCategoryFactors.inv.app S.X₁)⟦1⟧' := by
    have h := DerivedCategory.map_triangleOfSESδ Φ hS
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _)
  change (e.comp (triangleOfSESδ hS) (add_comm 1 i)).map Φ.mapDerivedCategory ≫
      (Φ.mapDerivedCategoryFactors.hom.app S.X₁)⟦i + 1⟧' =
    ShiftedHom.comp (show ShiftedHom _ _ i from
      e.map Φ.mapDerivedCategory ≫ (Φ.mapDerivedCategoryFactors.hom.app S.X₃)⟦i⟧')
      (triangleOfSESδ (hS.map_of_exact (Φ.mapHomologicalComplex _))) (add_comm 1 i)
  rw [ShiftedHom.map_comp]
  change (e.map Φ.mapDerivedCategory).comp (Φ.mapDerivedCategory.map (triangleOfSESδ hS) ≫
        (Φ.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁)) (add_comm 1 i) ≫ _ = _
  rw [hδ]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  congr 3
  have nat := (shiftFunctorAdd' (DerivedCategory 𝒜') 1 i (i + 1) (add_comm 1 i)).inv.naturality
    (Φ.mapDerivedCategoryFactors.inv.app S.X₁)
  dsimp at nat
  rw [reassoc_of% nat, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

end DerivedCategory

end
