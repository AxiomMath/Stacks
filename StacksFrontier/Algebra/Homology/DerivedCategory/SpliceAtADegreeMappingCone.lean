module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SpliceAtADegree

/-!
# The splice complex of a degree is a mapping cone

Let `m` be an integer, let `E` be a complex concentrated in degrees `≥ m` and `L` one
concentrated in degrees `≤ m - 1`, and let `g : Q(L) ⟶ Q(E)⟦1⟧`. The splice complex `M` of
`CochainComplex.exists_splice_triangle`, sitting in the distinguished triangle
`Q(E) ⟶ Q(M) ⟶ Q(L) ⟶ Q(E)⟦1⟧` with connecting morphism `g`, is constructed as the mapping cone
of a morphism `ψ : L⟦-1⟧ ⟶ E`, with `ι : E ⟶ M` the inclusion `mappingCone.inr ψ`.

## Main results

* `CochainComplex.exists_splice_triangle_mappingCone`: the splice triangle of
  `CochainComplex.exists_splice_triangle` together with an identification of `M` with a mapping
  cone `mappingCone ψ` under which `ι` is `mappingCone.inr ψ`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Pretriangulated

namespace CochainComplex

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A]

section Splice

variable [HasDerivedCategory.{w} A]

/-- **The splice complex of [Stacks, Tag 0FPV], as a mapping cone.** Let `m` be an integer, let
`E` be a complex concentrated in degrees `≥ m` and let `L` be a complex concentrated in degrees
`≤ m - 1`. Then every morphism `g : Q(L) ⟶ Q(E)⟦1⟧` of the derived category is the connecting
morphism of a distinguished triangle `Q(E) ⟶ Q(M) ⟶ Q(L) ⟶ Q(E)⟦1⟧` in which `M` is a complex
carrying morphisms of complexes `ι : E ⟶ M` and `π : M ⟶ L` which are isomorphisms in every
degree `≥ m`, resp. in every degree `< m`, and `M` is the mapping cone of a morphism
`ψ : L⟦-1⟧ ⟶ E` with `ι` the inclusion `mappingCone.inr ψ`. -/
theorem exists_splice_triangle_mappingCone (E L : CochainComplex A ℤ) (m : ℤ)
    [E.IsStrictlyGE m] [L.IsStrictlyLE (m - 1)]
    (g : DerivedCategory.Q.obj L ⟶ (DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧) :
    ∃ (M : CochainComplex A ℤ) (ι : E ⟶ M) (π : M ⟶ L),
      (∀ i : ℤ, m ≤ i → IsIso (ι.f i)) ∧ (∀ i : ℤ, i < m → IsIso (π.f i)) ∧
      Triangle.mk (DerivedCategory.Q.map ι) (DerivedCategory.Q.map π) g ∈
        distTriang (DerivedCategory A) ∧
      ∃ (ψ : L⟦(-1 : ℤ)⟧ ⟶ E) (e : M ≅ mappingCone ψ), ι ≫ e.hom = mappingCone.inr ψ := by
  have hFLE : (L⟦(-1 : ℤ)⟧).IsStrictlyLE m := L.isStrictlyLE_shift (m - 1) (-1) m (by lia)
  have eC : ((L⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) ≅ L :=
    (shiftFunctorCompIsoId (CochainComplex A ℤ) (-1 : ℤ) (1 : ℤ) (by lia)).app L
  obtain ⟨e, he⟩ :
      ∃ e : DerivedCategory.Q.obj L ≅ (DerivedCategory.Q.obj (L⟦(-1 : ℤ)⟧))⟦(1 : ℤ)⟧,
        e.hom = DerivedCategory.Q.map eC.inv ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (L⟦(-1 : ℤ)⟧) :=
    ⟨(DerivedCategory.Q.mapIso eC).symm ≪≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).app (L⟦(-1 : ℤ)⟧), rfl⟩
  obtain ⟨γ, hγ⟩ :=
    (CategoryTheory.shiftFunctor (DerivedCategory A) (1 : ℤ)).map_surjective (-(e.inv ≫ g))
  obtain ⟨ψ, hψ⟩ := exists_hom_Q_map_eq (L⟦(-1 : ℤ)⟧) E m γ
  obtain ⟨p₃, hp₃⟩ : ∃ p₃ : mappingCone ψ ⟶ (L⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧,
      p₃ = (mappingCone.triangle ψ).mor₃ := ⟨_, rfl⟩
  have hdist : (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle ψ)).rotate ∈
      distTriang (DerivedCategory A) :=
    rot_of_distTriang _ (DerivedCategory.mappingCone_triangle_distinguished ψ)
  refine ⟨mappingCone ψ, mappingCone.inr ψ, p₃ ≫ eC.hom, ?_, ?_, ?_, ψ, Iso.refl _,
    Category.comp_id _⟩
  · intro i hi
    refine mappingCone.isIso_inr_f ψ i ?_
    exact (L.isZero_of_isStrictlyLE (m - 1) i (by lia)).of_iso
      (L.shiftFunctorObjXIso (-1) (i + 1) i (by lia))
  · intro i hi
    have h₂ : IsIso (p₃.f i) := by
      rw [hp₃]
      exact mappingCone.isIso_triangle_mor₃_f ψ i (E.isZero_of_isStrictlyGE m i (by lia))
    have h₃ : IsIso (eC.hom.f i) := by
      have hev : IsIso ((HomologicalComplex.eval A (ComplexShape.up ℤ) i).map eC.hom) :=
        inferInstance
      exact hev
    exact IsIso.comp_isIso' h₂ h₃
  · refine isomorphic_distinguished _ hdist _ ?_
    refine Triangle.isoMk _ _ (Iso.refl (DerivedCategory.Q.obj E))
      (Iso.refl (DerivedCategory.Q.obj (mappingCone ψ))) e ?_ ?_ ?_
    · exact (comp_id (DerivedCategory.Q.map (mappingCone.inr ψ))).trans (id_comp _).symm
    · have hcancel : DerivedCategory.Q.map eC.hom ≫ DerivedCategory.Q.map eC.inv =
          𝟙 (DerivedCategory.Q.obj ((L⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧)) := by
        rw [← DerivedCategory.Q.map_comp, Iso.hom_inv_id, DerivedCategory.Q.map_id]
      have key : DerivedCategory.Q.map (p₃ ≫ eC.hom) ≫ e.hom =
          DerivedCategory.Q.map (mappingCone.triangle ψ).mor₃ ≫
            (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (L⟦(-1 : ℤ)⟧) := by
        rw [DerivedCategory.Q.map_comp, he]
        simp only [assoc]
        rw [← assoc (DerivedCategory.Q.map eC.hom), hcancel, id_comp, hp₃]
        rfl
      exact key.trans (id_comp _).symm
    · have key : e.hom ≫ (-((DerivedCategory.Q.map ψ)⟦(1 : ℤ)⟧')) = g := by
        rw [hψ, hγ, neg_neg, Iso.hom_inv_id_assoc]
      have key₂ : g ≫ ((𝟙 (DerivedCategory.Q.obj E))⟦(1 : ℤ)⟧') = g := by simp
      exact key₂.trans key.symm

end Splice

end CochainComplex

end
