module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers

/-!
# The limit of a tower whose Milnor difference is an epimorphism is its derived limit

Let `A` be an abelian category with exact countable products and let `(Kₙ)` be an inverse system
of cochain complexes in `A`. The inverse limit `lim Kₙ` is the kernel of the Milnor difference
`1 - shift : ∏ Kₙ → ∏ Kₙ`. If that difference map is an epimorphism, the short exact sequence
`0 → lim Kₙ → ∏ Kₙ → ∏ Kₙ → 0` gives a distinguished triangle in `D(A)`, and products of
complexes are products in `D(A)`; so `lim Kₙ` is the derived limit `R lim Kₙ`, the images of the
limit projections being its projections.

For modules over a ring the difference map of a tower with surjective transition maps is
surjective; on a site with enough weakly contractible objects the same holds for sheaves of
modules (Stacks 0947).

## Main results

* `HomologicalComplex.epi_milnorDifference_of_epi_eval`: the Milnor difference of a tower of
  complexes is an epimorphism if it is one in every degree.
* `DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi_milnorDifference`: the limit of a
  tower of complexes with epimorphic Milnor difference is its derived limit, with projections.

## References

* [Stacks Project, Tag 0941](https://stacks.math.columbia.edu/tag/0941)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open NoetherianAdicCompletion

/-- A product-comparing functor carries the Milnor difference of a tower to that of the image
tower, up to the product comparison map. -/
private theorem map_milnorDifference_comp_piComparison {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] (G : D ⥤ D') [G.Additive] (X : ℕ → D)
    (f : ∀ n, X (n + 1) ⟶ X n) [HasProduct X] [HasProduct fun n ↦ G.obj (X n)] :
    G.map (Stacks.InverseSystem.milnorDifference X f) ≫ piComparison G X =
      piComparison G X ≫ Stacks.InverseSystem.milnorDifference (fun n ↦ G.obj (X n))
        (fun n ↦ G.map (f n)) := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  simp only [Category.assoc, Stacks.InverseSystem.milnorDifference_π, piComparison_comp_π,
    ← G.map_comp, Preadditive.comp_sub, G.map_sub, piComparison_comp_π_assoc]

namespace HomologicalComplex

variable {V : Type*} [Category V] [Abelian V] [HasProductsOfShape ℕ V] {ι : Type*}
  {c : ComplexShape ι}

/-- **The Milnor difference of a tower of complexes is an epimorphism as soon as it is one in
every degree.** Products of complexes are computed degreewise, and so is the difference map. -/
theorem epi_milnorDifference_of_epi_eval (F : ℕᵒᵖ ⥤ HomologicalComplex V c)
    (h : ∀ i : ι, Epi (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ (F.obj ⟨n⟩).X i)
      (fun n : ℕ ↦ (F.map (homOfLE (Nat.le_succ n)).op).f i))) :
    Epi (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ F.obj ⟨n⟩)
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op)) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  let G := HomologicalComplex.eval V c i
  let X := fun n : ℕ ↦ F.obj ⟨n⟩
  have : Epi (G.map (Stacks.InverseSystem.milnorDifference X
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op)) ≫ piComparison G X) := by
    rw [map_milnorDifference_comp_piComparison]
    exact @epi_comp _ _ _ _ _ _ inferInstance _ (h i)
  exact (epi_comp_iff_of_isIso _ _).1 this

end HomologicalComplex

namespace DerivedCategory

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]

/-- **The limit of a tower of complexes whose Milnor difference is an epimorphism is its
derived limit.** For an inverse system `F` of cochain complexes in an abelian category with exact
countable products, if `1 - shift : ∏ Fₙ → ∏ Fₙ` is an epimorphism, then `lim Fₙ` is a derived
limit of the images of the `Fₙ` in `D(A)`, the images of the limit projections being its
projections. -/
theorem isDerivedLimitWithProjections_Q_limit_of_epi_milnorDifference (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    [HasLimit F] [Epi (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ F.obj ⟨n⟩)
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op))] :
    letI := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := A) (I := ℕ)
    IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj (limit F))
      (fun n => DerivedCategory.Q.map (limit.π F ⟨n⟩)) := by
  let := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := A) (I := ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := A)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  have hk := inverseSystemLimitKernelForkIsLimit F
  let S := ShortComplex.mk _ _ (inverseSystemLimitKernelFork F).condition
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel S hk
      mono_f := mono_of_isLimit_fork hk
      epi_g := inferInstanceAs (Epi (Stacks.InverseSystem.milnorDifference
        (fun n : ℕ ↦ F.obj ⟨n⟩) (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op))) }
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  let e := PreservesProduct.iso DerivedCategory.Q (fun n : ℕ ↦ F.obj ⟨n⟩)
  let T₂ : Triangle (DerivedCategory A) :=
    Triangle.mk (Pi.lift fun n ↦ DerivedCategory.Q.map (limit.π F ⟨n⟩))
      (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ (F ⋙ DerivedCategory.Q).obj ⟨n⟩)
        (fun n : ℕ ↦ (F ⋙ DerivedCategory.Q).map (homOfLE (Nat.le_succ n)).op))
      (e.inv ≫ DerivedCategory.triangleOfSESδ hS)
  refine ⟨e.inv ≫ DerivedCategory.triangleOfSESδ hS,
    isomorphic_distinguished _ hT T₂
      (Triangle.isoMk (DerivedCategory.triangleOfSES hS) T₂ (Iso.refl _) e e ?_ ?_ ?_).symm⟩
  · apply Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, T₂, Triangle.mk_mor₁,
      DerivedCategory.triangleOfSES, Triangle.mk_obj₁, e, PreservesProduct.iso_hom,
      Iso.refl_hom]
    rw [← Functor.map_comp]
    simp [S, inverseSystemLimitKernelFork]
  · exact map_milnorDifference_comp_piComparison DerivedCategory.Q (fun n : ℕ ↦ F.obj ⟨n⟩)
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op)
  · show _ ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = e.hom ≫ e.inv ≫ _
    simp only [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).trans (e.hom_inv_id_assoc _).symm

end DerivedCategory
