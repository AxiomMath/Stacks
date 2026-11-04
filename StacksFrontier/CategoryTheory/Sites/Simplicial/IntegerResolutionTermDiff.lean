module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionPostnikov
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorBarStructure

/-!
# The differential of the Postnikov system of Stacks 0D9I is the alternating face differential

Let `S` be a simplicial-site situation. The resolution `… → g₂!ℤ → g₁!ℤ → g₀!ℤ` of Stacks 09WI
enters the Postnikov system of Stacks 0D9I as the cochain complex
`CategoryTheory.SimplicialSiteSituation.integerResolutionComplex`, whose term in cohomological
degree `-n` is the degree-`n` term of the simplicial abelian sheaf of simplices, and whose
differential is therefore the alternating sum of that simplicial object's face maps. The terms of
the Postnikov system are those terms read in the derived category,
`StacksDraft.BrutalPostnikov.term`, and its differential is
`StacksDraft.BrutalPostnikov.termDiff`.

The sheaf-level computations that the proof of Stacks 0D9K rests on are stated not for the face
maps of that simplicial object but for
`CategoryTheory.SimplicialSiteSituation.integerFace`, the same structure map read through the
identification `CategoryTheory.SimplicialSiteSituation.resolutionDegreeIso'` of the degree-`n`
term with `g_{n!}ℤ`. This file identifies the two: transported along
`CategoryTheory.SimplicialSiteSituation.integerResolutionTermIso`, the differential of the
Postnikov system is the alternating sum `∑ (-1)ⁱ integerFace (δ i)` of the structure maps at the
cofaces, placed in cohomological degree zero. In degree zero that sum is the difference
`integerFace δ₀ - integerFace δ₁` of the two faces `⦋0⦌ ⟶ ⦋1⦌`, the form needed for the first of
the two computations omitted in the proof of Stacks 0D9K.

## Main results

* `CategoryTheory.SimplicialSiteSituation.integerFace_eq_simplicialIntegerResolution_map`: the
  structure map `integerFace` is the structure map of the simplicial object of the resolution of
  Stacks 09WI, read through that structure's own degreewise identification.
* `CategoryTheory.SimplicialSiteSituation.integerResolutionTermIso_inv_comp_termDiff`: **the
  differential of the Postnikov system of Stacks 0D9I is the alternating face differential**,
  transported along the identification of its terms with `g_{n!}ℤ`.
* `CategoryTheory.SimplicialSiteSituation.integerResolutionTermIso_inv_comp_termDiff_zero`: the
  same in degree zero, where the alternating sum is `integerFace δ₀ - integerFace δ₁`.

## References

* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.BrutalPostnikov
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- **The structure map `integerFace` is the structure map of the simplicial object of the
resolution of Stacks 09WI**, read through that structure's own degreewise identification of the
degree-`n` term with `g_{n!}ℤ`. Both the simplicial object and the identification of the
resolution are those of `resolutionSimplicial'` and `resolutionDegreeIso'`, which is what
`simplicialIntegerResolution_simplicial` and `simplicialIntegerResolution_degreeIso` say. -/
theorem integerFace_eq_simplicialIntegerResolution_map {n m : ℕ}
    (θ : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌) :
    integerFace S θ =
      ((simplicialIntegerResolution S).degreeIso m).inv ≫
        (simplicialIntegerResolution S).simplicial.map θ.op ≫
          ((simplicialIntegerResolution S).degreeIso n).hom :=
  rfl

/-- The identification of the degree `-n` term of the cochain complex of the integral resolution
with `g_{n!}ℤ`, written out: the identification of the term of an extended complex with the term
it extends, followed by the degreewise identification of the resolution. -/
theorem integerResolutionComplexXIso_eq (n : ℕ) :
    integerResolutionComplexXIso S n =
      HomologicalComplex.extendXIso (simplicialIntegerComplex S)
          (ComplexShape.embeddingUpIntLE 0) (i := n) (by simp) ≪≫
        (simplicialIntegerResolution S).degreeIso n :=
  rfl

/-- Conjugating a morphism by two isomorphisms, each presented as a composite whose first factor
cancels against the morphism's own presentation: the shape in which the differential of an
extended complex, read through the identifications of the extended terms, meets the
identifications of the terms of the complex it extends. -/
private theorem cancel_conj {C : Type*} [Category C] {A B₁ P B₂ R T : C}
    (α : P ≅ A) (β : B₁ ≅ P) (u : P ⟶ R) (γ : B₂ ≅ R) (δ : R ≅ T) :
    (β ≪≫ α).inv ≫ (β.hom ≫ u ≫ γ.inv) ≫ (γ ≪≫ δ).hom = α.inv ≫ u ≫ δ.hom := by
  simp

/-- **The differential of the alternating face map complex of the resolution of Stacks 09WI,
read through the degreewise identification of its terms with `g_{n!}ℤ`, is the alternating sum of
the structure maps at the cofaces.** -/
theorem degreeIso_inv_comp_simplicialIntegerComplex_d (n : ℕ) :
    ((simplicialIntegerResolution S).degreeIso (n + 1)).inv ≫
        (simplicialIntegerComplex S).d (n + 1) n ≫
          ((simplicialIntegerResolution S).degreeIso n).hom =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • integerFace S (SimplexCategory.δ i) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun (i : Fin (n + 2)) _ => ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    integerFace_eq_simplicialIntegerResolution_map S (SimplexCategory.δ i)]
  rfl

/-- **The differential of the cochain complex of the integral resolution is the alternating face
differential**, transported along the identification of its terms with `g_{n!}ℤ`. The complex is
the alternating face map complex of the simplicial abelian sheaf of simplices, extended by zero
from the nonpositive degrees, so its differential is that of the alternating face map complex
read through `HomologicalComplex.extendXIso`; conjugating the alternating sum degreewise turns
each face into the corresponding `integerFace`. -/
theorem integerResolutionComplexXIso_inv_comp_d (n : ℕ) :
    (integerResolutionComplexXIso S (n + 1)).inv ≫
        (integerResolutionComplex S).d (-((n : ℤ) + 1)) (-(n : ℤ)) ≫
          (integerResolutionComplexXIso S n).hom =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • integerFace S (SimplexCategory.δ i) := by
  have hi : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f (n + 1) = -((n + 1 : ℕ) : ℤ) := by simp
  have hj : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -((n : ℕ) : ℤ) := by simp
  have hd : (integerResolutionComplex S).d (-((n : ℤ) + 1)) (-(n : ℤ)) =
      (HomologicalComplex.extendXIso (simplicialIntegerComplex S)
            (ComplexShape.embeddingUpIntLE 0) hi).hom ≫
        (simplicialIntegerComplex S).d (n + 1) n ≫
          (HomologicalComplex.extendXIso (simplicialIntegerComplex S)
            (ComplexShape.embeddingUpIntLE 0) hj).inv :=
    HomologicalComplex.extend_d_eq _ _ hi hj
  rw [hd, ← degreeIso_inv_comp_simplicialIntegerComplex_d S n]
  exact cancel_conj _ _ _ _ _

section Derived

universe z

variable [HasDerivedCategory.{z} (Sheaf S.totalTopology Ab.{u})]

/-- **The differential of the Postnikov system of Stacks 0D9I is the alternating face
differential.** The term `Xₙ = g_{n!}ℤ` of the system is the degree `-n` term of the cochain
complex of the integral resolution placed in cohomological degree zero, and `termDiff` is the
differential of that complex placed in degree zero; transported along the identification of the
terms with `g_{n!}ℤ` it becomes the alternating sum of the structure maps at the cofaces. -/
theorem integerResolutionTermIso_inv_comp_termDiff (n : ℕ) :
    (integerResolutionTermIso S (n + 1)).inv ≫
        termDiff (integerResolutionComplex S) n ≫ (integerResolutionTermIso S n).hom =
      (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • integerFace S (SimplexCategory.δ i)) := by
  rw [← integerResolutionComplexXIso_inv_comp_d S n, Functor.map_comp, Functor.map_comp]
  rfl

/-- **The differential of the Postnikov system of Stacks 0D9I in degree zero is the difference of
the two faces `⦋0⦌ ⟶ ⦋1⦌`.** This is the form needed for the first of the two computations
omitted in the proof of Stacks 0D9K: the composite `X₁ ⟶ X₀ ⟶ K'` through either face is the
same, so the difference annihilates the map `X₀ ⟶ K'`. -/
theorem integerResolutionTermIso_inv_comp_termDiff_zero :
    (integerResolutionTermIso S 1).inv ≫
        termDiff (integerResolutionComplex S) 0 ≫ (integerResolutionTermIso S 0).hom =
      (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).map
        (integerFace S (SimplexCategory.δ (0 : Fin 2)) -
          integerFace S (SimplexCategory.δ (1 : Fin 2))) := by
  rw [integerResolutionTermIso_inv_comp_termDiff S 0]
  congr 1
  rw [Fin.sum_univ_two]
  simp [sub_eq_add_neg]

end Derived

end CategoryTheory.SimplicialSiteSituation

end
