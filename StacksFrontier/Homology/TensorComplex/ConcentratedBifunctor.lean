module

public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegrees

/-!
# Complexes concentrated in one degree

A cochain complex `K` is concentrated in degree `a` if `K.X i` is zero for `i ≠ a`; a single
complex is the basic example, but so is the image of a single complex under an additive functor,
which is not literally a single complex.

## Main definitions

* `Stacks.ConcentratedComplex.isoOfConcentrated`: an isomorphism in the one degree between two
  complexes concentrated in that degree is an isomorphism of complexes.

## Main results

* `Stacks.ConcentratedComplex.isIso_ιMapBifunctor`: for `K` concentrated in degree `a` and `L`
  in degree `b`, the inclusion of the summand `(a, b)` into `Tot(F(K, L))` in degree `a + b` is
  an isomorphism.
* `Stacks.ConcentratedComplex.isZero_mapBifunctor_X`: `Tot(F(K, L))` is concentrated in degree
  `a + b`.

These generalize `HomologicalComplex.isIso_ιMapBifunctor_single_single` and
`HomologicalComplex.isZero_mapBifunctor_single_single_X`.

## References

* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Stacks.ConcentratedComplex

section Bifunctor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D] [Preadditive C₁]
  [Preadditive C₂] [Preadditive D] (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ M : C₁, (F.obj M).Additive]
  (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) (a b : ℤ)
  (hK : ∀ i, i ≠ a → IsZero (K.X i)) (hL : ∀ j, j ≠ b → IsZero (L.X j))

include hK hL

/-- Off the pair `(a, b)` the bifunctor applied to the terms of two concentrated complexes
vanishes. -/
theorem isZero_obj_obj_X_X (i j : ℤ) (h : i ≠ a ∨ j ≠ b) :
    IsZero ((F.obj (K.X i)).obj (L.X j)) := by
  rcases h with hi | hj
  · exact (F.flip.obj (L.X j)).map_isZero (hK i hi)
  · exact (F.obj (K.X i)).map_isZero (hL j hj)

variable [K.HasMapBifunctor L F (ComplexShape.up ℤ)]

/-- The total complex of two concentrated complexes is concentrated in the sum of the
degrees. -/
theorem isZero_mapBifunctor_X (k : ℤ) (hk : k ≠ a + b) :
    IsZero ((mapBifunctor K L F (ComplexShape.up ℤ)).X k) := by
  rw [IsZero.iff_id_eq_zero]
  refine mapBifunctor.hom_ext fun i j hij => ?_
  refine (isZero_obj_obj_X_X F K L a b hK hL i j ?_).eq_of_src _ _
  have hij' : i + j = k := hij
  by_cases hi : i = a
  · exact Or.inr (by omega)
  · exact Or.inl hi

/-- In degree `a + b` the total complex of two concentrated complexes is the summand `(a, b)`:
its inclusion is an isomorphism. -/
theorem isIso_ιMapBifunctor :
    IsIso (ιMapBifunctor K L F (ComplexShape.up ℤ) a b (a + b) rfl) := by
  refine ⟨mapBifunctorDesc fun i j hij => if h : i = a ∧ j = b then
    eqToHom (by rw [h.1, h.2]) else 0, ?_, ?_⟩
  · simp
  · refine mapBifunctor.hom_ext fun i j hij => ?_
    by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · exact (isZero_obj_obj_X_X F K L a b hK hL i j (not_and_or.mp h)).eq_of_src _ _

end Bifunctor

section Iso

variable {C : Type*} [Category* C] [Preadditive C] (A B : CochainComplex C ℤ) (n : ℤ)
  (hA : ∀ k, k ≠ n → IsZero (A.X k)) (hB : ∀ k, k ≠ n → IsZero (B.X k)) (e : A.X n ≅ B.X n)

/-- **An isomorphism in the one degree of two complexes concentrated in that degree is an
isomorphism of complexes**: every differential has a zero source or a zero target. -/
def isoOfConcentrated : A ≅ B :=
  Hom.isoOfComponents (fun k => if h : k = n then
      A.XIsoOfEq h ≪≫ e ≪≫ (B.XIsoOfEq h).symm
    else (hA k h).iso (hB k h)) (by
    intro i j hij
    by_cases hi : i = n
    · have hj : j ≠ n := by
        have hij' : i + 1 = j := hij
        omega
      exact (hB j hj).eq_of_tgt _ _
    · exact (hA i hi).eq_of_src _ _)

/-- In the degree of concentration the isomorphism is the given one. -/
theorem isoOfConcentrated_hom_f : (isoOfConcentrated A B n hA hB e).hom.f n = e.hom := by
  simp [isoOfConcentrated]

end Iso

end Stacks.ConcentratedComplex

end
