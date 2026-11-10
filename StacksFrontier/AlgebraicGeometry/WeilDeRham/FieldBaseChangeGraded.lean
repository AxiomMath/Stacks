module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChangeLinear

/-!
# The comparison isomorphisms of Lemma 0FVT on graded pieces

The comparison isomorphisms `F' ⊗_F H^*(X) ≅ (H')^*(X_{k'})` of the hypothesis (3) of Lemma 0FVT
of the Stacks Project are isomorphisms of graded algebras: they carry `H^n(X)` into
`(H')^n(X_{k'})`. This file shows that they restrict to isomorphisms
`F' ⊗_F H^n(X) ≅ (H')^n(X_{k'})` of the graded pieces, which is how the proof of the lemma reads
statements about a single cohomological degree, as in (A6) and (A8).

## Main definitions

* `Stacks.WeilDeRham.FieldBaseChangeData.gradedEquiv`: `F' ⊗_F H^n(X) ≅ (H')^n(X_{k'})`.

## Main results

* `Stacks.WeilDeRham.FieldBaseChangeData.cohHom_gradedProj`: the comparison map commutes with the
  projections onto the graded pieces.

## References

* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Stacks.WeilCohomology

universe u w w'

namespace Stacks.WeilDeRham

open Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldBaseChangeData

variable (B : FieldBaseChangeData 𝔇 𝔇') (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The comparison map commutes with the projections onto the graded pieces**: the image of the
degree-`n` part of `a` is the degree-`n` part of the image of `a`. -/
theorem cohHom_gradedProj (n : ℤ) (a : 𝔇.H X) :
    B.cohHom X (𝔇.projGrade X n a) =
      𝔇'.projGrade ((fieldBaseChange k k').obj X) n (B.cohHom X a) := by
  induction a using DirectSum.Decomposition.inductionOn (ℳ := 𝔇.grade X) with
  | zero => simp
  | homogeneous a =>
    rename_i m
    rw [FirstChernClassData.coe_projGrade, FirstChernClassData.coe_projGrade]
    by_cases hm : m = n
    · subst hm
      rw [DirectSum.decompose_of_mem_same _ a.2,
        DirectSum.decompose_of_mem_same _ (B.cohHom_mem_grade X a.2)]
    · rw [DirectSum.decompose_of_mem_ne _ a.2 hm,
        DirectSum.decompose_of_mem_ne _ (B.cohHom_mem_grade X a.2) hm, map_zero]
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]

/-- The comparison map on `F' ⊗_F H^n(X)`, with values in `(H')^*(X_{k'})`. -/
def gradedHom (n : ℤ) : F' ⊗[F] 𝔇.grade X n →ₗ[F'] 𝔇'.H ((fieldBaseChange k k').obj X) :=
  (B.cohEquiv X).toLinearEquiv.toLinearMap ∘ₗ ((𝔇.grade X n).subtype.baseChange F')

/-- `gradedHom` sends `c ⊗ a` to `c` times the image of `a` under the comparison map. -/
theorem gradedHom_tmul (n : ℤ) (c : F') (a : 𝔇.grade X n) :
    B.gradedHom X n (c ⊗ₜ a) = c • B.cohHom X a := by
  rw [cohHom_apply, ← map_smul, ← TensorProduct.tmul_eq_smul_one_tmul]
  rfl

/-- `gradedHom` takes values in the degree-`n` piece `(H')^n(X_{k'})`. -/
theorem gradedHom_mem (n : ℤ) (x : F' ⊗[F] 𝔇.grade X n) :
    B.gradedHom X n x ∈ 𝔇'.grade ((fieldBaseChange k k').obj X) n := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    rw [gradedHom_tmul]
    exact Submodule.smul_mem _ _ (B.cohHom_mem_grade X a.2)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- `gradedHom` is injective: it is the base change of an inclusion, followed by an isomorphism. -/
theorem gradedHom_injective (n : ℤ) : Function.Injective (B.gradedHom X n) :=
  (B.cohEquiv X).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))

/-- `gradedHom` followed by the projection onto degree `n` is the base change of the projection. -/
theorem gradedHom_lTensor_gradedProj (n : ℤ) (x : F' ⊗[F] 𝔇.H X) :
    B.gradedHom X n ((𝔇.projGrade X n).baseChange F' x) =
      𝔇'.projGrade ((fieldBaseChange k k').obj X) n (B.cohEquiv X x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    rw [LinearMap.baseChange_tmul, gradedHom_tmul, cohHom_gradedProj]
    rw [TensorProduct.tmul_eq_smul_one_tmul c a, map_smul, map_smul, ← cohHom_apply]
    simp
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

/-- **The comparison isomorphism on the graded pieces**, `F' ⊗_F H^n(X) ≅ (H')^n(X_{k'})`. -/
def gradedEquiv (n : ℤ) :
    F' ⊗[F] 𝔇.grade X n ≃ₗ[F'] 𝔇'.grade ((fieldBaseChange k k').obj X) n :=
  LinearEquiv.ofBijective ((B.gradedHom X n).codRestrict _ (B.gradedHom_mem X n))
    ⟨fun x y hxy => B.gradedHom_injective X n (congrArg Subtype.val hxy), fun y => by
      refine ⟨(𝔇.projGrade X n).baseChange F' ((B.cohEquiv X).symm y), Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, gradedHom_lTensor_gradedProj, AlgEquiv.apply_symm_apply,
        FirstChernClassData.coe_projGrade, DirectSum.decompose_of_mem_same _ y.2]⟩

/-- The underlying element of `gradedEquiv X n x` is `gradedHom X n x`. -/
@[simp]
theorem coe_gradedEquiv (n : ℤ) (x : F' ⊗[F] 𝔇.grade X n) :
    (B.gradedEquiv X n x : 𝔇'.H ((fieldBaseChange k k').obj X)) = B.gradedHom X n x :=
  rfl

end FieldBaseChangeData

end Stacks.WeilDeRham

end
