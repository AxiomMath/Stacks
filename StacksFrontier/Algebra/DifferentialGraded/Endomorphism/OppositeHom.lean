module

public import StacksFrontier.Algebra.DifferentialGraded.Opposite
public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction

/-!
# Homomorphisms between graded opposite differential graded algebras

A homomorphism `f : B ⟶ C` of differential graded algebras over a commutative ring `R` induces a
homomorphism `Bᵒᵖ ⟶ Cᵒᵖ` of their graded opposites: the underlying `R`-linear map is the same, read
through the canonical identifications of the opposites with the originals, and multiplicativity
holds because both opposites twist the multiplication by the same Koszul sign. Taking the graded
opposite twice gives back the original algebra, which is recorded as an `Opposite` datum for the
opposite.

## Main definitions

* `DifferentialGradedAlgebra.Opposite.involution`: the original algebra, as a graded opposite of
  the graded opposite.
* `DifferentialGradedAlgebra.oppositeHom`: the induced homomorphism of graded opposites.

## Implementation notes

Both constructions are checked on homogeneous elements, where the sign rule of
`Opposite.map_mul_of_mem` applies, and extended by the direct-sum decomposition. The algebra
homomorphism is assembled from its underlying linear map with `AlgHom.ofLinearMap`, so that
compatibility with the `R`-algebra structure is inherited from `R`-linearity rather than checked
separately.

## References

* [Stacks Project, Tag 0FQ5](https://stacks.math.columbia.edu/tag/0FQ5)
-/

@[expose] public section

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The original algebra, viewed as a graded opposite of its graded opposite. -/
abbrev Opposite.involution (A : DifferentialGradedAlgebra R) (O : Opposite R A) :
    Opposite R O.toDifferentialGradedAlgebra where
  toDifferentialGradedAlgebra := A
  equiv := O.equiv.symm
  mem_grading_iff n x := by simp only [O.mem_grading_iff, LinearEquiv.apply_symm_apply]
  map_d x := by
    apply O.equiv.injective
    simp only [LinearEquiv.apply_symm_apply, O.map_d]
  map_one := by
    apply O.equiv.injective
    simp only [LinearEquiv.apply_symm_apply, O.map_one]
  map_mul_of_mem n m a b ha hb := by
    apply O.equiv.injective
    have ha' := (O.mem_grading_iff n (O.equiv.symm a)).mpr (by simpa using ha)
    have hb' := (O.mem_grading_iff m (O.equiv.symm b)).mpr (by simpa using hb)
    simp only [Units.smul_def, map_zsmul, LinearEquiv.apply_symm_apply,
      O.map_mul_of_mem m n _ _ hb' ha', Units.smul_def, smul_smul, ← Units.val_mul,
      ← Int.negOnePow_add, mul_comm m n, ← two_mul, Int.negOnePow_two_mul, Units.val_one, one_smul]

/-- A homomorphism of differential graded algebras induces one of their graded opposites. -/
noncomputable def oppositeHom {B C : DifferentialGradedAlgebra R} (OB : Opposite R B)
    (OC : Opposite R C) (f : B.Hom C) :
    OB.toDifferentialGradedAlgebra.Hom OC.toDifferentialGradedAlgebra := by
  let l := OC.equiv.symm.toLinearMap ∘ₗ f.toAlgebraHom.toLinearMap ∘ₗ OB.equiv.toLinearMap
  have hgrade (n : ℤ) (a : OB.toDifferentialGradedAlgebra.A)
      (ha : a ∈ OB.toDifferentialGradedAlgebra.grading n) :
      l a ∈ OC.toDifferentialGradedAlgebra.grading n := by
    apply (OC.mem_grading_iff n _).mpr
    simpa [l] using f.map_grading n _ ((OB.mem_grading_iff n a).mp ha)
  have hone : l 1 = 1 := by
    apply OC.equiv.injective
    simp [l, OB.map_one, OC.map_one]
  have hmul : ∀ a b, l (a * b) = l a * l b := by
    intro a b
    induction a using DirectSum.Decomposition.inductionOn
      OB.toDifferentialGradedAlgebra.grading with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']
    | @homogeneous n a =>
      induction b using DirectSum.Decomposition.inductionOn
        OB.toDifferentialGradedAlgebra.grading with
      | zero => simp
      | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']
      | @homogeneous m b =>
        apply OC.equiv.injective
        rw [OC.map_mul_of_mem n m _ _ (hgrade n a a.property) (hgrade m b b.property)]
        simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
          LinearEquiv.apply_symm_apply,
          OB.map_mul_of_mem n m a b a.property b.property, Units.smul_def, map_zsmul, map_mul]
  refine { toAlgebraHom := AlgHom.ofLinearMap l hone hmul, map_grading := hgrade, map_d := ?_ }
  intro a
  apply OC.equiv.injective
  simp [l, OB.map_d, OC.map_d, f.map_d]

end DifferentialGradedAlgebra
