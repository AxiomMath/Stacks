module

public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.RelativeLinearAction

/-!
# The linear action on projective space as a substitution of homogeneous coordinates

`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/RelativeLinearAction.lean` builds the action of an
invertible matrix by automorphisms of `ℙⁿ_R` by transporting the action on
`𝐏(V) = Proj (Sym_R V)` along a basis of `V`. That description is the right one for seeing that
the action is by automorphisms *over the base*, and the wrong one for seeing how the action varies
with the coefficient ring: `Sym_R V` has nothing to do with `R` in the shape the base-change
square of projective space is stated in.

This file reads the same action on the polynomial model `Proj R[T₀, …, Tₙ]`, where it is the
substitution of linear forms

`T_i ↦ ∑ⱼ M_{j i} T_j`,

and that description *is* natural in `R`: `MvPolynomial.map` of a ring homomorphism of
coefficients carries the substitution by `M` to the substitution by the matrix of images of the
entries of `M`. Combined with the naturality of the model comparison
(`Stacks.ProjectiveCohomology.projModelMap_comp_polynomialComparison_iso_inv`) this gives the
base-change compatibility of the matrix action on the library's model of projective space.

## Main definitions

* `AlgebraicGeometry.coordinateBasis`: the standard basis of `Fin (n + 1) → R`.
* `AlgebraicGeometry.matrixSubstGradedHom`: **the linear substitution of a matrix, as a graded
  ring endomorphism of `R[T₀, …, Tₙ]`.** It is defined as the conjugate of
  `SymPow.gradedSymAlgMap` by the basis comparison, so that gradedness is free; the formula on
  the coordinates is `AlgebraicGeometry.matrixSubstGradedHom_X`.

## Main results

* `AlgebraicGeometry.matrixSubstGradedHom_C` and `AlgebraicGeometry.matrixSubstGradedHom_X`: the
  substitution fixes the coefficients and sends `T_i` to `∑ⱼ M_{j i} T_j`.
* `AlgebraicGeometry.polyGradedMap_comp_matrixSubstGradedHom`: **the substitution is natural in
  the coefficient ring.**
* `AlgebraicGeometry.projMap_matrixSubstGradedHom`: `AlgebraicGeometry.Proj.map` of the
  substitution is the linear action on `𝐏(V)` read on the polynomial model.
* `AlgebraicGeometry.projectiveSpaceMatrixToAut_hom_eq`: **the matrix action on `ℙⁿ_R` is
  `AlgebraicGeometry.Proj.map` of the substitution by the inverse matrix**, conjugated by the
  comparison of the two models.
* `AlgebraicGeometry.projectiveSpaceMatrixToAut_hom_comp_projectiveSpaceOverRingMap`: **the
  matrix action on projective space is compatible with base change of the coefficient ring** —
  the automorphism attached to the matrix of images of the entries lies over the automorphism
  attached to the matrix.
* `AlgebraicGeometry.pullback_map_projectiveSpaceMatrixToAutOver`: the same read in the slice
  category, as the statement that pulling the automorphism of `ℙⁿ_R` over `Spec R` back along
  `Spec S ⟶ Spec R` gives the automorphism of `ℙⁿ_S` over `Spec S`.
* `AlgebraicGeometry.projectiveSpacePowerOverRingMap`: the base-change morphism
  `(ℙⁿ_S)^m ⟶ (ℙⁿ_R)^m` of `m`-fold self-products, with
  `AlgebraicGeometry.projectiveSpacePowerOverRingMap_comp_pi_left` identifying its coordinates
  and `AlgebraicGeometry.projectiveSpacePowerOverRingMap_comp_projectiveSpacePowerMatrixAut` its
  compatibility with the power of the matrix action.
* `AlgebraicGeometry.pullbackSectionOfRetraction`: the section of a base change attached to a
  retraction of the morphism it is taken along — the inclusion of the fibre of a family over a
  point of its base.
* `AlgebraicGeometry.pullbackSectionOfRetraction_comp_projectiveSpacePowerMatrixAut`: **the
  family of automorphisms given by a matrix over `A`, evaluated at a point of `Spec A`** — the
  fibre of the family over the point named by a retraction `γ` is the automorphism of
  `(ℙⁿ_R)^m` attached to the matrix of images of the entries under `γ`.
* `AlgebraicGeometry.pullbackSectionOfRetraction_comp_projectiveLinePowerGeneralLinearAction`:
  **the action morphism of `(GL₂)^m` on `(ℙ¹_k)^m` restricted to the fibre over a `k`-point of
  the group is the automorphism that point names.** This is the evaluation of the family of
  automorphisms that the contraction step of [Stacks, Tag 0AEM] runs on.

## Implementation notes

The substitution is *not* defined by `MvPolynomial.aeval` of linear forms, although that is what
it is. Defining it that way would leave two things to prove — that it preserves each homogeneous
piece, and that it is the conjugate of `SymPow.gradedSymAlgMap` — of which the second is needed
anyway, and the first then comes for free. So the definition is the conjugate and the formula on
the coordinates is a lemma.

`AlgebraicGeometry.Proj.map` is contravariant, and the automorphism attached to a matrix `M`
is `AlgebraicGeometry.ProjectiveSpaceOfModule.map` of the *inverse* linear map, so the matrix
appearing in `AlgebraicGeometry.projectiveSpaceMatrixToAut_hom_eq` is `M⁻¹`.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CommRingCat
open HomogeneousIdeal Graded
open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.ProjectiveCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The standard basis of `Fin (n + 1) → R`, which identifies the projective space of that
module with `ℙⁿ_R`. -/
abbrev coordinateBasis : Module.Basis (Fin (n + 1)) R (Fin (n + 1) → R) :=
  Pi.basisFun R (Fin (n + 1))

/-! ### The substitution -/

/-- **The linear substitution of a matrix, as a graded ring endomorphism of `R[T₀, …, Tₙ]`**: the
endomorphism of the symmetric algebra induced by the linear map of the matrix, conjugated by the
identification of the symmetric algebra of `Fin (n + 1) → R` with the polynomial ring. On the
coordinates it is `T_i ↦ ∑ⱼ M_{j i} T_j`, by
`AlgebraicGeometry.matrixSubstGradedHom_X`. -/
def matrixSubstGradedHom (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    polyGrading R n →+*ᵍ polyGrading R n :=
  (SymPow.gradedMvPolynomialHom (coordinateBasis R n)).comp
    ((SymPow.gradedSymAlgMap (Matrix.mulVecLin M)).comp
      (SymPow.gradedMvPolynomialInv (coordinateBasis R n)))

/-- The substitution of `M` sends a polynomial `p` to the image, under the basis comparison, of
the symmetric-algebra map of `M.mulVecLin` applied to the preimage of `p`. -/
theorem matrixSubstGradedHom_apply (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (p : MvPolynomial (Fin (n + 1)) R) :
    matrixSubstGradedHom R n M p =
      SymmetricAlgebra.equivMvPolynomial (coordinateBasis R n)
        (SymPow.symAlgMap (Matrix.mulVecLin M)
          ((SymmetricAlgebra.equivMvPolynomial (coordinateBasis R n)).symm p)) :=
  rfl

/-- The basis comparison carries a degree-one element of the symmetric algebra to the linear
form with the same coordinates. -/
theorem equivMvPolynomial_coordinateBasis_ι (v : Fin (n + 1) → R) :
    SymmetricAlgebra.equivMvPolynomial (coordinateBasis R n)
        (SymmetricAlgebra.ι R (Fin (n + 1) → R) v) =
      ∑ j, MvPolynomial.C (v j) * MvPolynomial.X j := by
  classical
  conv_lhs => rw [← (coordinateBasis R n).sum_repr v]
  simp [MvPolynomial.smul_eq_C_mul, -Pi.basisFun_apply]

/-- **The substitution fixes the coefficients.** All three factors of the definition are
homomorphisms of `R`-algebras. -/
@[simp]
theorem matrixSubstGradedHom_C (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : R) :
    matrixSubstGradedHom R n M (MvPolynomial.C r) = MvPolynomial.C r := by
  rw [matrixSubstGradedHom_apply, show (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) =
      algebraMap R (MvPolynomial (Fin (n + 1)) R) r from rfl,
    AlgEquiv.commutes, AlgHom.commutes, AlgEquiv.commutes]

/-- **The substitution sends the `i`-th coordinate to the `i`-th column of the matrix read as a
linear form.** -/
@[simp]
theorem matrixSubstGradedHom_X (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    matrixSubstGradedHom R n M (MvPolynomial.X i) =
      ∑ j, MvPolynomial.C (M j i) * MvPolynomial.X j := by
  classical
  rw [matrixSubstGradedHom_apply, SymmetricAlgebra.equivMvPolynomial_symm_X,
    SymPow.symAlgMap_ι, equivMvPolynomial_coordinateBasis_ι]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  simp

/-! ### The substitution is natural in the coefficient ring -/

section Natural

variable (S : Type u) [CommRing S]

/-- **The linear substitution of a matrix is natural in the coefficient ring.**
`MvPolynomial.map` of a ring homomorphism of coefficients carries the substitution by `M` to the
substitution by the matrix of images of the entries of `M`: both are ring homomorphisms out of a
polynomial ring, and they agree on the constants and on each coordinate. -/
theorem polyGradedMap_comp_matrixSubstGradedHom (φ : R →+* S)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (polyGradedMap (Fin (n + 1)) φ).comp (matrixSubstGradedHom R n M) =
      (matrixSubstGradedHom S n (M.map φ)).comp (polyGradedMap (Fin (n + 1)) φ) := by
  classical
  refine GradedRingHom.ext fun p => ?_
  induction p using MvPolynomial.induction_on with
  | C r =>
    show MvPolynomial.map φ (matrixSubstGradedHom R n M (MvPolynomial.C r)) =
      matrixSubstGradedHom S n (M.map φ) (MvPolynomial.map φ (MvPolynomial.C r))
    rw [matrixSubstGradedHom_C, MvPolynomial.map_C, matrixSubstGradedHom_C]
  | add p q hp hq =>
    show MvPolynomial.map φ (matrixSubstGradedHom R n M (p + q)) =
      matrixSubstGradedHom S n (M.map φ) (MvPolynomial.map φ (p + q))
    change MvPolynomial.map φ (matrixSubstGradedHom R n M p) =
      matrixSubstGradedHom S n (M.map φ) (MvPolynomial.map φ p) at hp
    change MvPolynomial.map φ (matrixSubstGradedHom R n M q) =
      matrixSubstGradedHom S n (M.map φ) (MvPolynomial.map φ q) at hq
    rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    show MvPolynomial.map φ (matrixSubstGradedHom R n M (p * MvPolynomial.X i)) =
      matrixSubstGradedHom S n (M.map φ) (MvPolynomial.map φ (p * MvPolynomial.X i))
    change MvPolynomial.map φ (matrixSubstGradedHom R n M p) =
      matrixSubstGradedHom S n (M.map φ) (MvPolynomial.map φ p) at hp
    rw [map_mul, map_mul, map_mul, map_mul, hp, matrixSubstGradedHom_X, MvPolynomial.map_X,
      matrixSubstGradedHom_X, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

end Natural

/-! ### The substitution computes the linear action -/

/-- The containment of irrelevant ideals for the symmetric-algebra map of an invertible matrix. -/
private theorem irrelevant_le_map_gradedSymAlgMap_mulVecLin
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    (fun i => SymPow.symmetricPower i R (Fin (n + 1) → R))₊ ≤
      (fun i => SymPow.symmetricPower i R (Fin (n + 1) → R))₊.map
        (SymPow.gradedSymAlgMap
          (Matrix.mulVecLin (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R))) := by
  rw [← Matrix.GeneralLinearGroup.coe_toLin]
  exact ProjectiveSpaceOfModule.irrelevant_le_map_gradedSymAlgMap R (Fin (n + 1) → R)
    (Matrix.GeneralLinearGroup.toLin M)

/-- The containment of irrelevant ideals for the substitution by an invertible matrix: each of the
three factors of the definition satisfies it. -/
theorem irrelevant_le_map_matrixSubstGradedHom
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    (polyGrading R n)₊ ≤ (polyGrading R n)₊.map
      (matrixSubstGradedHom R n (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) := by
  have h2 := irrelevant_le_map_gradedSymAlgMap_mulVecLin R n M
  exact HomogeneousIdeal.irrelevant_le_map_comp
    (HomogeneousIdeal.irrelevant_le_map_comp
      (irrelevant_le_map_gradedMvPolynomialInv (coordinateBasis R n)) h2)
    (irrelevant_le_map_gradedMvPolynomialHom (coordinateBasis R n))

/-- The inverse of the basis comparison between `𝐏(V)` and the polynomial model is
`AlgebraicGeometry.Proj.map` of the comparison of graded rings in the other direction. -/
theorem projectiveSpaceOfModuleIsoProjMvPolynomial_inv_coordinateBasis :
    (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).inv =
      Proj.map (SymPow.gradedMvPolynomialHom (coordinateBasis R n))
        (irrelevant_le_map_gradedMvPolynomialHom (coordinateBasis R n)) := by
  have key : (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).hom ≫
      Proj.map (SymPow.gradedMvPolynomialHom (coordinateBasis R n))
        (irrelevant_le_map_gradedMvPolynomialHom (coordinateBasis R n)) = 𝟙 _ := by
    rw [projectiveSpaceOfModuleIsoProjMvPolynomial_hom, ← Proj.map_comp]
    exact (Proj_map_congr _ _ _ _
      (SymPow.gradedMvPolynomialInv_comp_hom (coordinateBasis R n))).trans Proj.map_id
  calc (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).inv
      = (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).inv ≫ 𝟙 _ :=
        (Category.comp_id _).symm
    _ = _ := by rw [← key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **`AlgebraicGeometry.Proj.map` of the substitution by a matrix is the linear action on
`𝐏(V)`, read on the polynomial model.** -/
theorem projMap_matrixSubstGradedHom (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    Proj.map (matrixSubstGradedHom R n (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R))
        (irrelevant_le_map_matrixSubstGradedHom R n M) =
      (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).inv ≫
        ProjectiveSpaceOfModule.map R (Fin (n + 1) → R)
          (Matrix.GeneralLinearGroup.toLin M) ≫
        (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).hom := by
  have h2 := irrelevant_le_map_gradedSymAlgMap_mulVecLin R n M
  have hassoc : matrixSubstGradedHom R n (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
      ((SymPow.gradedMvPolynomialHom (coordinateBasis R n)).comp
          (SymPow.gradedSymAlgMap
            (Matrix.mulVecLin (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)))).comp
        (SymPow.gradedMvPolynomialInv (coordinateBasis R n)) :=
    GradedRingHom.ext fun _ => rfl
  have haction : Proj.map (SymPow.gradedSymAlgMap
        (Matrix.mulVecLin (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R))) h2 =
      ProjectiveSpaceOfModule.map R (Fin (n + 1) → R)
        (Matrix.GeneralLinearGroup.toLin M) :=
    Proj_map_congr _ _ _ _ (congrArg SymPow.gradedSymAlgMap
      (Matrix.GeneralLinearGroup.coe_toLin M).symm)
  rw [Proj_map_congr _ _ _ (HomogeneousIdeal.irrelevant_le_map_comp
      (irrelevant_le_map_gradedMvPolynomialInv (coordinateBasis R n))
      (HomogeneousIdeal.irrelevant_le_map_comp h2
        (irrelevant_le_map_gradedMvPolynomialHom (coordinateBasis R n)))) hassoc,
    Proj.map_comp _ _ (irrelevant_le_map_gradedMvPolynomialInv (coordinateBasis R n))
      (HomogeneousIdeal.irrelevant_le_map_comp h2
        (irrelevant_le_map_gradedMvPolynomialHom (coordinateBasis R n))),
    Proj.map_comp _ _ h2 (irrelevant_le_map_gradedMvPolynomialHom (coordinateBasis R n)),
    projectiveSpaceOfModuleIsoProjMvPolynomial_inv_coordinateBasis,
    projectiveSpaceOfModuleIsoProjMvPolynomial_hom, haction, Category.assoc]

/-! ### The matrix action on the library's model of projective space -/

section Model

/-- The identification of `𝐏(Fin (n + 1) → R)` with `ℙⁿ_R` underlying the matrix action is the
comparison with the polynomial model followed by the comparison of the two models of projective
`n`-space. -/
theorem projectiveSpaceOfModuleIso_coordinateBasis_hom :
    (projectiveSpaceOfModuleIso (coordinateBasis R n)).hom =
      (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).hom ≫
        (polynomialComparison R n).iso.inv :=
  rfl

/-- The inverse of the identification of `AlgebraicGeometry.projectiveSpaceOfModuleIso`. -/
theorem projectiveSpaceOfModuleIso_coordinateBasis_inv :
    (projectiveSpaceOfModuleIso (coordinateBasis R n)).inv =
      (polynomialComparison R n).iso.hom ≫
        (projectiveSpaceOfModuleIsoProjMvPolynomial (coordinateBasis R n)).inv :=
  rfl

/-- `Stacks.ProjectiveCohomology.projModelMap` is `AlgebraicGeometry.Proj.map` of the graded
homomorphism of a change of coefficients, spelled so that the composition law applies to it. -/
theorem projModelMap_eq_projMap (S : Type u) [CommRing S] (φ : R →+* S) :
    projModelMap n φ = Proj.map (polyGradedMap (Fin (n + 1)) φ)
      (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ) :=
  rfl

/-- **The matrix action on `ℙⁿ_R` is `AlgebraicGeometry.Proj.map` of the substitution by the
inverse matrix**, conjugated by the comparison of the two models of projective `n`-space. The
inverse appears because `AlgebraicGeometry.Proj.map` is contravariant. -/
theorem projectiveSpaceMatrixToAut_hom_eq (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    (projectiveSpaceMatrixToAut R n M).asIso.hom =
      (polynomialComparison R n).iso.hom ≫
        Proj.map (matrixSubstGradedHom R n
            ((M⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) R))
          (irrelevant_le_map_matrixSubstGradedHom R n M⁻¹) ≫
        (polynomialComparison R n).iso.inv := by
  have hinv : ((Matrix.GeneralLinearGroup.toLin M)⁻¹ :
      LinearMap.GeneralLinearGroup R (Fin (n + 1) → R)) =
      Matrix.GeneralLinearGroup.toLin M⁻¹ :=
    (map_inv Matrix.GeneralLinearGroup.toLin M).symm
  rw [show (projectiveSpaceMatrixToAut R n M).asIso.hom = _ from
      projectiveSpaceLinearToAut_hom (coordinateBasis R n) (Matrix.GeneralLinearGroup.toLin M),
    hinv, projectiveSpaceOfModuleIso_coordinateBasis_inv,
    projectiveSpaceOfModuleIso_coordinateBasis_hom, projMap_matrixSubstGradedHom]
  simp only [Category.assoc]

/-- The substitution by a matrix and the substitution by the matrix of its images commute with
the morphism of polynomial models induced by the coefficient homomorphism. -/
theorem projMap_matrixSubstGradedHom_comp_projModelMap (S : Type u) [CommRing S] (φ : R →+* S)
    (N : Matrix.GeneralLinearGroup (Fin (n + 1)) R)
    (N' : Matrix.GeneralLinearGroup (Fin (n + 1)) S)
    (hN : (N' : Matrix (Fin (n + 1)) (Fin (n + 1)) S) =
      (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R).map φ) :
    Proj.map (matrixSubstGradedHom S n (N' : Matrix (Fin (n + 1)) (Fin (n + 1)) S))
          (irrelevant_le_map_matrixSubstGradedHom S n N') ≫
        projModelMap n φ =
      projModelMap n φ ≫
        Proj.map (matrixSubstGradedHom R n (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R))
          (irrelevant_le_map_matrixSubstGradedHom R n N) := by
  rw [projModelMap_eq_projMap R n S φ, ← Proj.map_comp, ← Proj.map_comp]
  refine Proj_map_congr _ _ _ _ ?_
  rw [hN]
  exact (polyGradedMap_comp_matrixSubstGradedHom R n S φ
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)).symm

/-- **The matrix action on projective `n`-space is compatible with base change of the coefficient
ring.** The automorphism of `ℙⁿ_S` attached to the matrix of images of the entries of `M` lies
over the automorphism of `ℙⁿ_R` attached to `M`.

This is what lets the action of the generic matrix over the coordinate ring of the general linear
group be *evaluated*: specializing along a point of the group is a base change of the coefficient
ring, and this says the generic automorphism specializes to the automorphism that point names. -/
theorem projectiveSpaceMatrixToAut_hom_comp_projectiveSpaceOverRingMap
    (S : Type u) [CommRing S] (φ : R →+* S)
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    (projectiveSpaceMatrixToAut S n (Matrix.GeneralLinearGroup.map φ M)).asIso.hom ≫
        projectiveSpaceOverRingMap n (ofHom φ) =
      projectiveSpaceOverRingMap n (ofHom φ) ≫ (projectiveSpaceMatrixToAut R n M).asIso.hom := by
  have hN : (((Matrix.GeneralLinearGroup.map φ M)⁻¹ :
        Matrix.GeneralLinearGroup (Fin (n + 1)) S) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) S) =
      ((M⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R).map φ := by
    rw [← map_inv (Matrix.GeneralLinearGroup.map φ) M]
    rfl
  have key := projMap_matrixSubstGradedHom_comp_projModelMap R n S φ M⁻¹
    (Matrix.GeneralLinearGroup.map φ M)⁻¹ hN
  have hρ : (polynomialComparison S n).iso.hom ≫ projModelMap n φ ≫
      (polynomialComparison R n).iso.inv = projectiveSpaceOverRingMap n (ofHom φ) := by
    rw [Stacks.ProjectiveCohomology.projModelMap_comp_polynomialComparison_iso_inv R S n φ,
      Iso.hom_inv_id_assoc]
  rw [projectiveSpaceMatrixToAut_hom_eq, projectiveSpaceMatrixToAut_hom_eq, ← hρ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  refine congrArg (fun u => (polynomialComparison S n).iso.hom ≫ u) ?_
  rw [← Category.assoc, key, Category.assoc]

/-! ### The matrix action in the slice category, under base change -/

section OverBaseChange

/-- **A commuting square of automorphisms over a cartesian square descends to the fibre
product.** If `X` is the fibre product of `pY : Y ⟶ T` and `b : T' ⟶ T` through `ρ` and `pX`, if
`u` is an endomorphism of the fibre product lying over `aY` and fixing the projection to `T'`,
and if `aX` is an endomorphism of `X` lying over `aY` and fixing `pX`, then `u` *is* `aX` read on
the fibre product.

Both sides are morphisms into the fibre product, so it is enough to compare the two
projections. -/
private theorem comp_isoPullback_inv_eq {X Y T T' : Scheme.{u}} (ρ : X ⟶ Y) (pX : X ⟶ T')
    (pY : Y ⟶ T) (b : T' ⟶ T) [HasPullback pY b]
    (e : X ≅ pullback pY b) (hef : e.hom ≫ pullback.fst pY b = ρ)
    (hes : e.hom ≫ pullback.snd pY b = pX)
    (u : pullback pY b ⟶ pullback pY b) (aX : X ⟶ X) (aY : Y ⟶ Y)
    (huf : u ≫ pullback.fst pY b = pullback.fst pY b ≫ aY)
    (hus : u ≫ pullback.snd pY b = pullback.snd pY b)
    (haρ : aX ≫ ρ = ρ ≫ aY) (hap : aX ≫ pX = pX) :
    u ≫ e.inv = e.inv ≫ aX := by
  refine (cancel_mono e.hom).mp (pullback.hom_ext ?_ ?_)
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hef, huf, haρ, ← hef, Category.assoc, Iso.inv_hom_id_assoc]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [hes, hus, hap, ← hes, Iso.inv_hom_id_assoc]

variable (S : Type u) [CommRing S] (φ : R →+* S)

/-- The matrix action read in the slice category is the matrix action. -/
theorem projectiveSpaceMatrixToAutOver_hom_left
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    (projectiveSpaceMatrixToAutOver R n M).asIso.hom.left =
      (projectiveSpaceMatrixToAut R n M).asIso.hom :=
  rfl

/-- The identification of the base change of `ℙⁿ_R` with `ℙⁿ_S` is the inverse of the comparison
with the fibre product. -/
theorem projectiveSpacePullbackIso_hom_left :
    (projectiveSpacePullbackIso φ n).hom.left =
      (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback.inv :=
  rfl

/-- The pullback of the matrix action along `Spec S ⟶ Spec R` lies over the matrix action. -/
theorem pullback_map_projectiveSpaceMatrixToAutOver_left_comp_fst
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    ((Over.pullback (Spec.map (ofHom φ))).map
          (projectiveSpaceMatrixToAutOver R n M).asIso.hom).left ≫
        pullback.fst (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R)) (Spec.map (ofHom φ)) =
      pullback.fst (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R)) (Spec.map (ofHom φ)) ≫
        (projectiveSpaceMatrixToAut R n M).asIso.hom :=
  pullback.lift_fst _ _ _

/-- The pullback of the matrix action along `Spec S ⟶ Spec R` is a morphism over `Spec S`. -/
theorem pullback_map_projectiveSpaceMatrixToAutOver_left_comp_snd
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    ((Over.pullback (Spec.map (ofHom φ))).map
          (projectiveSpaceMatrixToAutOver R n M).asIso.hom).left ≫
        pullback.snd (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R)) (Spec.map (ofHom φ)) =
      pullback.snd (projectiveSpaceOverRing n (.of R) ↘ Spec (.of R)) (Spec.map (ofHom φ)) :=
  pullback.lift_snd _ _ _

/-- The underlying morphism of schemes of the base-change compatibility of the matrix action in
the slice category. -/
theorem pullback_map_projectiveSpaceMatrixToAutOver_left
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    ((Over.pullback (Spec.map (ofHom φ))).map
          (projectiveSpaceMatrixToAutOver R n M).asIso.hom).left ≫
        (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback.inv =
      (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback.inv ≫
        (projectiveSpaceMatrixToAut S n (Matrix.GeneralLinearGroup.map φ M)).asIso.hom :=
  comp_isoPullback_inv_eq _ _ _ _ _
    (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback_hom_fst
    (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback_hom_snd _ _ _
    (pullback_map_projectiveSpaceMatrixToAutOver_left_comp_fst R n S φ M)
    (pullback_map_projectiveSpaceMatrixToAutOver_left_comp_snd R n S φ M)
    (projectiveSpaceMatrixToAut_hom_comp_projectiveSpaceOverRingMap R n S φ M)
    (projectiveSpaceMatrixToAut_hom_comp_structureMorphism S n
      (Matrix.GeneralLinearGroup.map φ M))

/-- **The matrix action read in the slice category is compatible with base change.** Pulling the
automorphism of `ℙⁿ_R` over `Spec R` back along `Spec S ⟶ Spec R` and transporting it along the
identification of the base change with `ℙⁿ_S` gives the automorphism of `ℙⁿ_S` over `Spec S`
attached to the matrix of images of the entries.

`ℙⁿ_S` is the base change, so a morphism to it is determined by its two components; on the
component over `ℙⁿ_R` this is
`AlgebraicGeometry.projectiveSpaceMatrixToAut_hom_comp_projectiveSpaceOverRingMap` and on the
component over `Spec S` it is
`AlgebraicGeometry.projectiveSpaceMatrixToAut_hom_comp_structureMorphism`. -/
theorem pullback_map_projectiveSpaceMatrixToAutOver
    (M : Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    (Over.pullback (Spec.map (ofHom φ))).map (projectiveSpaceMatrixToAutOver R n M).asIso.hom ≫
        (projectiveSpacePullbackIso φ n).hom =
      (projectiveSpacePullbackIso φ n).hom ≫
        (projectiveSpaceMatrixToAutOver S n (Matrix.GeneralLinearGroup.map φ M)).asIso.hom :=
  Over.OverMorphism.ext (pullback_map_projectiveSpaceMatrixToAutOver_left R n S φ M)

end OverBaseChange

/-! ### The power action under base change -/

section PowerBaseChange

variable (S : Type u) [CommRing S] (φ : R →+* S) (m : ℕ)

/-- The identification of the base change of a power of `ℙⁿ` with the power of the base change,
written as a composite: the comparison with the product of the base changes, followed by the
factorwise identification. -/
theorem projectiveSpacePowerPullbackIso_hom_eq :
    (projectiveSpacePowerPullbackIso φ n m).hom =
      Limits.piComparison (Over.pullback (Spec.map (ofHom φ)))
          (fun _ : Fin m => (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) ≫
        (Pi.mapIso fun _ : Fin m => projectiveSpacePullbackIso φ n).hom :=
  rfl

/-- The `i`-th coordinate of the identification of the base change of a power of `ℙⁿ` with the
power of the base change is the base change of the `i`-th coordinate. -/
theorem projectiveSpacePowerPullbackIso_hom_π (i : Fin m) :
    (projectiveSpacePowerPullbackIso φ n m).hom ≫
        Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of S)).asOver (Spec (.of S))) i =
      (Over.pullback (Spec.map (ofHom φ))).map
          (Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i) ≫
        (projectiveSpacePullbackIso φ n).hom := by
  rw [projectiveSpacePowerPullbackIso_hom_eq, Category.assoc, Pi.mapIso_hom_π,
    ← Category.assoc, Limits.piComparison_comp_π]

/-- **The action of a power of the general linear group on a power of projective space is
compatible with base change of the coefficient ring.** Both sides are morphisms into a product,
so it is enough to compare their coordinates, and in each coordinate the statement is the
single-factor compatibility
`AlgebraicGeometry.pullback_map_projectiveSpaceMatrixToAutOver`. -/
theorem pullback_map_projectiveSpacePowerMatrixAut
    (M : Fin m → Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    (Over.pullback (Spec.map (ofHom φ))).map (projectiveSpacePowerMatrixAut R n m M).asIso.hom ≫
        (projectiveSpacePowerPullbackIso φ n m).hom =
      (projectiveSpacePowerPullbackIso φ n m).hom ≫
        (projectiveSpacePowerMatrixAut S n m
          (fun i => Matrix.GeneralLinearGroup.map φ (M i))).asIso.hom := by
  refine Pi.hom_ext _ _ fun i => ?_
  have hl : ((Over.pullback (Spec.map (ofHom φ))).map
          (projectiveSpacePowerMatrixAut R n m M).asIso.hom ≫
        (projectiveSpacePowerPullbackIso φ n m).hom) ≫
        Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of S)).asOver (Spec (.of S))) i =
      (Over.pullback (Spec.map (ofHom φ))).map
          (Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i) ≫
        (projectiveSpacePullbackIso φ n).hom ≫
          (projectiveSpaceMatrixToAutOver S n
            (Matrix.GeneralLinearGroup.map φ (M i))).asIso.hom := by
    rw [Category.assoc, projectiveSpacePowerPullbackIso_hom_π, ← Category.assoc,
      ← Functor.map_comp, projectiveSpacePowerMatrixAut_hom_π, Functor.map_comp,
      Category.assoc, pullback_map_projectiveSpaceMatrixToAutOver]
  have hr : ((projectiveSpacePowerPullbackIso φ n m).hom ≫
        (projectiveSpacePowerMatrixAut S n m
          (fun j => Matrix.GeneralLinearGroup.map φ (M j))).asIso.hom) ≫
        Pi.π (fun _ : Fin m => (projectiveSpaceOverRing n (.of S)).asOver (Spec (.of S))) i =
      (Over.pullback (Spec.map (ofHom φ))).map
          (Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i) ≫
        (projectiveSpacePullbackIso φ n).hom ≫
          (projectiveSpaceMatrixToAutOver S n
            (Matrix.GeneralLinearGroup.map φ (M i))).asIso.hom := by
    rw [Category.assoc, projectiveSpacePowerMatrixAut_hom_π, ← Category.assoc,
      projectiveSpacePowerPullbackIso_hom_π, Category.assoc]
  exact hl.trans hr.symm

end PowerBaseChange

/-! ### The base-change morphism of a power of projective space -/

section PowerOverRingMap

/-! The rearrangements below are stated for arbitrary morphisms of an arbitrary category on
purpose. The objects that occur in this file — the underlying object of a product taken in a
slice category, the underlying object of a base change — are reducible only through several
definitions, and a rewrite whose pattern has to be matched against them fails on the
transparency used for the motive. With the data abstracted into variables there is nothing to
unfold, and the rearranged identity is then applied by `exact`, which is not restricted in that
way. -/

/-- Two morphisms into the underlying object of a product taken in a slice category agree as
soon as both lie over one and the same morphism to the base and they agree after every
projection: they are then the underlying morphisms of two morphisms of the slice category, and
those are compared by the universal property of the product. -/
private theorem eq_of_comp_pi_left {C : Type*} [Category C] {Y : C} {ι : Type*}
    (D : ι → Over Y) [HasProduct D] {X : C} (x : X ⟶ Y)
    (u v : X ⟶ (∏ᶜ D).left) (hu : u ≫ (∏ᶜ D).hom = x) (hv : v ≫ (∏ᶜ D).hom = x)
    (hπ : ∀ i, u ≫ (Pi.π D i).left = v ≫ (Pi.π D i).left) : u = v := by
  have h : (Over.homMk u hu : Over.mk x ⟶ ∏ᶜ D) = Over.homMk v hv :=
    Pi.hom_ext _ _ fun i => Over.OverMorphism.ext (hπ i)
  exact congrArg Over.Hom.left h

/-- Transporting a commutation relation `u ≫ p = p ≫ x` along `b` with `b ≫ p = q ≫ c`. -/
private theorem comp_left_comm {C : Type*} [Category C] {W X Y Z : C}
    (b : W ⟶ X) (u : X ⟶ X) (p : X ⟶ Y) (q : W ⟶ Z) (c : Z ⟶ Y) (x : Y ⟶ Y)
    (h1 : u ≫ p = p ≫ x) (h2 : b ≫ p = q ≫ c) :
    (b ≫ u) ≫ p = q ≫ c ≫ x := by
  rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc]

/-- The same rearrangement with the commuting morphism on the other side of `b`. -/
private theorem comp_right_comm {C : Type*} [Category C] {W X Y Z : C}
    (b : W ⟶ X) (v : W ⟶ W) (p : X ⟶ Y) (q : W ⟶ Z) (c : Z ⟶ Y) (y : Z ⟶ Z) (x : Y ⟶ Y)
    (h1 : v ≫ q = q ≫ y) (h2 : b ≫ p = q ≫ c) (h3 : y ≫ c = c ≫ x) :
    (v ≫ b) ≫ p = q ≫ c ≫ x := by
  rw [Category.assoc, h2, ← Category.assoc, h1, Category.assoc, h3]

/-- Two mutually inverse base-change morphisms compose to the identity, coordinatewise. -/
private theorem comp_comp_eq_id_comp {C : Type*} [Category C] {W X Y Z : C}
    (b : W ⟶ X) (b' : X ⟶ W) (p : W ⟶ Y) (q : X ⟶ Z) (c : Z ⟶ Y) (c' : Y ⟶ Z)
    (h1 : b' ≫ p = q ≫ c) (h2 : b ≫ q = p ≫ c') (h3 : c' ≫ c = 𝟙 Y) :
    (b ≫ b') ≫ p = 𝟙 W ≫ p := by
  rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc, h3, Category.comp_id,
    Category.id_comp]

/-- Cancelling an isomorphism on the right. -/
private theorem comp_inv_eq_of_eq_comp_hom {C : Type*} [Category C] {X Y Z : C} (e : Y ≅ Z)
    (f : X ⟶ Z) (g : X ⟶ Y) (h : f = g ≫ e.hom) : f ≫ e.inv = g := by
  rw [h, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- A four-fold rearrangement. -/
private theorem comp_comp_comp_comp_eq {C : Type*} [Category C] {V W X Y Z : C}
    (a : V ⟶ W) (b : W ⟶ X) (e : X ⟶ Y) (p : Y ⟶ Z) (f : X ⟶ Z) (r : W ⟶ Z)
    (h1 : e ≫ p = f) (h2 : b ≫ f = r) : ((a ≫ b) ≫ e) ≫ p = a ≫ r := by
  rw [Category.assoc, Category.assoc, h1, h2]

/-- The same rearrangement when the two inner morphisms cancel. -/
private theorem comp_comp_comp_comp_eq_left {C : Type*} [Category C] {V W X Y : C}
    (a : V ⟶ W) (b : W ⟶ X) (e : X ⟶ Y) (p : Y ⟶ W) (f : X ⟶ W)
    (h1 : e ≫ p = f) (h2 : b ≫ f = 𝟙 W) : ((a ≫ b) ≫ e) ≫ p = a := by
  rw [Category.assoc, Category.assoc, h1, h2, Category.comp_id]

/-- Reassociating the five-fold composite the specialization of the family produces. -/
private theorem comp_specialize {C : Type*} [Category C] {W X Y : C}
    (s : W ⟶ X) (f : X ⟶ Y) (u : Y ⟶ Y) (g : Y ⟶ X) (k : X ⟶ W)
    (b : W ⟶ Y) (b' : Y ⟶ W) (v : W ⟶ W)
    (hb : s ≫ f = b) (hb' : g ≫ k = b') (hcomm : b ≫ u = v ≫ b) (hid : b ≫ b' = 𝟙 W) :
    s ≫ f ≫ u ≫ g ≫ k = v := by
  rw [← Category.assoc s f, hb, hb', ← Category.assoc b u b', hcomm, Category.assoc, hid,
    Category.comp_id]

variable (S : Type u) [CommRing S] (φ : R →+* S) (m : ℕ)

/-- **The `m`-fold self-product of `ℙⁿ` is stable under base change, read as a morphism of
schemes `(ℙⁿ_S)^m ⟶ (ℙⁿ_R)^m`**: the identification of the self-product over `S` with the base
change of the self-product over `R`, followed by the projection of that base change. -/
noncomputable def projectiveSpacePowerOverRingMap :
    (projectiveSpacePowerOver S n m).left ⟶ (projectiveSpacePowerOver R n m).left :=
  (projectiveSpacePowerPullbackIso φ n m).inv.left ≫
    pullback.fst (projectiveSpacePowerOver R n m).hom (Spec.map (ofHom φ))

/-- The inverse of the identification of the base change of `ℙⁿ_R` with `ℙⁿ_S` is the comparison
with the fibre product. -/
theorem projectiveSpacePullbackIso_inv_left :
    (projectiveSpacePullbackIso φ n).inv.left =
      (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback.hom :=
  rfl

/-- **The single-factor base-change morphism, read off the identification of the base change.**
Composing the comparison with the fibre product with the projection to `ℙⁿ_R` gives the
base-change morphism `ℙⁿ_S ⟶ ℙⁿ_R`. -/
theorem projectiveSpacePullbackIso_inv_left_comp_fst :
    (projectiveSpacePullbackIso φ n).inv.left ≫
        pullback.fst ((projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))).hom
          (Spec.map (ofHom φ)) =
      projectiveSpaceOverRingMap n (ofHom φ) :=
  (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom φ))).isoPullback_hom_fst

/-- **The base-change morphism of a power lies over the morphism of base schemes.** -/
theorem projectiveSpacePowerOverRingMap_comp_hom :
    projectiveSpacePowerOverRingMap R n S φ m ≫ (projectiveSpacePowerOver R n m).hom =
      (projectiveSpacePowerOver S n m).hom ≫ Spec.map (ofHom φ) := by
  rw [projectiveSpacePowerOverRingMap, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun u => u ≫ Spec.map (ofHom φ))
    (Over.w (projectiveSpacePowerPullbackIso φ n m).inv)

/-- **The base-change morphism of a power is the single-factor base-change morphism in every
coordinate.** This is the defining property of
`AlgebraicGeometry.projectiveSpacePowerOverRingMap`, and it is what reduces every statement
about the power to the corresponding statement about one factor. -/
theorem projectiveSpacePowerOverRingMap_comp_pi_left (i : Fin m) :
    projectiveSpacePowerOverRingMap R n S φ m ≫
        (Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i).left =
      (Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of S)).asOver (Spec (.of S))) i).left ≫
        projectiveSpaceOverRingMap n (ofHom φ) := by
  have hπ := projectiveSpacePowerPullbackIso_hom_π R n S φ m i
  have hmove : (projectiveSpacePowerPullbackIso φ n m).inv ≫
      (Over.pullback (Spec.map (ofHom φ))).map
        (Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i) =
      Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of S)).asOver (Spec (.of S))) i ≫
        (projectiveSpacePullbackIso φ n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hπ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hleft := congrArg
    (fun u => Over.Hom.left u ≫ pullback.fst
      ((projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))).hom (Spec.map (ofHom φ)))
    hmove
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst] at hleft
  rw [projectiveSpacePullbackIso_inv_left_comp_fst R n S φ] at hleft
  rw [projectiveSpacePowerOverRingMap, Category.assoc]
  exact hleft

/-- **The base-change morphism of a power is compatible with the power of the matrix action.**
Both sides are morphisms into a product, so it is enough to compare their coordinates, and in
each coordinate this is
`AlgebraicGeometry.projectiveSpaceMatrixToAut_hom_comp_projectiveSpaceOverRingMap`. -/
theorem projectiveSpacePowerOverRingMap_comp_projectiveSpacePowerMatrixAut
    (M : Fin m → Matrix.GeneralLinearGroup (Fin (n + 1)) R) :
    projectiveSpacePowerOverRingMap R n S φ m ≫
        (projectiveSpacePowerMatrixAut R n m M).asIso.hom.left =
      (projectiveSpacePowerMatrixAut S n m
          (fun i => Matrix.GeneralLinearGroup.map φ (M i))).asIso.hom.left ≫
        projectiveSpacePowerOverRingMap R n S φ m := by
  refine eq_of_comp_pi_left _ ((projectiveSpacePowerOver S n m).hom ≫ Spec.map (ofHom φ)) _ _
    ?_ ?_ ?_
  · rw [Category.assoc, Over.w (projectiveSpacePowerMatrixAut R n m M).asIso.hom,
      projectiveSpacePowerOverRingMap_comp_hom]
  · rw [Category.assoc, projectiveSpacePowerOverRingMap_comp_hom, ← Category.assoc,
      Over.w (projectiveSpacePowerMatrixAut S n m
        (fun i => Matrix.GeneralLinearGroup.map φ (M i))).asIso.hom]
  · intro i
    have hR := congrArg Over.Hom.left (projectiveSpacePowerMatrixAut_hom_π R n m M i)
    have hS := congrArg Over.Hom.left (projectiveSpacePowerMatrixAut_hom_π S n m
      (fun j => Matrix.GeneralLinearGroup.map φ (M j)) i)
    simp only [Over.comp_left, projectiveSpaceMatrixToAutOver_hom_left] at hR hS
    exact (comp_left_comm _ _ _ _ _ _ hR
        (projectiveSpacePowerOverRingMap_comp_pi_left R n S φ m i)).trans
      (comp_right_comm _ _ _ _ _ _ _ hS
        (projectiveSpacePowerOverRingMap_comp_pi_left R n S φ m i)
        (projectiveSpaceMatrixToAut_hom_comp_projectiveSpaceOverRingMap R n S φ (M i))).symm

end PowerOverRingMap

/-! ### Specializing the family at a point of the base -/

section Specialize

/-- **A retraction determines a section of a base change.** If `b : Y ⟶ X` is a section of
`a : X ⟶ Y`, then for every `P` over `Y` the projection of the base change of `P` along `a` has
a section, with components the identity of `P` and `b`. -/
noncomputable def pullbackSectionOfRetraction {C : Type*} [Category C] [HasPullbacks C]
    {X Y : C} (P : Over Y) (a : X ⟶ Y) (b : Y ⟶ X) (hab : b ≫ a = 𝟙 Y) :
    P.left ⟶ ((Over.pullback a).obj P).left :=
  pullback.lift (𝟙 P.left) (P.hom ≫ b)
    (by rw [Category.id_comp, Category.assoc, hab, Category.comp_id])

/-- The section attached to a retraction is a section of the projection. -/
theorem pullbackSectionOfRetraction_comp_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y : C} (P : Over Y) (a : X ⟶ Y) (b : Y ⟶ X) (hab : b ≫ a = 𝟙 Y) :
    pullbackSectionOfRetraction P a b hab ≫ pullback.fst P.hom a = 𝟙 P.left :=
  pullback.lift_fst _ _ _

/-- The second component of the section attached to a retraction is the retraction. -/
theorem pullbackSectionOfRetraction_comp_snd {C : Type*} [Category C] [HasPullbacks C]
    {X Y : C} (P : Over Y) (a : X ⟶ Y) (b : Y ⟶ X) (hab : b ≫ a = 𝟙 Y) :
    pullbackSectionOfRetraction P a b hab ≫ pullback.snd P.hom a = P.hom ≫ b :=
  pullback.lift_snd _ _ _

variable {A : Type u} [CommRing A] (α : R →+* A) (γ : A →+* R)
  (hγ : γ.comp α = RingHom.id R) (m : ℕ)

include hγ in
/-- A ring-theoretic retraction gives a section of the morphism of spectra. -/
theorem specMap_comp_specMap_eq_id :
    Spec.map (ofHom γ) ≫ Spec.map (ofHom α) = 𝟙 (Spec (CommRingCat.of R)) := by
  have h : CommRingCat.ofHom α ≫ CommRingCat.ofHom γ = 𝟙 (CommRingCat.of R) := by
    rw [← CommRingCat.ofHom_comp, hγ]
    exact CommRingCat.ofHom_id
  rw [← Spec.map_comp, h, Spec.map_id]

include hγ in
/-- **Base change of `ℙⁿ` along a retraction undoes base change along the morphism it
retracts**: `AlgebraicGeometry.projectiveSpaceOverMap` is functorial, and the composite of the
two morphisms of base schemes is the identity. -/
theorem projectiveSpaceOverRingMap_comp_self :
    projectiveSpaceOverRingMap n (ofHom γ) ≫ projectiveSpaceOverRingMap n (ofHom α) =
      𝟙 (projectiveSpaceOverRing n (CommRingCat.of R)) := by
  rw [projectiveSpaceOverRingMap_eq, projectiveSpaceOverRingMap_eq,
    projectiveSpaceOverMap_comp, specMap_comp_specMap_eq_id R α γ hγ,
    projectiveSpaceOverMap_id]

include hγ in
/-- **Base change of a power of `ℙⁿ` along a retraction undoes base change along the morphism it
retracts.** -/
theorem projectiveSpacePowerOverRingMap_comp_self :
    projectiveSpacePowerOverRingMap A n R γ m ≫ projectiveSpacePowerOverRingMap R n A α m =
      𝟙 (projectiveSpacePowerOver R n m).left := by
  refine eq_of_comp_pi_left _ (projectiveSpacePowerOver R n m).hom _ _ ?_ ?_ ?_
  · rw [Category.assoc, projectiveSpacePowerOverRingMap_comp_hom,
      ← Category.assoc, projectiveSpacePowerOverRingMap_comp_hom, Category.assoc,
      specMap_comp_specMap_eq_id R α γ hγ, Category.comp_id]
  · rw [Category.id_comp]
  · intro i
    exact comp_comp_eq_id_comp _ _ _ _ _ _
      (projectiveSpacePowerOverRingMap_comp_pi_left R n A α m i)
      (projectiveSpacePowerOverRingMap_comp_pi_left A n R γ m i)
      (projectiveSpaceOverRingMap_comp_self R n α γ hγ)

/-- **The section at a point of the base, read through the identification of the base change.**
Composing the section attached to the retraction `γ` with the identification of the base change
of `(ℙⁿ_R)^m` along `α` with `(ℙⁿ_A)^m` gives the base-change morphism of powers along `γ`. -/
theorem pullbackSectionOfRetraction_comp_projectiveSpacePowerPullbackIso_hom_left :
    pullbackSectionOfRetraction (projectiveSpacePowerOver R n m) (Spec.map (ofHom α))
          (Spec.map (ofHom γ)) (specMap_comp_specMap_eq_id R α γ hγ) ≫
        (projectiveSpacePowerPullbackIso α n m).hom.left =
      projectiveSpacePowerOverRingMap A n R γ m := by
  refine eq_of_comp_pi_left _
    ((projectiveSpacePowerOver R n m).hom ≫ Spec.map (ofHom γ)) _ _ ?_ ?_ ?_
  · rw [Category.assoc, Over.w (projectiveSpacePowerPullbackIso α n m).hom]
    exact pullbackSectionOfRetraction_comp_snd _ _ _ _
  · exact projectiveSpacePowerOverRingMap_comp_hom A n R γ m
  · intro i
    have hπ := congrArg Over.Hom.left (projectiveSpacePowerPullbackIso_hom_π R n A α m i)
    simp only [Over.comp_left] at hπ
    have hfst : pullbackSectionOfRetraction (projectiveSpacePowerOver R n m)
          (Spec.map (ofHom α)) (Spec.map (ofHom γ)) (specMap_comp_specMap_eq_id R α γ hγ) ≫
        ((Over.pullback (Spec.map (ofHom α))).map (Pi.π (fun _ : Fin m =>
          (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i)).left =
        pullback.lift ((Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i).left)
          ((projectiveSpacePowerOver R n m).hom ≫ Spec.map (ofHom γ))
          (by
            rw [Category.assoc, specMap_comp_specMap_eq_id R α γ hγ, Category.comp_id]
            exact Over.w (Pi.π (fun _ : Fin m =>
              (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i)) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst]
        simp only [Over.pullback_map_left, pullback.lift_fst]
        rw [← Category.assoc, pullbackSectionOfRetraction_comp_fst, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd]
        simp only [Over.pullback_map_left, pullback.lift_snd]
        exact pullbackSectionOfRetraction_comp_snd _ _ _ _
    rw [Category.assoc, hπ, projectiveSpacePowerOverRingMap_comp_pi_left,
      ← Category.assoc, hfst, projectiveSpacePullbackIso_hom_left]
    refine comp_inv_eq_of_eq_comp_hom _ _ _ (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst _ _ _).trans
        (comp_comp_comp_comp_eq_left _ _ _ _ _
          (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom α))).isoPullback_hom_fst
          (projectiveSpaceOverRingMap_comp_self R n α γ hγ)).symm
    · refine (pullback.lift_snd _ _ _).trans
        ((comp_comp_comp_comp_eq _ _ _ _ _ _
            (isPullback_projectiveSpaceOverMap n (Spec.map (ofHom α))).isoPullback_hom_snd
            (projectiveSpaceOverMap_fst n (Spec.map (ofHom γ)))).trans ?_).symm
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun u => u ≫ Spec.map (ofHom γ))
          (Over.w (Pi.π (fun _ : Fin m =>
            (projectiveSpaceOverRing n (.of R)).asOver (Spec (.of R))) i)))

/-- **The family of automorphisms given by a matrix over `A`, evaluated at a point of
`Spec A`.** Restricting the automorphism of the base change of `(ℙⁿ_R)^m` along `α` attached to
`M` to the fibre over the point of `Spec A` named by a retraction `γ` of `α` gives the
automorphism of `(ℙⁿ_R)^m` attached to the matrix of images of the entries of `M` under `γ`.

This is what makes the generic matrix over the coordinate ring of the general linear group a
*family*: its value at a point of the group is the automorphism that point names. -/
theorem pullbackSectionOfRetraction_comp_projectiveSpacePowerMatrixAut
    (M : Fin m → Matrix.GeneralLinearGroup (Fin (n + 1)) A) :
    pullbackSectionOfRetraction (projectiveSpacePowerOver R n m) (Spec.map (ofHom α))
          (Spec.map (ofHom γ)) (specMap_comp_specMap_eq_id R α γ hγ) ≫
        ((Aut.autMulEquivOfIso (projectiveSpacePowerPullbackIso α n m)).symm
          (projectiveSpacePowerMatrixAut A n m M)).asIso.hom.left ≫
        pullback.fst (projectiveSpacePowerOver R n m).hom (Spec.map (ofHom α)) =
      (projectiveSpacePowerMatrixAut R n m
        (fun i => Matrix.GeneralLinearGroup.map γ (M i))).asIso.hom.left := by
  have hΨ : ((Aut.autMulEquivOfIso (projectiveSpacePowerPullbackIso α n m)).symm
        (projectiveSpacePowerMatrixAut A n m M)).asIso.hom.left =
      (projectiveSpacePowerPullbackIso α n m).hom.left ≫
        (projectiveSpacePowerMatrixAut A n m M).asIso.hom.left ≫
        (projectiveSpacePowerPullbackIso α n m).inv.left := by
    rfl
  rw [hΨ, Category.assoc, Category.assoc]
  exact comp_specialize _ _ _ _ _ _ _ _
    (pullbackSectionOfRetraction_comp_projectiveSpacePowerPullbackIso_hom_left R n α γ hγ m)
    rfl
    (projectiveSpacePowerOverRingMap_comp_projectiveSpacePowerMatrixAut A n R γ m M)
    (projectiveSpacePowerOverRingMap_comp_self R n α γ hγ m)

end Specialize

/-! ### The action of `(GL₂)^m` on `(ℙ¹_k)^m` evaluated at a point of the group -/

section GenericSpecialize

variable (k : Type u) [CommRing k] (m : ℕ)

/-- **The action morphism of `(GL₂)^m` on `(ℙ¹_k)^m`, restricted to the fibre over a point of
the group.** A `k`-point of `(GL₂)^m` is a retraction `γ` of the structure map of its coordinate
ring; it names the `m` invertible two-by-two matrices over `k` got by applying `γ` to the
entries of the generic ones, and the restriction of the action morphism to the fibre over that
point is the automorphism of `(ℙ¹_k)^m` those matrices give.

This is the evaluation the contraction step of [Stacks, Tag 0AEM] needs: the family
`AlgebraicGeometry.projectiveLinePowerGeneralLinearAction` is a single morphism over the group,
and this says that its fibre over `g ∈ (GL₂)^m(k)` is `x ↦ g · x`. -/
theorem pullbackSectionOfRetraction_comp_projectiveLinePowerGeneralLinearAction
    (γ : generalLinearTwoPowerCoordinateRing k m →+* k)
    (hγ : γ.comp (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) = RingHom.id k) :
    pullbackSectionOfRetraction (projectiveSpacePowerOver k 1 m)
          (Spec.map (generalLinearTwoPowerStructureMap k m)) (Spec.map (ofHom γ))
          (specMap_comp_specMap_eq_id k
            (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) γ hγ) ≫
        projectiveLinePowerGeneralLinearAction k m =
      (projectiveSpacePowerMatrixAut k 1 m fun i =>
        Matrix.GeneralLinearGroup.map γ (genericGeneralLinearTwoPower k m i)).asIso.hom.left := by
  rw [projectiveLinePowerGeneralLinearAction, projectiveLinePowerGenericAutBaseChange,
    projectiveLinePowerGenericAut]
  exact pullbackSectionOfRetraction_comp_projectiveSpacePowerMatrixAut k 1
    (algebraMap k (generalLinearTwoPowerCoordinateRing k m)) γ hγ m
    (genericGeneralLinearTwoPower k m)

/-- **The action morphism of `(GL₂)^m` on `(ℙ¹_k)^m` at the point named by `m` invertible
matrices over `k`.** For every `m`-tuple `M` of invertible two-by-two matrices over `k` there is
a `k`-point of `(GL₂)^m` at which the action family restricts to the automorphism of `(ℙ¹_k)^m`
given by `M`.

This is the form in which the contraction step of [Stacks, Tag 0AEM] uses the family: a property
of the family over a Zariski open subset of the group gives, at each `k`-point of that open
subset, the same property of the single automorphism `x ↦ M · x`. -/
theorem pullbackSectionOfRetraction_comp_projectiveLinePowerGeneralLinearAction_point
    (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k) :
    pullbackSectionOfRetraction (projectiveSpacePowerOver k 1 m)
          (Spec.map (generalLinearTwoPowerStructureMap k m))
          (Spec.map (ofHom (generalLinearTwoPowerPoint k m M)))
          (specMap_comp_specMap_eq_id k
            (algebraMap k (generalLinearTwoPowerCoordinateRing k m))
            (generalLinearTwoPowerPoint k m M)
            (generalLinearTwoPowerPoint_comp_algebraMap k m M)) ≫
        projectiveLinePowerGeneralLinearAction k m =
      (projectiveSpacePowerMatrixAut k 1 m M).asIso.hom.left := by
  rw [pullbackSectionOfRetraction_comp_projectiveLinePowerGeneralLinearAction k m
    (generalLinearTwoPowerPoint k m M) (generalLinearTwoPowerPoint_comp_algebraMap k m M)]
  exact congrArg (fun N => (projectiveSpacePowerMatrixAut k 1 m N).asIso.hom.left)
    (funext fun i => generalLinearTwoPowerPoint_map_genericGeneralLinearTwoPower k m M i)

end GenericSpecialize

end Model

end AlgebraicGeometry

end
