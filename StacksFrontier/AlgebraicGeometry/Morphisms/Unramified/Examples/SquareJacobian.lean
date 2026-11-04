module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.ZeroScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Square systems of equations with invertible Jacobian

Let `g₁, …, g_n` be as many polynomials as there are variables, and let `q` be a prime of
`R[x₁, …, x_n]` containing them at which the Jacobian has rank `n`. Then the Jacobian
determinant does not lie in `q`, the quotient `B = R[x₁, …, x_n]/(g₁, …, g_n)` admits a
submersive presentation after inverting that determinant, and the resulting localization is
étale over `R`.

## Main definitions

* `AlgebraicGeometry.FullRankJacobianSystem.jacobianDet` is the determinant of the full Jacobian
  matrix of a square system.
* `AlgebraicGeometry.FullRankJacobianSystem.presentation` is the presentation of the quotient by
  a square system, viewed as a pre-submersive presentation through the identity matching of
  equations with variables.

## Main results

* `AlgebraicGeometry.FullRankJacobianSystem.jacobianDet_notMem_prime`: the Jacobian determinant
  avoids the prime.
* `AlgebraicGeometry.FullRankJacobianSystem.etale_localizationAway_jacobianDet`: inverting the
  Jacobian determinant yields an étale `R`-algebra.

## Implementation notes

Étaleness is obtained from Mathlib's theory of standard smooth algebras: composing the
pre-submersive presentation of the quotient with the standard presentation of a localization
away from an element multiplies the two Jacobians, and both factors become units after the
localization. The resulting submersive presentation has relative dimension zero, and standard
smooth of relative dimension zero is étale.

## References

* [Stacks Project, Tag 024Y](https://stacks.math.columbia.edu/tag/024Y)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

noncomputable section

namespace FullRankJacobianSystem

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The determinant of the Jacobian matrix of a system with as many equations as variables. -/
public def jacobianDet (S : FullRankJacobianSystem R n n) : MvPolynomial (Fin n) R :=
  (Matrix.of fun i j : Fin n => MvPolynomial.pderiv j (S.equations i)).det

/-- For a square system the full-rank condition says exactly that the Jacobian determinant does
not lie in the selected prime. -/
public theorem jacobianDet_notMem_prime (S : FullRankJacobianSystem R n n) :
    jacobianDet S ∉ S.prime := by
  classical
  let K := S.prime.ResidueField
  let M : Matrix (Fin n) (Fin n) K := fun i j =>
    algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.pderiv j (S.equations i))
  have hrank : M.rank = n := S.jacobian_rank
  have hsurj : Function.Surjective ⇑M.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    refine Submodule.eq_top_of_finrank_eq ?_
    show M.rank = Module.finrank K (Fin n → K)
    rw [hrank, Module.finrank_fin_fun]
  have hunit : IsUnit M.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    simpa only [Matrix.coe_mulVecLin] using
      LinearMap.injective_iff_surjective.mpr hsurj
  have hdet : M.det = algebraMap (MvPolynomial (Fin n) R) K (jacobianDet S) := by
    let M₀ : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
      fun i j => MvPolynomial.pderiv j (S.equations i)
    show Matrix.det (M₀.map (algebraMap (MvPolynomial (Fin n) R) K)) = _
    exact (RingHom.map_det (algebraMap (MvPolynomial (Fin n) R) K) M₀).symm
  exact fun hmem => hunit.ne_zero <| hdet.trans <|
    (Ideal.algebraMap_residueField_eq_zero (I := S.prime) (x := jacobianDet S)).2 hmem

/-- The presentation of the quotient by a square system, with the `i`-th equation matched to the
`i`-th variable. Its Jacobian is the image of `jacobianDet`. -/
public def presentation (S : FullRankJacobianSystem R n n) :
    Algebra.PreSubmersivePresentation R
      (MvPolynomial (Fin n) R ⧸ S.equationIdeal) (Fin n) (Fin n) where
  __ := Algebra.Presentation.naive (v := S.equations)
  map := id
  map_inj := Function.injective_id

/-- The Jacobian of `FullRankJacobianSystem.presentation` is the image of the Jacobian
determinant in the quotient. -/
public theorem presentation_jacobian (S : FullRankJacobianSystem R n n) :
    (presentation S).jacobian = Ideal.Quotient.mk S.equationIdeal (jacobianDet S) := by
  classical
  have hmat : (presentation S).jacobiMatrix =
      (Matrix.of fun i j : Fin n => MvPolynomial.pderiv j (S.equations i)).transpose := by
    ext i j
    simp [presentation, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hmat,
    Matrix.det_transpose]
  rfl

/-- Inverting the Jacobian determinant of a square system with full rank at a prime gives an
étale `R`-algebra. -/
@[sga "4½ Arcata 2.1.1" "special case"]
public theorem etale_localizationAway_jacobianDet (S : FullRankJacobianSystem R n n) :
    Algebra.Etale R
      (Localization.Away (Ideal.Quotient.mk S.equationIdeal (jacobianDet S))) := by
  set B := MvPolynomial (Fin n) R ⧸ S.equationIdeal
  set d : B := Ideal.Quotient.mk S.equationIdeal (jacobianDet S)
  let Q : Algebra.PreSubmersivePresentation B (Localization.Away d) Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway (Localization.Away d) d
  have hjac : IsUnit (Q.comp (presentation S)).jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, presentation_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    have hd : IsUnit (algebraMap B (Localization.Away d) d) :=
      IsLocalization.Away.algebraMap_isUnit _
    exact hd.mul hd
  have hdim : (Q.comp (presentation S)).dimension = 0 := by
    rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
    simp [Algebra.Presentation.dimension]
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 R (Localization.Away d) :=
    Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension
      { toPreSubmersivePresentation := Q.comp (presentation S), jacobian_isUnit := hjac } hdim
  infer_instance

end FullRankJacobianSystem

end

end AlgebraicGeometry
