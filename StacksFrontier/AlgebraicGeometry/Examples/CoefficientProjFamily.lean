module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Flat
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.DegreeOneChart
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlat
public import StacksFrontier.RingTheory.MvPolynomial.CoefficientIdeal

/-!
# The projective family attached to a coefficientwise ideal

Let `K` be a monotone family of ideals of `R` indexed by the monomials of `R[X₀, …, X_m]` which
is trivial in degree zero. The quotient of the polynomial ring by the ideal cut out by `K` is a
graded `R`-algebra whose degree-zero part is `R` and which is generated in degree one, so its
`Proj` is a proper `R`-scheme, and it is flat over `R` as soon as every `R ⧸ K d` is flat.

## Main definitions

* `Stacks.CoefficientProj.projGrading`: the grading by total degree of the quotient.
* `Stacks.CoefficientProj.mkX`: the image of a variable in the quotient.
* `Stacks.CoefficientProj.quotientMkGraded`: the quotient map as a homomorphism of graded rings.
* `Stacks.CoefficientProj.toSpecBase`: the structure morphism of the family over `Spec R`.

## Main results

* `Stacks.CoefficientProj.isProper_toSpecBase`: the family is proper.
* `Stacks.CoefficientProj.flat_toSpecBase`: the family is flat when every `R ⧸ K d` is.
-/

@[expose] public noncomputable section

namespace Stacks.CoefficientProj

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open Stacks.GradedModel

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {m : ℕ} {R : Type u} [CommRing R] (K : (Fin (m + 1) →₀ ℕ) → Ideal R)

/-- The grading by total degree of `R[X₀, …, X_m] ⧸ coefficientIdeal K`. -/
abbrev projGrading :
    ℕ → Submodule R (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) :=
  quotientGrading (homogeneousSubmodule (Fin (m + 1)) R) (coefficientIdeal K)

/-- The quotient map onto `R[X₀, …, X_m] ⧸ coefficientIdeal K`, as a homomorphism of graded
rings. -/
def quotientMkGraded : homogeneousSubmodule (Fin (m + 1)) R →+*ᵍ projGrading K where
  __ := Ideal.Quotient.mk (coefficientIdeal K)
  map_mem ha := mk_mem_quotientGrading ha

/-- The graded quotient map sends a polynomial to its class modulo `coefficientIdeal K`. -/
@[simp]
theorem quotientMkGraded_apply (p : MvPolynomial (Fin (m + 1)) R) :
    quotientMkGraded K p = Ideal.Quotient.mk (coefficientIdeal K) p := rfl

/-- The graded quotient map `quotientMkGraded K` is surjective. -/
theorem surjective_quotientMkGraded : Function.Surjective (quotientMkGraded K) :=
  Ideal.Quotient.mk_surjective

/-- The image of the `i`-th variable in `R[X₀, …, X_m] ⧸ coefficientIdeal K`. -/
abbrev mkX (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K :=
  Ideal.Quotient.mk (coefficientIdeal K) (X i)

/-- The image of each variable is homogeneous of degree one. -/
theorem mkX_mem_one (i : Fin (m + 1)) : mkX K i ∈ projGrading K 1 :=
  mk_mem_quotientGrading ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R i))

/-- The images of the variables generate the quotient as an algebra over its degree-zero part. -/
theorem adjoin_range_mkX : Algebra.adjoin ↥(projGrading K 0) (Set.range (mkX K)) = ⊤ :=
  adjoin_range_X_quotientGrading_zero K

/-- The quotient is a finitely generated algebra over its degree-zero part. -/
instance finiteType :
    Algebra.FiniteType ↥(projGrading K 0)
      (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) :=
  ⟨Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, adjoin_range_mkX K⟩⟩

/-- The structure morphism of the family over the spectrum of the base ring. -/
def toSpecBase : Proj (projGrading K) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projGrading K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ↥(projGrading K 0)))

/-- The base ring is the degree-zero part of the quotient. -/
def baseRingEquiv (hK : Monotone K) (hK0 : K 0 = ⊥) : R ≃+* ↥(projGrading K 0) :=
  RingEquiv.ofBijective _ (bijective_algebraMap_quotientGrading_zero K hK hK0)

/-- The isomorphism `baseRingEquiv K hK hK0` is the algebra map of `R` into degree zero. -/
@[simp]
theorem baseRingEquiv_apply (hK : Monotone K) (hK0 : K 0 = ⊥) (r : R) :
    baseRingEquiv K hK hK0 r = algebraMap R ↥(projGrading K 0) r := rfl

/-- The morphism of spectra induced by the algebra map of `R` into the degree-zero part is an
isomorphism. -/
theorem isIso_specMap_algebraMap (hK : Monotone K) (hK0 : K 0 = ⊥) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R ↥(projGrading K 0)))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap R ↥(projGrading K 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_algebraMap_quotientGrading_zero K hK hK0)
  infer_instance

/-- **The family is proper over the base.** -/
theorem isProper_toSpecBase (hK : Monotone K) (hK0 : K 0 = ⊥) :
    IsProper (toSpecBase K) := by
  have := isIso_specMap_algebraMap K hK hK0
  rw [toSpecBase, MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

/-- Each standard affine chart of the family is flat over the degree-zero part. -/
theorem flat_away (hK : Monotone K) (hK0 : K 0 = ⊥)
    (hflat : ∀ d, Module.Flat R (R ⧸ K d)) (i : Fin (m + 1)) :
    Module.Flat ↥(projGrading K 0) (Away (projGrading K) (mkX K i)) := by
  have _ : Module.Flat R (Away (projGrading K) (mkX K i)) :=
    Away.flat_of_eventually_flat (projGrading K) (mkX_mem_one K i) 0
      fun n _ => by rw [smul_eq_mul, mul_one]; exact flat_quotientGrading K hK hflat n
  refine Stacks.SymmetricAway.flat_of_baseRingEquiv (baseRingEquiv K hK hK0) fun b z => ?_
  have key : algebraMap R (Away (projGrading K) (mkX K i))
      ((baseRingEquiv K hK hK0).symm b) =
      algebraMap ↥(projGrading K 0) (Away (projGrading K) (mkX K i)) b := by
    rw [HomogeneousLocalization.algebraMap_eq_fromZeroRingHom_comp, RingHom.comp_apply,
      ← baseRingEquiv_apply K hK hK0, RingEquiv.apply_symm_apply]
    rfl
  rw [Algebra.smul_def, Algebra.smul_def, key]

/-- **The family is flat over the base** as soon as every `R ⧸ K d` is a flat `R`-module. -/
theorem flat_toSpecBase (hK : Monotone K) (hK0 : K 0 = ⊥)
    (hflat : ∀ d, Module.Flat R (R ⧸ K d)) :
    AlgebraicGeometry.Flat (toSpecBase K) := by
  have := isIso_specMap_algebraMap K hK hK0
  have := (HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat)).toRespects
  rw [toSpecBase, MorphismProperty.cancel_right_of_respectsIso (P := @Flat)]
  exact Proj.flat_toSpecZero_of_flat_away (projGrading K) (mkX K) (fun _ => 1)
    (fun _ => Nat.one_pos) (mkX_mem_one K) (adjoin_range_mkX K) (flat_away K hK hK0 hflat)

end Stacks.CoefficientProj

end
