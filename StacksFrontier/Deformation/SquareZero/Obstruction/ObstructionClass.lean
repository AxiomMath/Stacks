module

public import Mathlib.LinearAlgebra.Basis.Defs
public import StacksFrontier.Deformation.SquareZero.Obstruction.RelationDifference
public import StacksFrontier.Deformation.SquareZero.Obstruction.ConormalFunctional
public import StacksFrontier.Deformation.SquareZero.Obstruction.FittingMapOfRelationAgreement

/-!
# The obstruction class of a square-zero deformation diagram

The reduced polynomial differential and the evaluation difference, the criterion that the class
of the conormal functional vanishes exactly when a fitting map exists, and the obstruction class
`Stacks.Deformation.obstructionClass` in the first Ext group from the naive cotangent complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- `Algebra.Generators.toExtension` is a semireducible `def`, so the two spellings of its
-- polynomial ring -- `P.toExtension.Ring` and `P.Ring` -- do not unify at the transparency
-- that `simp` and `rw` use. Making it implicit-reducible here lets both spellings match.
attribute [local implicit_reducible] Algebra.Generators.toExtension

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂

namespace Stacks.Deformation
attribute [local instance] HasDerivedCategory.standard

/-- `Algebra.Generators.cotangentSpaceBasis_apply` in the `Algebra.Extension.Ring` spelling
of the polynomial ring. The cotangent space of the canonical presentation is stated over
`P.toExtension.Ring`, while Mathlib's lemma is stated over the definitionally equal `P.Ring`,
so rewriting with the Mathlib spelling leaves a goal that is not type-correct at the
transparency `rw` works at. The two spellings are bridged once here. -/
public theorem cotangentSpaceBasis_apply_toExtension
    (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (b : B) :
    (Algebra.Generators.self A B).cotangentSpaceBasis b =
      (1 : B) ⊗ₜ[(Algebra.Generators.self A B).toExtension.Ring]
        KaehlerDifferential.D A (Algebra.Generators.self A B).toExtension.Ring
          (MvPolynomial.X b) :=
  Algebra.Generators.cotangentSpaceBasis_apply (Algebra.Generators.self A B) b

/-- The differential of a polynomial after reducing its coefficients to the base ring. -/
public noncomputable def reducedPolynomialDifferential
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A') :
    (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace :=
  (1 : D.S₁.B) ⊗ₜ[(Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.Ring]
    KaehlerDifferential.D D.S₁.A
      (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.Ring
      (coefficientReduction D p)

/-- The reduced differential of a constant polynomial vanishes. -/
public theorem reducedPolynomialDifferential_C
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (a : D.S₁.A') :
    reducedPolynomialDifferential D (MvPolynomial.C a) = 0 := by
  simp only [reducedPolynomialDifferential, coefficientReduction,
    MvPolynomial.map_C]
  have h : KaehlerDifferential.D D.S₁.A
      (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.Ring
      (MvPolynomial.C (algebraMap D.S₁.A' D.S₁.A a)) = 0 :=
    Derivation.map_algebraMap _ _
  rw [h, TensorProduct.tmul_zero]

/-- The reduced differential of a variable is the corresponding basis element of the free
cotangent space. -/
public theorem reducedPolynomialDifferential_X
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) (b : D.S₁.B) :
    reducedPolynomialDifferential D (MvPolynomial.X b) =
      (Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b := by
  rw [cotangentSpaceBasis_apply_toExtension]
  simp [reducedPolynomialDifferential, coefficientReduction]

/-- The reduced differential is additive. -/
public theorem reducedPolynomialDifferential_add
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p q : MvPolynomial D.S₁.B D.S₁.A') :
    reducedPolynomialDifferential D (p + q) =
      reducedPolynomialDifferential D p + reducedPolynomialDifferential D q := by
  simp [reducedPolynomialDifferential, map_add, TensorProduct.tmul_add]

/-- The polynomial ring acts on the cotangent space of the canonical presentation through
the presentation itself: the action of a polynomial is the action of its value in the base
ring. The scalar is typed at `Algebra.Generators.Ring`, which is the spelling the cotangent
space carries, so that the equation can be rewritten with. -/
public theorem smul_cotangentSpace_eq
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (r : (Algebra.Generators.self D.S₁.A D.S₁.B).Ring)
    (y : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace) :
    r • y = (reducedPresentationToB D r) • y :=
  (IsScalarTower.algebraMap_smul D.S₁.B r y).symm

/-- The Leibniz rule for the reduced differential of a product with a variable. -/
public theorem reducedPolynomialDifferential_mul_X
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (p : MvPolynomial D.S₁.B D.S₁.A') (b : D.S₁.B) :
    reducedPolynomialDifferential D (p * MvPolynomial.X b) =
      (presentationToB D p) •
        (Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b +
      b • reducedPolynomialDifferential D p := by
  rw [cotangentSpaceBasis_apply_toExtension]
  simp only [reducedPolynomialDifferential, coefficientReduction, map_mul,
    MvPolynomial.map_X, Derivation.leibniz, TensorProduct.tmul_add]
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    smul_cotangentSpace_eq D ((MvPolynomial.map (algebraMap D.S₁.A' D.S₁.A)) p),
    smul_cotangentSpace_eq D (MvPolynomial.X b),
    show (reducedPresentationToB D) ((MvPolynomial.map (algebraMap D.S₁.A' D.S₁.A)) p) =
      presentationToB D p from DFunLike.congr_fun (presentationToB_factor D) p,
    show (reducedPresentationToB D) (MvPolynomial.X b) = b by
      simp [reducedPresentationToB]]

/-- Difference between two evaluations of the polynomial presentation, expressed in the
square-zero kernel. -/
public theorem ideal_coe_add {R : Type*} [CommRing R] (I : Ideal R) (x y : I) :
    ((x + y : I) : R) = (x : R) + (y : R) := rfl

/-- The coercion from an ideal to the ring preserves subtraction. -/
public theorem ideal_coe_sub {R : Type*} [CommRing R] (I : Ideal R) (x y : I) :
    ((x - y : I) : R) = (x : R) - (y : R) := rfl

/-- The coercion from an ideal to the ring preserves negation. -/
public theorem ideal_coe_neg {R : Type*} [CommRing R] (I : Ideal R) (x : I) :
    ((-x : I) : R) = -(x : R) := rfl

/-- The coercion from an ideal to the ring sends scalar multiplication to multiplication. -/
public theorem ideal_coe_smul {R : Type*} [CommRing R] (I : Ideal R)
    (a : R) (x : I) : ((a • x : I) : R) = a * (x : R) := rfl

/-- The difference in `N₂` between the evaluation of a polynomial at the lifts `z` and at the
second chosen lifts. -/
public noncomputable def evaluationDifferenceWith
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (p : MvPolynomial D.S₁.B D.S₁.A') : D.S₂.N :=
  D.X₂.kernelEquiv.symm ⟨(presentationEval₂With D z) p - (presentationEval₂ D) p,
    by
      apply RingHom.mem_ker.mpr
      rw [map_sub]
      change D.X₂.toB ((presentationEval₂With D z) p) -
        D.X₂.toB ((presentationEval₂ D) p) = 0
      have h₁ := DFunLike.congr_fun (presentationEval₂With_toB D z hz) p
      have h₂ := DFunLike.congr_fun (presentationEval₂_toB D) p
      change D.X₂.toB ((presentationEval₂With D z) p) =
        algebraMap D.S₁.B D.S₂.B (presentationToB D p) at h₁
      change D.X₂.toB ((presentationEval₂ D) p) =
        algebraMap D.S₁.B D.S₂.B (presentationToB D p) at h₂
      rw [h₁, h₂, sub_self]⟩

/-- Viewed in the second extension, `evaluationDifferenceWith D z hz p` is the difference of the
two evaluations of `p`. -/
public theorem evaluationDifferenceWith_spec
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (p : MvPolynomial D.S₁.B D.S₁.A') :
    ((D.X₂.kernelEquiv (evaluationDifferenceWith D z hz p) :
      RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') =
      (presentationEval₂With D z) p - (presentationEval₂ D) p :=
  congrArg Subtype.val (D.X₂.kernelEquiv.apply_symm_apply ⟨_, _⟩)

/-- The evaluation difference vanishes on constant polynomials. -/
public theorem evaluationDifferenceWith_C
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (a : D.S₁.A') :
    evaluationDifferenceWith D z hz (MvPolynomial.C a) = 0 := by
  apply D.X₂.kernelEquiv.injective
  apply Subtype.ext
  rw [evaluationDifferenceWith_spec, map_zero]
  simp [presentationEval₂With, presentationEval₂]

/-- The evaluation difference is additive. -/
public theorem evaluationDifferenceWith_add
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (p q : MvPolynomial D.S₁.B D.S₁.A') :
    evaluationDifferenceWith D z hz (p + q) =
      evaluationDifferenceWith D z hz p + evaluationDifferenceWith D z hz q := by
  apply D.X₂.kernelEquiv.injective
  apply Subtype.ext
  rw [map_add D.X₂.kernelEquiv]
  rw [ideal_coe_add]
  simp only [evaluationDifferenceWith_spec, map_add]
  abel

/-- The Leibniz rule for the evaluation difference of a product with a variable. -/
public theorem evaluationDifferenceWith_mul_X
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (p : MvPolynomial D.S₁.B D.S₁.A') (b : D.S₁.B) :
    evaluationDifferenceWith D z hz (p * MvPolynomial.X b) =
      (presentationToB D p) • evaluationDifferenceWith D z hz (MvPolynomial.X b) +
      b • evaluationDifferenceWith D z hz p := by
  apply D.X₂.kernelEquiv.injective
  apply Subtype.ext
  rw [map_add,
    ← IsScalarTower.algebraMap_smul (A := D.S₂.B)
      (presentationToB D p) (evaluationDifferenceWith D z hz (MvPolynomial.X b)),
    ← IsScalarTower.algebraMap_smul (A := D.S₂.B)
      b (evaluationDifferenceWith D z hz p), map_smul, map_smul]
  rw [ideal_coe_add]
  simp only [evaluationDifferenceWith_spec]
  have hfg : D.X₂.toB.toRingHom.comp (presentationEval₂With D z) =
      D.X₂.toB.toRingHom.comp (presentationEval₂ D) := by
    rw [presentationEval₂With_toB D z hz, presentationEval₂_toB D]
  have hP : D.X₂.toB ((presentationEval₂ D) p) =
      algebraMap D.S₁.B D.S₂.B (presentationToB D p) := by
    have h := DFunLike.congr_fun (presentationEval₂_toB D) p
    exact h
  have hX : D.X₂.toB ((presentationEval₂ D) (MvPolynomial.X b)) =
      algebraMap D.S₁.B D.S₂.B b := by
    have h := DFunLike.congr_fun (presentationEval₂_toB D) (MvPolynomial.X b)
    change D.X₂.toB ((presentationEval₂ D) (MvPolynomial.X b)) =
      algebraMap D.S₁.B D.S₂.B (presentationToB D (MvPolynomial.X b)) at h
    simpa [presentationToB] using h
  have hsP := congrArg Subtype.val
    (D.X₂.toB_smul_kernel ((presentationEval₂ D) p)
      (D.X₂.kernelEquiv (evaluationDifferenceWith D z hz (MvPolynomial.X b))))
  have hsX := congrArg Subtype.val
    (D.X₂.toB_smul_kernel ((presentationEval₂ D) (MvPolynomial.X b))
      (D.X₂.kernelEquiv (evaluationDifferenceWith D z hz p)))
  rw [hP] at hsP
  rw [hX] at hsX
  rw [hsP, hsX]
  simpa only [ideal_coe_smul, evaluationDifferenceWith_spec] using
    (ringHom_sub_mul_of_squareZero D.X₂.toB.toRingHom
      D.X₂.sq_zero (presentationEval₂With D z) (presentationEval₂ D) hfg p
      (MvPolynomial.X b))

/-- The change of polynomial evaluation is obtained by applying the differential to
the changes of the variable lifts. -/
public theorem evaluationDifferenceWith_eq_differential
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (t : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace →ₗ[D.S₁.B]
      D.S₂.N)
    (ht : ∀ b, evaluationDifferenceWith D z hz (MvPolynomial.X b) =
      t ((Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b))
    (p : MvPolynomial D.S₁.B D.S₁.A') :
    evaluationDifferenceWith D z hz p = t (reducedPolynomialDifferential D p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [evaluationDifferenceWith_C, reducedPolynomialDifferential_C, map_zero]
  | add p q hp hq =>
      rw [evaluationDifferenceWith_add, reducedPolynomialDifferential_add, map_add,
        hp, hq]
  | mul_X p b hp =>
      rw [evaluationDifferenceWith_mul_X, reducedPolynomialDifferential_mul_X,
        map_add, map_smul, map_smul, hp, ht]

/-- The coefficient reduction of a relation, as a relation of the canonical presentation of
`B₁` over `A₁`. -/
public def reducedRelation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.ker :=
  ⟨coefficientReduction D x.1, by
    apply RingHom.mem_ker.mpr
    have h := DFunLike.congr_fun (presentationToB_factor D) x.1
    change reducedPresentationToB D (coefficientReduction D x.1) =
      presentationToB D x.1 at h
    change reducedPresentationToB D (coefficientReduction D x.1) = 0
    rw [h]
    exact RingHom.mem_ker.mp x.2⟩

/-- The conormal functional sends the class of a reduced relation to the relation difference. -/
public theorem conormalFunctional_reducedRelation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    conormalFunctional D (Algebra.Extension.Cotangent.mk (reducedRelation D x)) =
      relationDifference D x := by
  rw [conormalFunctional_mk]
  exact reducedRelationDifference_spec D x

/-- The cotangent complex sends the class of a reduced relation to its reduced differential. -/
public theorem cotangentComplex_reducedRelation
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.cotangentComplex
      (Algebra.Extension.Cotangent.mk (reducedRelation D x)) =
        reducedPolynomialDifferential D x.1 := by
  rw [Algebra.Extension.cotangentComplex_mk]
  rfl

/-- The functional on the free cotangent space specified by the changes of variable lifts. -/
public noncomputable def evaluationDifferenceLinear
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b) :
    (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace →ₗ[D.S₁.B]
      D.S₂.N :=
  (Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis.constr D.S₁.B
    (fun b ↦ evaluationDifferenceWith D z hz (MvPolynomial.X b))

/-- `evaluationDifferenceLinear` sends the basis element of a variable to the evaluation
difference of that variable. -/
public theorem evaluationDifferenceLinear_basis
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (b : D.S₁.B) :
    evaluationDifferenceLinear D z hz
      ((Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b) =
        evaluationDifferenceWith D z hz (MvPolynomial.X b) := by
  simp [evaluationDifferenceLinear, Module.Basis.constr_basis]

/-- Viewed in the second extension, the relation difference of `x` is its second evaluation
minus the image of its first evaluation. -/
public theorem relationDifference_spec
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (x : RingHom.ker (presentationToB D)) :
    ((D.X₂.kernelEquiv (relationDifference D x) :
      RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') =
      (presentationEval₂ D) x.1 -
        ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
          RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') := by
  change ((D.X₂.kernelEquiv
      (relationEval₂ D x - D.mapN (relationEval₁ D x)) :
        RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') = _
  rw [map_sub, ideal_coe_sub, relationEval₂_spec]

/-- Evaluation at `z` agrees on relations with the image of their first evaluation exactly when
the evaluation difference is minus the relation difference on every relation. -/
public theorem relationAgreement_iff_evaluationDifference
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b) :
    (∀ x : RingHom.ker (presentationToB D),
      (presentationEval₂With D z) x.1 =
        ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
          RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')) ↔
    (∀ x : RingHom.ker (presentationToB D),
      evaluationDifferenceWith D z hz x.1 = -relationDifference D x) := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · apply D.X₂.kernelEquiv.injective
    apply Subtype.ext
    rw [evaluationDifferenceWith_spec, map_neg, ideal_coe_neg,
      relationDifference_spec, h x]
    abel
  · have hx := congrArg
      (fun n : D.S₂.N ↦
        ((D.X₂.kernelEquiv n : RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B'))
      (h x)
    rw [evaluationDifferenceWith_spec, map_neg, ideal_coe_neg,
      relationDifference_spec] at hx
    linear_combination hx

/-- Modify the second chosen lifts by a functional on the free cotangent space. -/
public noncomputable def adjustedLift₂
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (t : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace →ₗ[D.S₁.B]
      D.S₂.N) (b : D.S₁.B) : D.X₂.B' :=
  lift₂ D b -
    ((D.X₂.kernelEquiv
      (t ((Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b)) :
      RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')

/-- The adjusted lifts still lift the images of the elements of `B₁` in `B₂`. -/
public theorem adjustedLift₂_toB
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (t : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace →ₗ[D.S₁.B]
      D.S₂.N) (b : D.S₁.B) :
    D.X₂.toB (adjustedLift₂ D t b) = algebraMap D.S₁.B D.S₂.B b := by
  have hk := (D.X₂.kernelEquiv
    (t ((Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b))).property
  change D.X₂.toB
    ((D.X₂.kernelEquiv
      (t ((Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b)) :
      RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B') = 0 at hk
  simp only [adjustedLift₂, map_sub, hk, sub_zero, lift₂_spec]

/-- At the lifts adjusted by `t`, the evaluation difference of a variable is minus `t` on the
corresponding basis element. -/
public theorem evaluationDifferenceWith_adjusted_X
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (t : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace →ₗ[D.S₁.B]
      D.S₂.N) (b : D.S₁.B) :
    evaluationDifferenceWith D (adjustedLift₂ D t) (adjustedLift₂_toB D t)
      (MvPolynomial.X b) =
        -t ((Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b) := by
  apply D.X₂.kernelEquiv.injective
  apply Subtype.ext
  rw [evaluationDifferenceWith_spec, map_neg, ideal_coe_neg]
  simp [presentationEval₂With, presentationEval₂, adjustedLift₂]

/-- If `t` takes the basis element of each variable to its evaluation difference, then `t` of the
cotangent complex image of a reduced relation is the evaluation difference of the relation. -/
private theorem evaluationDifferenceWith_eq_cotangentComplex
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (t : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace →ₗ[D.S₁.B]
      D.S₂.N)
    (ht : ∀ b, evaluationDifferenceWith D z hz (MvPolynomial.X b) =
      t ((Algebra.Generators.self D.S₁.A D.S₁.B).cotangentSpaceBasis b))
    (x : RingHom.ker (presentationToB D)) :
    evaluationDifferenceWith D z hz x.1 =
      t ((Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.cotangentComplex
        (Algebra.Extension.Cotangent.mk (reducedRelation D x))) := by
  rw [cotangentComplex_reducedRelation]
  exact evaluationDifferenceWith_eq_differential D z hz t ht x.1

/-- If a family of lifts makes the relations agree, then minus its evaluation difference
pulls back along the cotangent complex to the conormal functional. -/
private theorem lcomp_cotangentComplex_neg_evaluationDifferenceLinear
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (z : D.S₁.B → D.X₂.B')
    (hz : ∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b)
    (hrel : ∀ x : RingHom.ker (presentationToB D),
      (presentationEval₂With D z) x.1 =
        ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
          RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')) :
    LinearMap.lcomp D.S₁.B D.S₂.N
        (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.cotangentComplex
        (-(evaluationDifferenceLinear D z hz)) = conormalFunctional D := by
  ext y
  obtain ⟨r, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective y
  obtain ⟨x, hx⟩ := reducedRelation_has_lift D r
  rw [← show reducedRelation D x = r from Subtype.ext hx]
  change (-(evaluationDifferenceLinear D z hz)) _ = _
  rw [LinearMap.neg_apply, ← evaluationDifferenceWith_eq_cotangentComplex D z hz _
      (fun b ↦ (evaluationDifferenceLinear_basis D z hz b).symm) x,
    (relationAgreement_iff_evaluationDifference D z hz).mp hrel x,
    conormalFunctional_reducedRelation, neg_neg]

/-- If `t` lifts the conormal functional along the cotangent complex, then the lifts adjusted
by `t` have evaluation difference equal to minus the relation difference. -/
private theorem evaluationDifferenceWith_adjustedLift₂_eq_neg
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂})
    (t : (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.CotangentSpace →ₗ[D.S₁.B]
      D.S₂.N)
    (ht : LinearMap.lcomp D.S₁.B D.S₂.N
      (Algebra.Generators.self D.S₁.A D.S₁.B).toExtension.cotangentComplex t =
        conormalFunctional D)
    (x : RingHom.ker (presentationToB D)) :
    evaluationDifferenceWith D (adjustedLift₂ D t) (adjustedLift₂_toB D t) x.1 =
      -relationDifference D x := by
  rw [evaluationDifferenceWith_eq_cotangentComplex D _ _ (-t) (fun b ↦
      (evaluationDifferenceWith_adjusted_X D t b).trans (LinearMap.neg_apply t _).symm) x,
    LinearMap.neg_apply, ← conormalFunctional_reducedRelation, ← ht]
  rfl

/-- The class of the conormal functional vanishes exactly when some family of lifts makes the
evaluations of relations agree with the images of their first evaluations. -/
public theorem conormalClass_eq_zero_iff_relationAgreement
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := Algebra.Generators.self D.S₁.A D.S₁.B
    (Submodule.Quotient.mk (conormalFunctional D) :
      (P.toExtension.Cotangent →ₗ[D.S₁.B] D.S₂.N) ⧸
        LinearMap.range (LinearMap.lcomp D.S₁.B D.S₂.N
          P.toExtension.cotangentComplex)) = 0 ↔
      ∃ z : D.S₁.B → D.X₂.B',
        (∀ b, D.X₂.toB (z b) = algebraMap D.S₁.B D.S₂.B b) ∧
        (∀ x : RingHom.ker (presentationToB D),
          (presentationEval₂With D z) x.1 =
            ((D.X₂.kernelEquiv (D.mapN (relationEval₁ D x)) :
              RingHom.ker D.X₂.toB.toRingHom) : D.X₂.B')) := by
  intro P
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨t, ht⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp h)
    exact ⟨_, adjustedLift₂_toB D t, (relationAgreement_iff_evaluationDifference D _ _).mpr
      (evaluationDifferenceWith_adjustedLift₂_eq_neg D t ht)⟩
  · rintro ⟨z, hz, hrel⟩
    rw [Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr
      ⟨_, lcomp_cotangentComplex_neg_evaluationDifferenceLinear D z hz hrel⟩

/-- The class of the conormal functional vanishes exactly when the diagram has a fitting map. -/
public theorem conormalClass_eq_zero_iff_fittingMap
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let P := Algebra.Generators.self D.S₁.A D.S₁.B
    (Submodule.Quotient.mk (conormalFunctional D) :
      (P.toExtension.Cotangent →ₗ[D.S₁.B] D.S₂.N) ⧸
        LinearMap.range (LinearMap.lcomp D.S₁.B D.S₂.N
          P.toExtension.cotangentComplex)) = 0 ↔ Nonempty D.FittingMap := by
  refine ⟨fun h ↦ ?_, fun ⟨F⟩ ↦
    (conormalClass_eq_zero_iff_relationAgreement D).mpr (relation_agreement_of_fittingMap D F)⟩
  obtain ⟨z, hz, hrel⟩ := (conormalClass_eq_zero_iff_relationAgreement D).mp h
  exact ⟨fittingMap_of_relation_agreement D z hz hrel⟩

/-- The canonical obstruction to filling a compatible square-zero deformation diagram.

Its value lies in `Ext¹_{B₁}(NL_{B₁/A₁}, N₂)`.  The subtype records the characteristic
property of the obstruction: it is zero precisely when a fitting map `B'₁ → B'₂` exists. -/
@[stacks 08S5 "obstruction"]
public def obstructionClass
    (D : CompatibleSquareZeroDeformationDiagram.{u₁, u₂, u₃, u₄,
      v₁, v₂, v₃, v₄, w₁, w₂}) :
    let K := ((ModuleCat.uliftFunctor.{v₄} D.S₁.B).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex D.S₁.A D.S₁.B)
    {o : DerivedCategory.Ext
        (DerivedCategory.Q.obj
          (HomologicalComplex.double (K.d 1 0)
            (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v₄} D.S₁.B) 0).obj
          ((ModuleCat.uliftFunctor.{max u₂ u₃} D.S₁.B).obj
            (ModuleCat.of D.S₁.B D.S₂.N))) 1 //
      o = 0 ↔ Nonempty D.FittingMap} := by
  let P := Algebra.Generators.self D.S₁.A D.S₁.B
  let e := obstructionExtCokernelIso D
  let q : (P.toExtension.Cotangent →ₗ[D.S₁.B] D.S₂.N) ⧸
      LinearMap.range (LinearMap.lcomp D.S₁.B D.S₂.N
        P.toExtension.cotangentComplex) :=
    Submodule.Quotient.mk (conormalFunctional D)
  refine ⟨e.symm q, fun h ↦ ?_, fun h ↦ ?_⟩
  · have hq : q = 0 := by simpa [q] using congrArg e h
    exact (conormalClass_eq_zero_iff_fittingMap D).mp hq
  · have hq : q = 0 := (conormalClass_eq_zero_iff_fittingMap D).mpr h
    apply e.injective
    simpa [q] using hq

end Stacks.Deformation
end
