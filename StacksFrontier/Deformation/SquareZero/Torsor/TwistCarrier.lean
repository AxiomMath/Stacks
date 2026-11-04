module

public import Mathlib.Algebra.Ring.MinimalAxioms
public import StacksFrontier.Deformation.SquareZero.Torsor.TwistCochain

/-!
# The twisted ring of a solution (Stacks 08S7)

The carrier `TwistCarrier X δ`, a copy of the ring of a solution `X` whose operations
are deformed by the cochains of `δ`, its commutative ring structure, the twist value of
a polynomial, and the evaluation ring map `twistEval : A'[B] → TwistCarrier X δ`.

Part of `StacksFrontier.Deformation.SquareZero.Torsor`; see that module for the overview of
Stacks 08S7.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u₃ u₄ v

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

variable {S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}}

section Twist

variable (X : S.CompatibleExtension.{v})

section Carrier

/-- The carrier of the twist of a solution `X` by a conormal functional `δ`: a copy of the
ring of `X`, whose addition and multiplication are deformed by the two cochains of `δ`. -/
public structure TwistCarrier (X : S.CompatibleExtension.{v})
    (δ : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N) :
    Type v where
  /-- An element of the ring of `X`, viewed in the twisted carrier. -/
  mk ::
  /-- The underlying element of the ring of `X`. -/
  val : X.B'

namespace TwistCarrier

variable {X : S.CompatibleExtension.{v}}
  {δ : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N}

/-- The underlying element of `mk x` is `x`. -/
@[simp]
public lemma val_mk (x : X.B') : (mk x : TwistCarrier X δ).val = x := rfl

/-- An element of the twisted carrier is determined by its underlying element. -/
public lemma val_injective :
    Function.Injective (val (X := X) (δ := δ)) := by
  intro a b h
  cases a
  cases b
  exact congrArg mk h

/-- The image in `B` of an element of the twisted carrier.  The twisted operations do not
change this, because they differ from the original ones by elements of the kernel `N`. -/
public def toB (x : TwistCarrier X δ) : S.B := X.toB x.val

/-- The image in `B` of `mk x` is the image of `x`. -/
@[simp]
public lemma toB_mk (x : X.B') : (mk x : TwistCarrier X δ).toB = X.toB x := rfl

/-- The image in `B` of an element of the twisted carrier is that of its underlying element. -/
public lemma toB_eq_toB_val (x : TwistCarrier X δ) : X.toB x.val = x.toB := rfl

/-- Multiplying an element of the kernel by an element of the twisted carrier scales it by
the image in `B`. -/
public lemma val_mul_kernelInclusion (x : TwistCarrier X δ) (n : S.N) :
    x.val * kernelInclusion X n = kernelInclusion X (x.toB • n) :=
  mul_kernelInclusion X x.val n

/-- The zero of the twisted carrier is the zero of the ring of `X`. -/
public instance : Zero (TwistCarrier X δ) := ⟨mk 0⟩

/-- The one of the twisted carrier is `1` corrected by the multiplicative cochain at
`(1, 1)`. -/
public noncomputable instance : One (TwistCarrier X δ) :=
  ⟨mk (1 - kernelInclusion X (twistMulCochain δ 1 1))⟩

/-- The twisted addition: the sum in `X`, corrected by the additive cochain. -/
public noncomputable instance : Add (TwistCarrier X δ) :=
  ⟨fun x y ↦ mk (x.val + y.val + kernelInclusion X (twistAddCochain δ x.toB y.toB))⟩

/-- The twisted negation, corrected by the additive cochain. -/
public noncomputable instance : Neg (TwistCarrier X δ) :=
  ⟨fun x ↦ mk (-x.val - kernelInclusion X (twistAddCochain δ x.toB (-x.toB)))⟩

/-- The twisted multiplication: the product in `X`, corrected by the multiplicative cochain. -/
public noncomputable instance : Mul (TwistCarrier X δ) :=
  ⟨fun x y ↦ mk (x.val * y.val + kernelInclusion X (twistMulCochain δ x.toB y.toB))⟩

/-- The underlying element of `0` is `0`. -/
@[simp]
public lemma val_zero : (0 : TwistCarrier X δ).val = 0 := rfl

/-- The underlying element of the twisted `1`. -/
@[simp]
public lemma val_one :
    (1 : TwistCarrier X δ).val = 1 - kernelInclusion X (twistMulCochain δ 1 1) := rfl

/-- The underlying element of a twisted sum. -/
@[simp]
public lemma val_add (x y : TwistCarrier X δ) :
    (x + y).val = x.val + y.val + kernelInclusion X (twistAddCochain δ x.toB y.toB) := rfl

/-- The underlying element of a twisted negation. -/
@[simp]
public lemma val_neg (x : TwistCarrier X δ) :
    (-x).val = -x.val - kernelInclusion X (twistAddCochain δ x.toB (-x.toB)) := rfl

/-- The underlying element of a twisted product. -/
@[simp]
public lemma val_mul (x y : TwistCarrier X δ) :
    (x * y).val = x.val * y.val + kernelInclusion X (twistMulCochain δ x.toB y.toB) := rfl

/-- The image in `B` of the twisted `0` is `0`. -/
@[simp]
public lemma toB_zero : (0 : TwistCarrier X δ).toB = 0 := by
  simp [toB]

/-- The image in `B` of the twisted `1` is `1`. -/
@[simp]
public lemma toB_one : (1 : TwistCarrier X δ).toB = 1 := by
  simp [toB]

/-- The image in `B` is additive for the twisted addition. -/
@[simp]
public lemma toB_add (x y : TwistCarrier X δ) : (x + y).toB = x.toB + y.toB := by
  simp [toB]

/-- The image in `B` commutes with the twisted negation. -/
@[simp]
public lemma toB_neg (x : TwistCarrier X δ) : (-x).toB = -x.toB := by
  simp [toB]

/-- The image in `B` is multiplicative for the twisted multiplication. -/
@[simp]
public lemma toB_mul (x y : TwistCarrier X δ) : (x * y).toB = x.toB * y.toB := by
  simp [toB]

/-- The twisted addition is associative. -/
public lemma twist_add_assoc (x y z : TwistCarrier X δ) : x + y + z = x + (y + z) := by
  apply val_injective
  have hc := twistAddCochain_cocycle δ x.toB y.toB z.toB
  have key : kernelInclusion X (twistAddCochain δ x.toB y.toB) +
      kernelInclusion X (twistAddCochain δ (x.toB + y.toB) z.toB) =
      kernelInclusion X (twistAddCochain δ y.toB z.toB) +
      kernelInclusion X (twistAddCochain δ x.toB (y.toB + z.toB)) := by
    rw [← map_add, ← map_add, hc]
  simp only [val_add, toB_add]
  linear_combination key

/-- The zero of the twisted carrier is a left unit for the twisted addition. -/
public lemma twist_zero_add (x : TwistCarrier X δ) : 0 + x = x := by
  apply val_injective
  simp

/-- The twisted negation is a left inverse for the twisted addition. -/
public lemma twist_neg_add_cancel (x : TwistCarrier X δ) : -x + x = 0 := by
  apply val_injective
  simp only [val_add, val_neg, val_zero, toB_neg]
  rw [twistAddCochain_comm δ (-x.toB) x.toB]
  abel

/-- The twisted multiplication is commutative. -/
public lemma twist_mul_comm (x y : TwistCarrier X δ) : x * y = y * x := by
  apply val_injective
  simp only [val_mul]
  rw [twistMulCochain_comm δ x.toB y.toB, mul_comm x.val y.val]

/-- The twisted multiplication is associative. -/
public lemma twist_mul_assoc (x y z : TwistCarrier X δ) : x * y * z = x * (y * z) := by
  apply val_injective
  have hc := twistMulCochain_cocycle δ x.toB y.toB z.toB
  have key : kernelInclusion X (twistMulCochain δ x.toB y.toB) * z.val +
        kernelInclusion X (twistMulCochain δ (x.toB * y.toB) z.toB) =
      x.val * kernelInclusion X (twistMulCochain δ y.toB z.toB) +
        kernelInclusion X (twistMulCochain δ x.toB (y.toB * z.toB)) := by
    rw [mul_comm (kernelInclusion X (twistMulCochain δ x.toB y.toB)) z.val,
      val_mul_kernelInclusion, val_mul_kernelInclusion, ← map_add, ← map_add, hc]
  simp only [val_mul, toB_mul]
  linear_combination key

/-- The one of the twisted carrier is a left unit for the twisted multiplication. -/
public lemma twist_one_mul (x : TwistCarrier X δ) : 1 * x = x := by
  apply val_injective
  have key : x.val * kernelInclusion X (twistMulCochain δ 1 1) =
      kernelInclusion X (x.toB • twistMulCochain δ 1 1) :=
    val_mul_kernelInclusion x _
  simp only [val_mul, val_one, toB_one]
  rw [twistMulCochain_one_left δ x.toB]
  linear_combination -key

/-- The twisted multiplication distributes over the twisted addition. -/
public lemma twist_left_distrib (x y z : TwistCarrier X δ) :
    x * (y + z) = x * y + x * z := by
  apply val_injective
  have hc := twistCochain_distrib δ x.toB y.toB z.toB
  have key : x.val * kernelInclusion X (twistAddCochain δ y.toB z.toB) +
        kernelInclusion X (twistMulCochain δ x.toB (y.toB + z.toB)) =
      kernelInclusion X (twistMulCochain δ x.toB y.toB) +
        kernelInclusion X (twistMulCochain δ x.toB z.toB) +
        kernelInclusion X (twistAddCochain δ (x.toB * y.toB) (x.toB * z.toB)) := by
    rw [val_mul_kernelInclusion, ← map_add, ← map_add, ← map_add, hc]
  simp only [val_mul, val_add, toB_add, toB_mul]
  linear_combination key

/-- The twisted operations make the carrier a commutative ring. -/
public noncomputable instance : CommRing (TwistCarrier X δ) :=
  CommRing.ofMinimalAxioms twist_add_assoc twist_zero_add twist_neg_add_cancel
    twist_mul_assoc twist_mul_comm twist_one_mul twist_left_distrib

/-- On the kernel, the twisted addition agrees with the original one. -/
@[simp]
public lemma mk_kernelInclusion_add (n m : S.N) :
    (mk (kernelInclusion X n) : TwistCarrier X δ) + mk (kernelInclusion X m) =
      mk (kernelInclusion X (n + m)) := by
  apply val_injective
  simp [map_add]

/-- On the kernel, the twisted negation agrees with the original one. -/
@[simp]
public lemma mk_kernelInclusion_neg (n : S.N) :
    -(mk (kernelInclusion X n) : TwistCarrier X δ) = mk (kernelInclusion X (-n)) := by
  apply val_injective
  simp [map_neg]

/-- On the kernel, the twisted subtraction agrees with the original one. -/
public lemma mk_kernelInclusion_sub (n m : S.N) :
    (mk (kernelInclusion X n) : TwistCarrier X δ) - mk (kernelInclusion X m) =
      mk (kernelInclusion X (n - m)) := by
  rw [sub_eq_add_neg, mk_kernelInclusion_neg, mk_kernelInclusion_add, ← sub_eq_add_neg]

/-- Multiplying an element of the kernel in the twisted ring scales it by the image in
`B`. -/
public lemma mul_mk_kernelInclusion (x : TwistCarrier X δ) (n : S.N) :
    x * mk (kernelInclusion X n) = mk (kernelInclusion X (x.toB • n)) := by
  apply val_injective
  simp only [val_mul, toB_mk, toB_kernelInclusion, twistMulCochain_zero_right,
    map_zero, add_zero]
  exact val_mul_kernelInclusion x n

end TwistCarrier

end Carrier

section TwistValue

/-- The relation of `A'[B] → B` which the additive cochain of a conormal functional
evaluates. -/
public noncomputable def addCochainRelation (b c : S.B) :
    RingHom.ker (problemPresentationToB S) :=
  ⟨normalizedSection S (b + c) - normalizedSection S b - normalizedSection S c,
    normalizedSection_add_mem b c⟩

/-- The relation of `A'[B] → B` which the multiplicative cochain of a conormal functional
evaluates. -/
public noncomputable def mulCochainRelation (b c : S.B) :
    RingHom.ker (problemPresentationToB S) :=
  ⟨normalizedSection S b * normalizedSection S c - normalizedSection S (b * c),
    normalizedSection_mul_mem b c⟩

/-- The relation of `A'[B] → B` measuring the failure of the normalised section to be
multiplicative at `1`. -/
public noncomputable def oneCochainRelation (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}) :
    RingHom.ker (problemPresentationToB S) :=
  ⟨normalizedSection S (1 : S.B) - 1, normalizedSection_one_sub_one_mem⟩

/-- Every polynomial differs from the normalised section of its image by a relation. -/
public lemma sub_normalizedSection_mem (p : MvPolynomial S.B S.A') :
    p - normalizedSection S (problemPresentationToB S p) ∈
      RingHom.ker (problemPresentationToB S) := by
  apply RingHom.mem_ker.mpr
  rw [map_sub, problemPresentationToB_normalizedSection, sub_self]

/-- The relation by which a polynomial differs from the normalised section of its image. -/
public noncomputable def twistRelation (p : MvPolynomial S.B S.A') :
    RingHom.ker (problemPresentationToB S) :=
  ⟨p - normalizedSection S (problemPresentationToB S p), sub_normalizedSection_mem p⟩

variable (δ : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N)

/-- The additive cochain, written through the relation functional. -/
public lemma twistAddCochain_eq (b c : S.B) :
    twistAddCochain δ b c = -relationFunctional δ (addCochainRelation b c) := rfl

/-- The multiplicative cochain, written through the relation functional. -/
public lemma twistMulCochain_eq (b c : S.B) :
    twistMulCochain δ b c = relationFunctional δ (mulCochainRelation b c) := rfl

/-- The correction term by which the twisted evaluation of a polynomial differs from the
original one. -/
public noncomputable def twistValue (p : MvPolynomial S.B S.A') : S.N :=
  relationFunctional δ (twistRelation p)

/-- The correction term of the zero polynomial vanishes. -/
@[simp]
public lemma twistValue_zero : twistValue δ (0 : MvPolynomial S.B S.A') = 0 := by
  have h : twistRelation (0 : MvPolynomial S.B S.A') = 0 :=
    Subtype.ext (by simp [twistRelation])
  rw [twistValue, h, map_zero]

/-- On a relation, the correction term is just the value of the functional. -/
public lemma twistValue_of_mem_ker {p : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S)) :
    twistValue δ p = relationValue δ p hp := by
  have h : twistRelation p = ⟨p, hp⟩ := by
    apply Subtype.ext
    change p - normalizedSection S (problemPresentationToB S p) = p
    rw [RingHom.mem_ker.mp hp, normalizedSection_zero, sub_zero]
  rw [twistValue, h]
  rfl

/-- The correction term is additive up to the additive cochain. -/
public lemma twistValue_add (p q : MvPolynomial S.B S.A') :
    twistValue δ (p + q) = twistValue δ p + twistValue δ q +
      twistAddCochain δ (problemPresentationToB S p) (problemPresentationToB S q) := by
  have h : twistRelation (p + q) = twistRelation p + twistRelation q -
      addCochainRelation (problemPresentationToB S p) (problemPresentationToB S q) := by
    apply Subtype.ext
    change p + q - normalizedSection S (problemPresentationToB S (p + q)) =
      p - normalizedSection S (problemPresentationToB S p) +
        (q - normalizedSection S (problemPresentationToB S q)) -
        (normalizedSection S (problemPresentationToB S p + problemPresentationToB S q) -
          normalizedSection S (problemPresentationToB S p) -
          normalizedSection S (problemPresentationToB S q))
    rw [map_add]
    ring
  rw [twistValue, twistValue, twistValue, h, map_sub, map_add, twistAddCochain_eq]
  abel

/-- The correction term obeys the Leibniz rule up to the multiplicative cochain. -/
public lemma twistValue_mul (p q : MvPolynomial S.B S.A') :
    twistValue δ (p * q) = problemPresentationToB S p • twistValue δ q +
      problemPresentationToB S q • twistValue δ p +
      twistMulCochain δ (problemPresentationToB S p) (problemPresentationToB S q) := by
  have h : twistRelation (p * q) =
      relationSmul (normalizedSection S (problemPresentationToB S p)) (twistRelation q) +
        relationSmul (normalizedSection S (problemPresentationToB S q)) (twistRelation p) +
        mulCochainRelation (problemPresentationToB S p) (problemPresentationToB S q) +
        relationMul (twistRelation p) (twistRelation q) := by
    apply Subtype.ext
    change p * q - normalizedSection S (problemPresentationToB S (p * q)) =
      normalizedSection S (problemPresentationToB S p) *
            (q - normalizedSection S (problemPresentationToB S q)) +
          normalizedSection S (problemPresentationToB S q) *
            (p - normalizedSection S (problemPresentationToB S p)) +
          (normalizedSection S (problemPresentationToB S p) *
              normalizedSection S (problemPresentationToB S q) -
            normalizedSection S (problemPresentationToB S p *
              problemPresentationToB S q)) +
        (p - normalizedSection S (problemPresentationToB S p)) *
          (q - normalizedSection S (problemPresentationToB S q))
    rw [map_mul]
    ring
  rw [twistValue, twistValue, twistValue, h, map_add, map_add, map_add,
    relationFunctional_relationSmul, relationFunctional_relationSmul,
    relationFunctional_relationMul, problemPresentationToB_normalizedSection,
    problemPresentationToB_normalizedSection, twistMulCochain_eq, add_zero]

/-- The correction term at `1` is the multiplicative cochain at `(1, 1)`, with a sign. -/
public lemma twistValue_one : twistValue δ (1 : MvPolynomial S.B S.A') =
    -twistMulCochain δ 1 1 := by
  have h1 : twistRelation (1 : MvPolynomial S.B S.A') = -oneCochainRelation S := by
    apply Subtype.ext
    change (1 : MvPolynomial S.B S.A') -
      normalizedSection S (problemPresentationToB S 1) =
      -(normalizedSection S (1 : S.B) - 1)
    rw [map_one]
    ring
  have h2 : mulCochainRelation (1 : S.B) (1 : S.B) =
      relationSmul (normalizedSection S (1 : S.B)) (oneCochainRelation S) := by
    apply Subtype.ext
    change normalizedSection S (1 : S.B) * normalizedSection S (1 : S.B) -
        normalizedSection S ((1 : S.B) * 1) =
      normalizedSection S (1 : S.B) * (normalizedSection S (1 : S.B) - 1)
    rw [mul_one (1 : S.B)]
    ring
  rw [twistValue, h1, map_neg, twistMulCochain_eq, h2, relationFunctional_relationSmul,
    problemPresentationToB_normalizedSection, one_smul]

/-- A coefficient in the ideal `I` contributes no correction term, because it reduces to
zero in the canonical presentation over `A`. -/
public lemma twistValue_C_of_mem_I (i : S.I) :
    twistValue δ (MvPolynomial.C (i : S.A')) = 0 := by
  have hA : algebraMap S.A' S.A (i : S.A') = 0 := by
    have hi : (i : S.A') ∈ RingHom.ker (algebraMap S.A' S.A) := by
      rw [S.kernel_eq]
      exact i.2
    exact RingHom.mem_ker.mp hi
  have hB : problemPresentationToB S (MvPolynomial.C (i : S.A')) = 0 := by
    rw [problemPresentationToB_C, IsScalarTower.algebraMap_apply S.A' S.A S.B, hA, map_zero]
  have h : reducedRelationOf S (twistRelation (MvPolynomial.C (i : S.A'))) = 0 := by
    apply Subtype.ext
    change reduceCoefficients S (MvPolynomial.C (i : S.A') -
      normalizedSection S (problemPresentationToB S (MvPolynomial.C (i : S.A')))) =
      ((0 : (Algebra.Generators.self S.A S.B).toExtension.ker) : _)
    rw [hB, normalizedSection_zero, sub_zero]
    change MvPolynomial.map (algebraMap S.A' S.A) (MvPolynomial.C (i : S.A')) = 0
    rw [MvPolynomial.map_C, hA, MvPolynomial.C_0]
  rw [twistValue, relationFunctional_apply, h, map_zero, map_zero]

end TwistValue

section TwistEval

variable (X : S.CompatibleExtension.{v})

/-- Evaluation of the canonical presentation `A'[B] → B'` at the chosen lifts of `X`. -/
public noncomputable def solutionEval : MvPolynomial S.B S.A' →ₐ[S.A'] X.B' :=
  presentationEval₁ (comparisonDiagram X X)

/-- The first presentation evaluation of the comparison diagram of `X` and `Y` is the
evaluation in `X`. -/
@[simp]
public lemma presentationEval₁_comparisonDiagram (Y : S.CompatibleExtension.{v}) :
    presentationEval₁ (comparisonDiagram X Y) = solutionEval X := rfl

/-- The evaluation in `X` lifts the presentation `A'[B] → B`. -/
@[simp]
public lemma toB_solutionEval (p : MvPolynomial S.B S.A') :
    X.toB (solutionEval X p) = problemPresentationToB S p :=
  DFunLike.congr_fun (presentationEval₁_toB (comparisonDiagram X X)) p

/-- The evaluation in `X` sends a constant `C a` to the image of `a`. -/
@[simp]
public lemma solutionEval_C (a : S.A') :
    solutionEval X (MvPolynomial.C a) = algebraMap S.A' X.B' a := by
  simp

/-- On a relation, the kernel inclusion of the relation evaluation is the evaluation in `X`. -/
public lemma kernelInclusion_solutionRelationEval
    (x : RingHom.ker (problemPresentationToB S)) :
    kernelInclusion X (solutionRelationEval X x) = solutionEval X x.1 :=
  relationEval₁_spec (comparisonDiagram X X) x

variable (δ : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N)

/-- The twisted evaluation of a polynomial lifts its image in `B`. -/
public lemma toB_mk_twistEval (p : MvPolynomial S.B S.A') :
    (TwistCarrier.mk (solutionEval X p + kernelInclusion X (twistValue δ p)) :
        TwistCarrier X δ).toB = problemPresentationToB S p := by
  rw [TwistCarrier.toB_mk, map_add, toB_kernelInclusion, add_zero, toB_solutionEval]

/-- Evaluation of the canonical presentation in the twist of `X` by `δ`: the evaluation in
`X`, corrected by the value of `δ` on the relation of the normalised section.  This is the
pushout description of the twisted extension in the Stacks proof. -/
public noncomputable def twistEval : MvPolynomial S.B S.A' →+* TwistCarrier X δ where
  toFun p := TwistCarrier.mk (solutionEval X p + kernelInclusion X (twistValue δ p))
  map_one' := by
    apply TwistCarrier.val_injective
    rw [TwistCarrier.val_mk, TwistCarrier.val_one, map_one, twistValue_one, map_neg]
    abel
  map_mul' p q := by
    apply TwistCarrier.val_injective
    have h1 : solutionEval X p * kernelInclusion X (twistValue δ q) =
        kernelInclusion X (problemPresentationToB S p • twistValue δ q) := by
      rw [mul_kernelInclusion, toB_solutionEval]
    have h2 : solutionEval X q * kernelInclusion X (twistValue δ p) =
        kernelInclusion X (problemPresentationToB S q • twistValue δ p) := by
      rw [mul_kernelInclusion, toB_solutionEval]
    have h3 : kernelInclusion X (twistValue δ p) * kernelInclusion X (twistValue δ q) = 0 :=
      kernelInclusion_mul_kernelInclusion X _ _
    simp only [TwistCarrier.val_mul, toB_mk_twistEval, map_mul, twistValue_mul, map_add]
    linear_combination -h1 - h2 - h3
  map_zero' := by
    apply TwistCarrier.val_injective
    rw [TwistCarrier.val_mk, TwistCarrier.val_zero, map_zero, twistValue_zero, map_zero,
      add_zero]
  map_add' p q := by
    apply TwistCarrier.val_injective
    simp only [TwistCarrier.val_add, toB_mk_twistEval, map_add, twistValue_add]
    abel

/-- The twisted evaluation of `p`: the evaluation in `X`, corrected by the correction term. -/
public lemma twistEval_apply (p : MvPolynomial S.B S.A') :
    twistEval X δ p =
      TwistCarrier.mk (solutionEval X p + kernelInclusion X (twistValue δ p)) := rfl

/-- The twisted evaluation lifts the presentation `A'[B] → B`. -/
@[simp]
public lemma toB_twistEval (p : MvPolynomial S.B S.A') :
    (twistEval X δ p).toB = problemPresentationToB S p :=
  toB_mk_twistEval X δ p

/-- On a relation, the twisted evaluation differs from the original one by the value of the
functional. -/
public lemma twistEval_of_mem_ker (x : RingHom.ker (problemPresentationToB S)) :
    twistEval X δ x.1 =
      TwistCarrier.mk (kernelInclusion X
        (solutionRelationEval X x + relationValue δ x.1 x.2)) := by
  rw [twistEval_apply, twistValue_of_mem_ker δ x.2, map_add,
    kernelInclusion_solutionRelationEval]

end TwistEval

end Twist

end Stacks.Deformation

end
