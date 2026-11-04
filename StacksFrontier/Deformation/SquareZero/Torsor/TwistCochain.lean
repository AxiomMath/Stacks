module

public import StacksFrontier.Deformation.SquareZero.Torsor.ObstructionClass

/-!
# The twisting cochains of a conormal functional (Stacks 08S7)

The kernel inclusion of a solution, the normalised section of `A'[B] → B`, the
relation functional and relation value of a conormal functional `δ`, and the additive
and multiplicative 2-cochains `twistAddCochain δ` and `twistMulCochain δ` with their
cocycle identities.

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

/-- The inclusion of the kernel `N` into the ring of a solution. -/
public noncomputable def kernelInclusion (X : S.CompatibleExtension.{v}) : S.N →+ X.B' where
  toFun n := ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B')
  map_zero' := congrArg Subtype.val (map_zero X.kernelEquiv)
  map_add' n m := congrArg Subtype.val (map_add X.kernelEquiv n m)

variable (X : S.CompatibleExtension.{v})

/-- The kernel inclusion sends `n` to the element `kernelEquiv n` of the ring of `X`. -/
public lemma kernelInclusion_apply (n : S.N) :
    kernelInclusion X n = ((X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') := rfl

/-- The kernel inclusion is injective. -/
public lemma kernelInclusion_injective : Function.Injective (kernelInclusion X) :=
  Subtype.coe_injective.comp X.kernelEquiv.injective

/-- The kernel inclusion lands in the kernel of the projection to `B`. -/
@[simp]
public lemma toB_kernelInclusion (n : S.N) : X.toB (kernelInclusion X n) = 0 :=
  (X.kernelEquiv n).property

/-- The product of two elements of the kernel vanishes, the kernel being square-zero. -/
public lemma kernelInclusion_mul_kernelInclusion (n m : S.N) :
    kernelInclusion X n * kernelInclusion X m = 0 := by
  have h : kernelInclusion X n * kernelInclusion X m ∈
      RingHom.ker X.toB.toRingHom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (X.kernelEquiv n).property (X.kernelEquiv m).property
  rw [X.sq_zero] at h
  simpa using h

/-- Multiplying an element of the kernel by `z` scales it by the image of `z` in `B`. -/
public lemma mul_kernelInclusion (z : X.B') (n : S.N) :
    z * kernelInclusion X n = kernelInclusion X (X.toB z • n) := by
  calc z * kernelInclusion X n
      = ((z • X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') := rfl
    _ = ((X.toB z • X.kernelEquiv n : RingHom.ker X.toB.toRingHom) : X.B') := by
        rw [X.toB_smul_kernel]
    _ = kernelInclusion X (X.toB z • n) :=
        congrArg Subtype.val (map_smul X.kernelEquiv (X.toB z) n).symm

/-- Every element of the ring of `X` mapping to zero in `B` lies in the image of the kernel
inclusion. -/
public lemma exists_eq_kernelInclusion {x : X.B'} (hx : X.toB x = 0) :
    ∃ n, kernelInclusion X n = x := by
  obtain ⟨n, hn⟩ := X.kernelEquiv.surjective
    (⟨x, RingHom.mem_ker.mpr hx⟩ : RingHom.ker X.toB.toRingHom)
  exact ⟨n, congrArg Subtype.val hn⟩

/-- The product of a polynomial with a relation of `A'[B] → B` is again a relation. -/
public def relationSmul (p : MvPolynomial S.B S.A')
    (x : RingHom.ker (problemPresentationToB S)) :
    RingHom.ker (problemPresentationToB S) :=
  ⟨p * x.1, Ideal.mul_mem_left _ p x.2⟩

/-- The product of two relations of `A'[B] → B` is again a relation. -/
public def relationMul (x y : RingHom.ker (problemPresentationToB S)) :
    RingHom.ker (problemPresentationToB S) :=
  ⟨x.1 * y.1, Ideal.mul_mem_right _ _ x.2⟩

variable (S) in
/-- A set-theoretic section of `A'[B] → B` normalised so that `0` lifts to `0`. -/
public noncomputable def normalizedSection (b : S.B) : MvPolynomial S.B S.A' :=
  MvPolynomial.X b - MvPolynomial.X (0 : S.B)

/-- The normalised section is a section of the presentation `A'[B] → B`. -/
@[simp]
public lemma problemPresentationToB_normalizedSection (b : S.B) :
    problemPresentationToB S (normalizedSection S b) = b := by
  simp [normalizedSection]

/-- The normalised section sends `0` to `0`. -/
@[simp]
public lemma normalizedSection_zero : normalizedSection S (0 : S.B) = 0 := by
  simp [normalizedSection]

variable (S) in
/-- The difference of two polynomials with the same image in `B` is a relation. -/
public def relationOfSub (p q : MvPolynomial S.B S.A')
    (hpq : problemPresentationToB S p = problemPresentationToB S q) :
    RingHom.ker (problemPresentationToB S) :=
  ⟨p - q, by
    apply RingHom.mem_ker.mpr
    rw [map_sub, hpq, sub_self]⟩

section Functional

variable (δ : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N)

/-- The additive functional on relations of `A'[B] → B` determined by a conormal
functional: reduce the relation to `A[B]`, take its conormal class, and apply the
functional. -/
public noncomputable def relationFunctional :
    RingHom.ker (problemPresentationToB S) →+ S.N where
  toFun x := δ (Algebra.Extension.Cotangent.mk (reducedRelationOf S x))
  map_zero' := by
    have h : reducedRelationOf S (0 : RingHom.ker (problemPresentationToB S)) = 0 :=
      Subtype.ext (map_zero (reduceCoefficients S))
    rw [h, map_zero, map_zero]
  map_add' x y := by
    have h : reducedRelationOf S (x + y) =
        reducedRelationOf S x + reducedRelationOf S y :=
      Subtype.ext (map_add (reduceCoefficients S) x.1 y.1)
    change δ (Algebra.Extension.Cotangent.mk (reducedRelationOf S (x + y))) = _
    rw [h, map_add, map_add]

/-- The relation functional of `δ` applies `δ` to the conormal class of the reduced
relation. -/
public lemma relationFunctional_apply (x : RingHom.ker (problemPresentationToB S)) :
    relationFunctional δ x =
      δ (Algebra.Extension.Cotangent.mk (reducedRelationOf S x)) := rfl

/-- The relation functional only depends on the underlying polynomial of a relation. -/
public lemma relationFunctional_congr {x y : RingHom.ker (problemPresentationToB S)}
    (h : x.1 = y.1) : relationFunctional δ x = relationFunctional δ y :=
  congrArg (relationFunctional δ) (Subtype.ext h)

/-- The functional vanishes on a product of two relations. -/
public lemma relationFunctional_relationMul
    (x y : RingHom.ker (problemPresentationToB S)) :
    relationFunctional δ (relationMul x y) = 0 := by
  have h : Algebra.Extension.Cotangent.mk (reducedRelationOf S (relationMul x y)) = 0 := by
    rw [Algebra.Extension.Cotangent.mk_eq_zero_iff]
    change reduceCoefficients S (x.1 * y.1) ∈ _ ^ 2
    rw [map_mul, pow_two]
    exact Ideal.mul_mem_mul (reducedRelationOf S x).2 (reducedRelationOf S y).2
  rw [relationFunctional_apply, h, map_zero]

/-- The functional is semilinear for multiplication of a relation by a polynomial. -/
public lemma relationFunctional_relationSmul (p : MvPolynomial S.B S.A')
    (x : RingHom.ker (problemPresentationToB S)) :
    relationFunctional δ (relationSmul p x) =
      problemPresentationToB S p • relationFunctional δ x := by
  have h1 : reducedRelationOf S (relationSmul p x) =
      reduceCoefficients S p • reducedRelationOf S x :=
    Subtype.ext (map_mul (reduceCoefficients S) p x.1)
  have h2 : (algebraMap (Algebra.Generators.self S.A S.B).toExtension.Ring S.B)
      (reduceCoefficients S p) = problemPresentationToB S p :=
    DFunLike.congr_fun (problemPresentationToB_factor S) p
  rw [relationFunctional_apply, h1, map_smul]
  change δ ((algebraMap (Algebra.Generators.self S.A S.B).toExtension.Ring S.B)
      (reduceCoefficients S p) • _) = _
  rw [h2, map_smul]
  rfl

/-- The functional of `δ`, evaluated on a polynomial known to be a relation. -/
public noncomputable def relationValue (p : MvPolynomial S.B S.A')
    (hp : p ∈ RingHom.ker (problemPresentationToB S)) : S.N :=
  relationFunctional δ ⟨p, hp⟩

/-- The value of `δ` on a relation only depends on the polynomial, not on the membership
proof. -/
public lemma relationValue_congr {p q : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S))
    (hq : q ∈ RingHom.ker (problemPresentationToB S)) (h : p = q) :
    relationValue δ p hp = relationValue δ q hq := by subst h; rfl

/-- The value of `δ` on the zero polynomial vanishes. -/
public lemma relationValue_eq_zero {p : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S)) (h : p = 0) :
    relationValue δ p hp = 0 := by
  subst h
  exact map_zero (relationFunctional δ)

/-- The value of `δ` on relations is additive. -/
public lemma relationValue_add {p q : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S))
    (hq : q ∈ RingHom.ker (problemPresentationToB S)) :
    relationValue δ (p + q) (add_mem hp hq) =
      relationValue δ p hp + relationValue δ q hq :=
  (map_add (relationFunctional δ) ⟨p, hp⟩ ⟨q, hq⟩ :)

/-- The value of `δ` on relations commutes with subtraction. -/
public lemma relationValue_sub {p q : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S))
    (hq : q ∈ RingHom.ker (problemPresentationToB S)) :
    relationValue δ (p - q) (sub_mem hp hq) =
      relationValue δ p hp - relationValue δ q hq :=
  (map_sub (relationFunctional δ) ⟨p, hp⟩ ⟨q, hq⟩ :)

/-- The value of `δ` on relations commutes with negation. -/
public lemma relationValue_neg {p : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S)) :
    relationValue δ (-p) (neg_mem hp) = -relationValue δ p hp :=
  map_neg (relationFunctional δ) ⟨p, hp⟩

/-- The value of `δ` on the product of a polynomial `r` with a relation is the image of `r` in
`B` acting on the value. -/
public lemma relationValue_smul (r : MvPolynomial S.B S.A') {p : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S)) :
    relationValue δ (r * p) (Ideal.mul_mem_left _ r hp) =
      problemPresentationToB S r • relationValue δ p hp :=
  relationFunctional_relationSmul δ r ⟨p, hp⟩

/-- The action of `d : B` on the value of `δ` is the value on the product with the normalised
section of `d`. -/
public lemma smul_relationValue (d : S.B) {p : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S)) :
    d • relationValue δ p hp =
      relationValue δ (normalizedSection S d * p) (Ideal.mul_mem_left _ _ hp) := by
  rw [relationValue_smul, problemPresentationToB_normalizedSection]

/-- The value of `δ` on the product of two relations vanishes. -/
public lemma relationValue_mul_eq_zero {p q : MvPolynomial S.B S.A'}
    (hp : p ∈ RingHom.ker (problemPresentationToB S))
    (hq : q ∈ RingHom.ker (problemPresentationToB S)) :
    relationValue δ (p * q) (Ideal.mul_mem_right _ _ hp) = 0 :=
  relationFunctional_relationMul δ ⟨p, hp⟩ ⟨q, hq⟩

/-- The additive defect of the normalised section is a relation. -/
public lemma normalizedSection_add_mem (b c : S.B) :
    normalizedSection S (b + c) - normalizedSection S b - normalizedSection S c ∈
      RingHom.ker (problemPresentationToB S) := by
  apply RingHom.mem_ker.mpr
  simp

/-- The multiplicative defect of the normalised section is a relation. -/
public lemma normalizedSection_mul_mem (b c : S.B) :
    normalizedSection S b * normalizedSection S c - normalizedSection S (b * c) ∈
      RingHom.ker (problemPresentationToB S) := by
  apply RingHom.mem_ker.mpr
  simp

/-- The normalised section of `1` differs from `1` by a relation. -/
public lemma normalizedSection_one_sub_one_mem :
    normalizedSection S (1 : S.B) - 1 ∈ RingHom.ker (problemPresentationToB S) := by
  apply RingHom.mem_ker.mpr
  simp

/-- The 2-cochain by which the twisted addition differs from the original one. -/
public noncomputable def twistAddCochain (b c : S.B) : S.N :=
  -relationValue δ _ (normalizedSection_add_mem (S := S) b c)

/-- The 2-cochain by which the twisted multiplication differs from the original one. -/
public noncomputable def twistMulCochain (b c : S.B) : S.N :=
  relationValue δ _ (normalizedSection_mul_mem (S := S) b c)

/-- The additive cochain is symmetric. -/
public lemma twistAddCochain_comm (b c : S.B) :
    twistAddCochain δ b c = twistAddCochain δ c b := by
  unfold twistAddCochain
  congr 1
  apply relationValue_congr
  rw [add_comm b c]
  ring

/-- The multiplicative cochain is symmetric. -/
public lemma twistMulCochain_comm (b c : S.B) :
    twistMulCochain δ b c = twistMulCochain δ c b := by
  unfold twistMulCochain
  apply relationValue_congr
  rw [mul_comm b c]
  ring

/-- The additive cochain vanishes when its first argument is `0`. -/
@[simp]
public lemma twistAddCochain_zero_left (c : S.B) : twistAddCochain δ 0 c = 0 := by
  unfold twistAddCochain
  rw [neg_eq_zero]
  apply relationValue_eq_zero
  rw [zero_add, normalizedSection_zero]
  ring

/-- The multiplicative cochain vanishes when its second argument is `0`. -/
@[simp]
public lemma twistMulCochain_zero_right (b : S.B) : twistMulCochain δ b 0 = 0 := by
  unfold twistMulCochain
  apply relationValue_eq_zero
  rw [mul_zero, normalizedSection_zero]
  ring

/-- The additive cochain satisfies the cocycle identity. -/
public lemma twistAddCochain_cocycle (a b c : S.B) :
    twistAddCochain δ a b + twistAddCochain δ (a + b) c =
      twistAddCochain δ b c + twistAddCochain δ a (b + c) := by
  unfold twistAddCochain
  rw [← neg_add, ← neg_add, neg_inj, ← relationValue_add, ← relationValue_add]
  apply relationValue_congr
  rw [add_assoc a b c]
  ring

/-- The multiplicative cochain satisfies the cocycle identity for the `B`-module `N`. -/
public lemma twistMulCochain_cocycle (a b c : S.B) :
    c • twistMulCochain δ a b + twistMulCochain δ (a * b) c =
      a • twistMulCochain δ b c + twistMulCochain δ a (b * c) := by
  unfold twistMulCochain
  rw [smul_relationValue, smul_relationValue, ← relationValue_add, ← relationValue_add]
  apply relationValue_congr
  rw [mul_assoc a b c]
  ring

/-- The compatibility of the two cochains which yields distributivity of the twisted
operations. -/
public lemma twistCochain_distrib (a b c : S.B) :
    a • twistAddCochain δ b c + twistMulCochain δ a (b + c) =
      twistMulCochain δ a b + twistMulCochain δ a c + twistAddCochain δ (a * b) (a * c) := by
  unfold twistAddCochain twistMulCochain
  rw [smul_neg, smul_relationValue, ← relationValue_neg, ← relationValue_add,
    ← relationValue_neg, ← relationValue_add, ← relationValue_add]
  apply relationValue_congr
  rw [mul_add a b c]
  ring

/-- The multiplicative cochain at `(1, b)` is `b` acting on its value at `(1, 1)`. -/
public lemma twistMulCochain_one_left (b : S.B) :
    twistMulCochain δ 1 b = b • twistMulCochain δ 1 1 := by
  have hw := normalizedSection_one_sub_one_mem (S := S)
  have hzero : relationValue δ
      (-normalizedSection S b *
        ((normalizedSection S (1 : S.B) - 1) * (normalizedSection S (1 : S.B) - 1)))
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hw)) = 0 := by
    rw [relationValue_smul δ (-normalizedSection S b) (Ideal.mul_mem_right _ _ hw),
      relationValue_mul_eq_zero δ hw hw, smul_zero]
  unfold twistMulCochain
  rw [smul_relationValue, ← sub_eq_zero, ← relationValue_sub]
  refine Eq.trans (relationValue_congr δ _ _ ?_) hzero
  rw [mul_one (1 : S.B), one_mul b]
  ring

end Functional

end Twist

end Stacks.Deformation

end
