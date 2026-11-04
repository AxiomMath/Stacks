module

public import Mathlib.Algebra.Torsor.Defs
public import StacksFrontier.Deformation.SquareZero.Torsor.TwistCarrier
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The torsor of isomorphism classes of solutions (Stacks 08S7)

The twisted solution `twistExtension X δ`, the computation of its obstruction class,
which shows that every class is realised, and the principal homogeneous space structure
on isomorphism classes of solutions under `Ext¹_B(NL_{B/A}, N)`.

Part of `StacksFrontier.Deformation.SquareZero.Torsor`; see that module for the overview of
Stacks 08S7.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u₃ u₄ v

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

variable {S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄}}

section TwistExtension

variable (X : S.CompatibleExtension.{v})
  (δ : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N)

/-- The `A'`-algebra structure on the twist of `X` by `δ`, obtained from the twisted
evaluation of the canonical presentation. -/
public noncomputable instance twistAlgebra : Algebra S.A' (TwistCarrier X δ) :=
  ((twistEval X δ).comp (algebraMap S.A' (MvPolynomial S.B S.A'))).toAlgebra

/-- The structure map of the twist sends `a` to the twisted evaluation of the constant `C a`. -/
public lemma algebraMap_twistCarrier (a : S.A') :
    algebraMap S.A' (TwistCarrier X δ) a = twistEval X δ (MvPolynomial.C a) := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, MvPolynomial.algebraMap_eq]

/-- The projection from the twist of `X` by `δ` onto `B`. -/
public noncomputable def twistToB : TwistCarrier X δ →ₐ[S.A'] S.B where
  toFun := TwistCarrier.toB
  map_one' := TwistCarrier.toB_one
  map_mul' := TwistCarrier.toB_mul
  map_zero' := TwistCarrier.toB_zero
  map_add' := TwistCarrier.toB_add
  commutes' a := by
    rw [algebraMap_twistCarrier, toB_twistEval, problemPresentationToB_C]

/-- The projection from the twist to `B` is the image in `B`. -/
@[simp]
public lemma twistToB_apply (x : TwistCarrier X δ) : twistToB X δ x = x.toB := rfl

/-- The projection from the twist to `B` is surjective. -/
public lemma twistToB_surjective : Function.Surjective (twistToB X δ) := by
  intro b
  obtain ⟨y, hy⟩ := X.surjective b
  exact ⟨TwistCarrier.mk y, hy⟩

/-- The image of an element of the kernel lies in the kernel of the twisted projection. -/
public lemma mk_kernelInclusion_mem_ker (n : S.N) :
    (TwistCarrier.mk (kernelInclusion X n) : TwistCarrier X δ) ∈
      RingHom.ker (twistToB X δ).toRingHom := by
  apply RingHom.mem_ker.mpr
  change (TwistCarrier.mk (kernelInclusion X n) : TwistCarrier X δ).toB = 0
  rw [TwistCarrier.toB_mk, toB_kernelInclusion]

/-- The kernel of the twisted projection is square-zero. -/
public lemma twistToB_sq_zero : RingHom.ker (twistToB X δ).toRingHom ^ 2 = ⊥ := by
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.mpr ?_) bot_le
  intro r hr s hs
  have hr0 : r.toB = 0 := RingHom.mem_ker.mp hr
  have hs0 : s.toB = 0 := RingHom.mem_ker.mp hs
  have hz : r.val * s.val = 0 :=
    squareZero_kernel_mul X.toB.toRingHom X.sq_zero
      ⟨r.val, RingHom.mem_ker.mpr hr0⟩ ⟨s.val, RingHom.mem_ker.mpr hs0⟩
  rw [Ideal.mem_bot]
  apply TwistCarrier.val_injective
  rw [TwistCarrier.val_mul, TwistCarrier.val_zero, hz, hr0, hs0,
    twistMulCochain_zero_right, map_zero, add_zero]

/-- The inclusion of `N` into the kernel of the twisted projection. -/
public noncomputable def twistKernelHom : S.N →+ RingHom.ker (twistToB X δ).toRingHom where
  toFun n := ⟨TwistCarrier.mk (kernelInclusion X n), mk_kernelInclusion_mem_ker X δ n⟩
  map_zero' := by
    apply Subtype.ext
    change (TwistCarrier.mk (kernelInclusion X 0) : TwistCarrier X δ) =
      ((0 : RingHom.ker (twistToB X δ).toRingHom) : TwistCarrier X δ)
    rw [map_zero]
    rfl
  map_add' n m := by
    apply Subtype.ext
    change (TwistCarrier.mk (kernelInclusion X (n + m)) : TwistCarrier X δ) =
      TwistCarrier.mk (kernelInclusion X n) + TwistCarrier.mk (kernelInclusion X m)
    rw [TwistCarrier.mk_kernelInclusion_add]

/-- The inclusion of `N` into the kernel of the twisted projection, on underlying elements. -/
@[simp]
public lemma twistKernelHom_coe (n : S.N) :
    ((twistKernelHom X δ n : RingHom.ker (twistToB X δ).toRingHom) : TwistCarrier X δ) =
      TwistCarrier.mk (kernelInclusion X n) := rfl

/-- The inclusion of `N` into the kernel of the twisted projection is injective. -/
public lemma twistKernelHom_injective : Function.Injective (twistKernelHom X δ) := by
  intro n m h
  exact kernelInclusion_injective X (congrArg TwistCarrier.val (congrArg Subtype.val h))

/-- The inclusion of `N` into the kernel of the twisted projection is surjective. -/
public lemma twistKernelHom_surjective : Function.Surjective (twistKernelHom X δ) := by
  intro x
  have hx : X.toB x.1.val = 0 := RingHom.mem_ker.mp x.2
  obtain ⟨n, hn⟩ := exists_eq_kernelInclusion X hx
  refine ⟨n, Subtype.ext ?_⟩
  rw [twistKernelHom_coe, hn]

/-- The kernel of the twisted projection is identified with `N`. -/
public noncomputable def twistKernelEquiv : S.N ≃+ RingHom.ker (twistToB X δ).toRingHom :=
  AddEquiv.ofBijective (twistKernelHom X δ)
    ⟨twistKernelHom_injective X δ, twistKernelHom_surjective X δ⟩

/-- The identification of `N` with the kernel of the twisted projection, on underlying
elements. -/
@[simp]
public lemma twistKernelEquiv_coe (n : S.N) :
    ((twistKernelEquiv X δ n : RingHom.ker (twistToB X δ).toRingHom) :
      TwistCarrier X δ) = TwistCarrier.mk (kernelInclusion X n) := rfl

/-- The `B`-action on the kernel of the twisted projection, transported from `N`. -/
@[instance_reducible]
public noncomputable def twistKernelSMul :
    SMul S.B (RingHom.ker (twistToB X δ).toRingHom) :=
  ⟨fun b x ↦ twistKernelEquiv X δ (b • (twistKernelEquiv X δ).symm x)⟩

/-- The `B`-module structure on the kernel of the twisted projection, transported from
`N`. -/
@[instance_reducible]
public noncomputable def twistKernelModule :
    Module S.B (RingHom.ker (twistToB X δ).toRingHom) :=
  @Function.Injective.module S.B S.N _ _ _ _ _ (twistKernelSMul X δ)
    (twistKernelEquiv X δ).symm.toAddMonoidHom (twistKernelEquiv X δ).symm.injective
    (fun b x ↦ (twistKernelEquiv X δ).symm_apply_apply (b • (twistKernelEquiv X δ).symm x))

/-- The twist of a solution `X` by a conormal functional `δ`, which is again a solution of
the same square-zero extension problem. -/
public noncomputable def twistExtension : S.CompatibleExtension.{v} :=
  let : Module S.B (RingHom.ker (twistToB X δ).toRingHom) := twistKernelModule X δ
  { B' := TwistCarrier X δ
    toB := twistToB X δ
    surjective := twistToB_surjective X δ
    sq_zero := twistToB_sq_zero X δ
    toB_smul_kernel := fun b' x ↦ by
      apply Subtype.ext
      change ((twistKernelEquiv X δ
          (b'.toB • (twistKernelEquiv X δ).symm x) :
            RingHom.ker (twistToB X δ).toRingHom) : TwistCarrier X δ) = b' * x.1
      rw [twistKernelEquiv_coe, ← TwistCarrier.mul_mk_kernelInclusion b' _,
        ← twistKernelEquiv_coe X δ ((twistKernelEquiv X δ).symm x),
        AddEquiv.apply_symm_apply]
    kernelEquiv :=
      { __ := twistKernelEquiv X δ
        map_smul' := fun b n ↦ by
          change twistKernelEquiv X δ (b • n) =
            twistKernelEquiv X δ (b • (twistKernelEquiv X δ).symm (twistKernelEquiv X δ n))
          rw [AddEquiv.symm_apply_apply] }
    map_I := fun i ↦ by
      rw [algebraMap_twistCarrier, twistEval_apply, twistValue_C_of_mem_I, map_zero,
        add_zero, solutionEval_C]
      change (TwistCarrier.mk (kernelInclusion X (S.c i)) : TwistCarrier X δ) =
        TwistCarrier.mk (algebraMap S.A' X.B' (i : S.A'))
      rw [kernelInclusion_apply, X.map_I i] }

/-- The projection of the twisted extension is the image in `B`. -/
@[simp]
public lemma twistExtension_toB (x : TwistCarrier X δ) :
    (twistExtension X δ).toB x = x.toB := rfl

/-- The kernel inclusion of the twisted extension is that of `X`, read in the twist. -/
@[simp]
public lemma kernelInclusion_twistExtension (n : S.N) :
    kernelInclusion (twistExtension X δ) n =
      TwistCarrier.mk (kernelInclusion X n) := rfl

end TwistExtension

section Surjective

variable (X : S.CompatibleExtension.{v})
  (δ : (Algebra.Generators.self S.A S.B).toExtension.Cotangent →ₗ[S.B] S.N)

/-- The value of `δ` on a relation applies `δ` to its reduced conormal class. -/
public lemma relationValue_eq_apply (x : RingHom.ker (problemPresentationToB S)) :
    relationValue δ x.1 x.2 =
      δ (Algebra.Extension.Cotangent.mk (reducedRelationOf S x)) := rfl

/-- The lifts of the variables of the canonical presentation in the twist, at which the
twisted evaluation is the polynomial evaluation.  The type is spelled through the
comparison diagram, which is where these lifts are used. -/
public noncomputable def twistLift
    (b : (comparisonDiagram X (twistExtension X δ)).S₁.B) :
    (comparisonDiagram X (twistExtension X δ)).X₂.B' :=
  twistEval X δ (MvPolynomial.X b)

/-- The lifts in the twist are lifts of the variables. -/
public lemma twistLift_spec (b : (comparisonDiagram X (twistExtension X δ)).S₁.B) :
    (comparisonDiagram X (twistExtension X δ)).X₂.toB (twistLift X δ b) =
      algebraMap (comparisonDiagram X (twistExtension X δ)).S₁.B
        (comparisonDiagram X (twistExtension X δ)).S₂.B b :=
  (toB_twistEval X δ (MvPolynomial.X (show S.B from b))).trans
    (problemPresentationToB_X S (show S.B from b))

/-- Evaluating the canonical presentation at these lifts is exactly the twisted
evaluation. -/
public lemma presentationEval₂With_twistLift :
    presentationEval₂With (comparisonDiagram X (twistExtension X δ)) (twistLift X δ) =
      (twistEval X δ : MvPolynomial S.B S.A' →+* TwistCarrier X δ) := by
  apply MvPolynomial.ringHom_ext'
  · refine RingHom.ext fun a ↦ ?_
    change presentationEval₂With (comparisonDiagram X (twistExtension X δ)) (twistLift X δ)
        (MvPolynomial.C a) = algebraMap S.A' (TwistCarrier X δ) a
    simp only [presentationEval₂With, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_C]
    rfl
  · intro b
    change presentationEval₂With (comparisonDiagram X (twistExtension X δ)) (twistLift X δ)
        (MvPolynomial.X b) = twistLift X δ b
    simp [presentationEval₂With]

/-- Evaluating the canonical presentation at the lifts in the twist is the twisted
evaluation, pointwise. -/
public lemma presentationEval₂With_twistLift_apply (p : MvPolynomial S.B S.A') :
    presentationEval₂With (comparisonDiagram X (twistExtension X δ)) (twistLift X δ) p =
      twistEval X δ p :=
  DFunLike.congr_fun (presentationEval₂With_twistLift X δ) p

/-- The evaluation of the canonical presentation in the twist at the *chosen* lifts of the
twist, which is what the obstruction functional is built from. -/
public noncomputable def twistCanonicalEval (p : MvPolynomial S.B S.A') :
    TwistCarrier X δ :=
  presentationEval₂ (comparisonDiagram X (twistExtension X δ)) p

/-- The functional on the free cotangent space recording how passing to the twist changes
the evaluation of the canonical presentation. -/
public noncomputable def twistCorrection :
    (Algebra.Generators.self S.A S.B).toExtension.CotangentSpace →ₗ[S.B] S.N :=
  evaluationDifferenceLinear (comparisonDiagram X (twistExtension X δ))
    (twistLift X δ) (twistLift_spec X δ)

/-- The change of evaluation on a relation, between the twisted evaluation and the chosen
evaluation in the twist. -/
public noncomputable def twistEvaluationDifference
    (x : RingHom.ker (problemPresentationToB S)) : S.N :=
  evaluationDifferenceWith (comparisonDiagram X (twistExtension X δ)) (twistLift X δ)
    (twistLift_spec X δ) x.1

/-- The kernel inclusion into the twist is injective. -/
public lemma mk_kernelInclusion_inj {n m : S.N}
    (h : (TwistCarrier.mk (kernelInclusion X n) : TwistCarrier X δ) =
      TwistCarrier.mk (kernelInclusion X m)) : n = m :=
  twistKernelHom_injective X δ (Subtype.ext h)

/-- The change of evaluation on a relation, read in the twist, is the difference of the
twisted and the chosen evaluations. -/
public lemma mk_kernelInclusion_twistEvaluationDifference
    (x : RingHom.ker (problemPresentationToB S)) :
    (TwistCarrier.mk (kernelInclusion X (twistEvaluationDifference X δ x)) :
        TwistCarrier X δ) =
      twistEval X δ x.1 - twistCanonicalEval X δ x.1 :=
  (evaluationDifferenceWith_spec (comparisonDiagram X (twistExtension X δ))
      (twistLift X δ) (twistLift_spec X δ) x.1).trans
    (congrArg (fun w : TwistCarrier X δ ↦ w - twistCanonicalEval X δ x.1)
      (presentationEval₂With_twistLift_apply X δ x.1))

/-- The difference of the relation evaluations in the twist and in `X`, read in the twist, is
the chosen evaluation in the twist minus the evaluation in `X`. -/
public lemma mk_kernelInclusion_solutionRelationEval_sub
    (x : RingHom.ker (problemPresentationToB S)) :
    (TwistCarrier.mk (kernelInclusion X
        (solutionRelationEval (twistExtension X δ) x - solutionRelationEval X x)) :
        TwistCarrier X δ) =
      twistCanonicalEval X δ x.1 -
        TwistCarrier.mk (kernelInclusion X (solutionRelationEval X x)) :=
  relationDifference_spec (comparisonDiagram X (twistExtension X δ)) x

/-- The key computation of the Stacks proof: on a relation, the change of evaluation
accounts exactly for the value of `δ`. -/
public lemma twistEvaluationDifference_spec
    (x : RingHom.ker (problemPresentationToB S)) :
    twistEvaluationDifference X δ x +
      (solutionRelationEval (twistExtension X δ) x - solutionRelationEval X x) =
      relationValue δ x.1 x.2 := by
  refine mk_kernelInclusion_inj X δ ?_
  rw [← TwistCarrier.mk_kernelInclusion_add,
    mk_kernelInclusion_twistEvaluationDifference,
    mk_kernelInclusion_solutionRelationEval_sub, sub_add_sub_cancel, twistEval_of_mem_ker,
    TwistCarrier.mk_kernelInclusion_sub, add_sub_cancel_left]

/-- The correction functional computes the change of evaluation, through the differential
of the canonical presentation. -/
public lemma twistCorrection_cotangentComplex
    (x : RingHom.ker (problemPresentationToB S)) :
    twistCorrection X δ
        ((Algebra.Generators.self S.A S.B).toExtension.cotangentComplex
          (Algebra.Extension.Cotangent.mk (reducedRelationOf S x))) =
      twistEvaluationDifference X δ x := by
  have hcc : (Algebra.Generators.self S.A S.B).toExtension.cotangentComplex
        (Algebra.Extension.Cotangent.mk (reducedRelationOf S x)) =
      reducedPolynomialDifferential (comparisonDiagram X (twistExtension X δ)) x.1 :=
    cotangentComplex_reducedRelation (comparisonDiagram X (twistExtension X δ)) x
  exact (congrArg (fun y ↦ twistCorrection X δ y) hcc).trans
    (evaluationDifferenceWith_eq_differential (comparisonDiagram X (twistExtension X δ))
      (twistLift X δ) (twistLift_spec X δ) (twistCorrection X δ)
      (fun b ↦ (evaluationDifferenceLinear_basis (comparisonDiagram X (twistExtension X δ))
        (twistLift X δ) (twistLift_spec X δ) b).symm) x.1).symm

/-- The obstruction functional from `X` to its twist by `δ` differs from `δ` by a
functional pulled back along the conormal differential; so the two have the same class. -/
public lemma obstructionFunctional_twistExtension :
    obstructionFunctional X (twistExtension X δ) - δ =
      LinearMap.lcomp S.B S.N
        (Algebra.Generators.self S.A S.B).toExtension.cotangentComplex
        (-twistCorrection X δ) := by
  apply conormalFunctional_ext
  intro x
  rw [LinearMap.sub_apply, obstructionFunctional_mk, LinearMap.lcomp_apply,
    LinearMap.neg_apply, twistCorrection_cotangentComplex, ← relationValue_eq_apply δ x,
    ← twistEvaluationDifference_spec X δ x]
  abel

/-- The obstruction class from `X` to its twist by `δ` is the class of `δ`. -/
public lemma obstructionCokernelClass_twistExtension :
    obstructionCokernelClass X (twistExtension X δ) = Submodule.Quotient.mk δ := by
  change Submodule.Quotient.mk (obstructionFunctional X (twistExtension X δ)) =
    Submodule.Quotient.mk δ
  rw [Submodule.Quotient.eq]
  exact LinearMap.mem_range.mpr ⟨_, (obstructionFunctional_twistExtension X δ).symm⟩

end Surjective

/-- Every conormal class is the obstruction class of a second solution: twist the given
solution by a representative of the class, as in the Stacks proof. -/
public lemma exists_obstructionCokernelClass_eq (X : S.CompatibleExtension.{v})
    (q : conormalCokernel S) :
    ∃ Y : S.CompatibleExtension.{v}, obstructionCokernelClass X Y = q := by
  obtain ⟨δ, hδ⟩ := Quotient.exists_rep q
  refine ⟨twistExtension X δ, ?_⟩
  rw [obstructionCokernelClass_twistExtension]
  exact hδ

/-- A bijection of a nonempty type with an additive group makes it a principal homogeneous
space under that group: translate and subtract through the bijection. -/
@[instance_reducible]
public noncomputable def addTorsorOfEquiv {G : Type*} {P : Type*} [AddGroup G] [Nonempty P]
    (e : P ≃ G) : AddTorsor G P where
  vadd g p := e.symm (g + e p)
  vsub p₁ p₂ := e p₁ - e p₂
  zero_vadd p := show e.symm (0 + e p) = p by simp
  add_vadd g₁ g₂ p :=
    show e.symm (g₁ + g₂ + e p) = e.symm (g₁ + e (e.symm (g₂ + e p))) by simp [add_assoc]
  vsub_vadd' p₁ p₂ := show e.symm (e p₁ - e p₂ + e p₂) = p₁ by simp
  vadd_vsub' g p := show e (e.symm (g + e p)) - e p = g by simp

section Torsor

variable (h : Nonempty (SquareZeroExtensionProblem.CompatibleExtension.{v} S))

/-- The obstruction class relative to a chosen solution, as a function on isomorphism
classes. -/
public noncomputable def obstructionCokernelClassMap :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄, v} S →
      conormalCokernel S :=
  Quotient.lift (fun Y ↦ obstructionCokernelClass h.some Y)
    (fun _ _ r ↦ (obstructionCokernelClass_congr_right r.some).symm)

/-- The obstruction class map at the class of `Y` is the obstruction class from the chosen
solution to `Y`. -/
@[simp]
public lemma obstructionCokernelClassMap_mk (Y : S.CompatibleExtension.{v}) :
    obstructionCokernelClassMap h
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) Y) =
      obstructionCokernelClass h.some Y := rfl

/-- The obstruction class of a pair, expressed through a chosen base solution. -/
public lemma obstructionCokernelClass_sub (X Y : S.CompatibleExtension.{v}) :
    obstructionCokernelClass h.some Y - obstructionCokernelClass h.some X =
      obstructionCokernelClass X Y := by
  have h₁ := obstructionCokernelClass_add X h.some Y
  rw [obstructionCokernelClass_comm h.some X] at h₁
  rw [← h₁]
  abel

/-- Isomorphism classes of solutions are in bijection with the conormal cokernel, once a
solution has been chosen. -/
public noncomputable def isomorphismClassesEquivCokernel :
    SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄, v} S ≃
      conormalCokernel S :=
  Equiv.ofBijective (obstructionCokernelClassMap h) (by
    refine ⟨fun p q hpq => ?_, fun q => ?_⟩
    · induction p using Quotient.ind with
      | _ X =>
      induction q using Quotient.ind with
      | _ Y =>
      rw [obstructionCokernelClassMap_mk, obstructionCokernelClassMap_mk] at hpq
      exact Quotient.sound ((obstructionCokernelClass_eq_zero_iff X Y).mp
        (by rw [← obstructionCokernelClass_sub h X Y, hpq, sub_self]))
    · obtain ⟨Y, hY⟩ := exists_obstructionCokernelClass_eq h.some q
      exact ⟨Quotient.mk _ Y, hY⟩)

/-- The isomorphism classes of solutions form a principal homogeneous space under the
conormal cokernel. -/
@[instance_reducible]
public noncomputable def isomorphismClassesCokernelTorsor :
    AddTorsor (conormalCokernel S)
      (SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄, v}
        S) :=
  have : Nonempty
      (SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄, v}
        S) := ⟨Quotient.mk _ h.some⟩
  addTorsorOfEquiv (isomorphismClassesEquivCokernel h)

/-- In the torsor of isomorphism classes, `[Y] -ᵥ [X]` is the obstruction class of `(X, Y)`. -/
public lemma isomorphismClassesCokernelTorsor_vsub (X Y : S.CompatibleExtension.{v}) :
    @VSub.vsub (conormalCokernel S)
        (SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses S)
        (isomorphismClassesCokernelTorsor h).toVSub
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) Y)
        (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) X) =
      obstructionCokernelClass X Y :=
  obstructionCokernelClass_sub h X Y


/-- If a square-zero extension problem has a solution, this is the canonical principal
homogeneous-space structure on its isomorphism classes under `Ext¹_B(NL_{B/A}, N)`. -/
@[stacks 08S7, instance_reducible, sga "7 VI 4.16" "(b), affine case"]
public noncomputable def isomorphismClassesTorsor
    (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})
    (h : Nonempty (SquareZeroExtensionProblem.CompatibleExtension.{v} S)) :
    AddTorsor (naiveCotangentExtOne S.A S.B S.N)
      (SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄, v}
        S) :=
  have : Nonempty
      (SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses.{u₁, u₂, u₃, u₄, v}
        S) := ⟨Quotient.mk _ h.some⟩
  addTorsorOfEquiv
    ((isomorphismClassesEquivCokernel h).trans (extCokernelIso S.A S.B S.N).toEquiv.symm)

/-- In the canonical torsor of solutions, the difference `[Y] -ᵥ [X]` is the obstruction
class `o(X, Y)` to a map from `X` to `Y`. -/
@[stacks 08S7 "canonical difference"]
public theorem isomorphismClasses_vsub_eq_obstructionClass
    (S : SquareZeroExtensionProblem.{u₁, u₂, u₃, u₄})
    (h : Nonempty (SquareZeroExtensionProblem.CompatibleExtension.{v} S))
    (X Y : S.CompatibleExtension.{v}) :
    (@VSub.vsub
      (naiveCotangentExtOne S.A S.B S.N)
      (SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses S)
      (isomorphismClassesTorsor S h).toVSub
      (Quotient.mk
          (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) Y :
          SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses S)
      (Quotient.mk
          (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid S) X :
          SquareZeroExtensionProblem.CompatibleExtension.IsomorphismClasses S) =
      (obstructionClass (comparisonDiagram X Y)).1) := by
  change (extCokernelIso S.A S.B S.N).symm (obstructionCokernelClass h.some Y) -
      (extCokernelIso S.A S.B S.N).symm (obstructionCokernelClass h.some X) =
    (obstructionClass (comparisonDiagram X Y)).1
  rw [← map_sub, obstructionCokernelClass_sub h X Y]
  rfl

end Torsor

end Stacks.Deformation

end
