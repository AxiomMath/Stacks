module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction

/-!
# Evaluation at one for differential graded modules

Let `φ : A → B` be a homomorphism of differential graded algebras over a commutative ring `R`
and let `N` be a right differential graded `B`-module. The graded Hom from the regular module
`B`, viewed as a right differential graded `A`-module, is canonically the restriction of `N`
along `φ`, and the isomorphism is evaluation at the unit `1 ∈ B`; it is compatible with the
differentials and natural in `N`.

## Main definitions

* `DifferentialGradedModule.regularModule`: a differential graded algebra regarded as a right
  differential graded module over itself.
* `DifferentialGradedModule.EvaluationAtOneData`: the graded Hom module out of the regular
  module, its identification with the homogeneous maps in each degree, and the natural
  evaluation isomorphism.

## Main results

* `DifferentialGradedModule.evaluationAtOne`: evaluation at one, as a natural isomorphism of
  differential graded modules.

## Implementation notes

The homogeneous Hom modules are those of the differential graded category of differential graded
modules, `DifferentialGradedModule.homogeneousMapSubmodule`, applied to the regular module; the
data bundles the graded Hom together with the degreewise identifications rather than relying on
a total graded Hom module, which the differential graded category does not provide. Bijectivity
of the evaluation morphism is what makes it an isomorphism of differential graded modules.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public section

namespace DifferentialGradedModule

universe u v

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, v} R}

/-- The regular right differential graded module over a differential graded algebra: the algebra
itself, acting on itself on the right. -/
public abbrev regularModule (B : DifferentialGradedAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v, v} B where
  M := B.A
  grading := B.grading
  d := B.d
  d_comp_d := B.d_comp_d
  d_mem := B.d_mem
  smul_mem := by
    intro n m x a hx ha
    simpa [MulOpposite.smul_eq_mul_unop] using SetLike.mul_mem_graded hx ha
  leibniz := by
    intro n m x a hx ha
    simpa [MulOpposite.smul_eq_mul_unop] using B.leibniz n m x a hx ha

/-- The natural graded Hom from the regular `B`-module, together with evaluation at one. -/
public structure EvaluationAtOneData (φ : A.Hom B) where
  hom : DifferentialGradedModule.{u, v, v} B → DifferentialGradedModule.{u, v, v} A
  homogeneousEquiv : ∀ (N : DifferentialGradedModule.{u, v, v} B) (n : ℤ),
    (hom N).grading n ≃ₗ[R] homogeneousMapSubmodule B (regularModule B) N n
  map : ∀ {N N' : DifferentialGradedModule.{u, v, v} B},
    Hom N N' → Hom (hom N) (hom N')
  differential : ∀ (N : DifferentialGradedModule.{u, v, v} B) (n : ℤ)
      (f : (hom N).grading n),
    (homogeneousEquiv N (n + 1)
      ⟨(hom N).d f, (hom N).d_mem n f f.property⟩).1 =
      N.d ∘ₗ (homogeneousEquiv N n f).1 -
        DifferentialGraded.gradedSign R n • ((homogeneousEquiv N n f).1 ∘ₗ (regularModule B).d)
  evaluation : ∀ N : DifferentialGradedModule.{u, v, v} B,
    Hom (hom N) (restrictScalars φ N)
  evaluation_apply : ∀ (N : DifferentialGradedModule.{u, v, v} B)
      (n : ℤ) (f : (hom N).grading n),
    (evaluation N).toFun f =
      ((homogeneousEquiv N n f).1 : B.A →ₗ[R] N.M) (1 : B.A)
  evaluation_bijective : ∀ N : DifferentialGradedModule.{u, v, v} B,
    Function.Bijective (evaluation N).toFun
  evaluation_natural : ∀ {N N' : DifferentialGradedModule.{u, v, v} B}
      (g : Hom N N'),
    (evaluation N').toFun ∘ₗ (map g).toFun =
      g.toFun ∘ₗ (evaluation N).toFun

/-- Evaluation at the unit identifies the graded Hom from `B` with restriction to `A`,
naturally in the differential graded `B`-module. -/
@[stacks 0BYX "evaluation_at_one"]
public noncomputable def evaluationAtOne (φ : A.Hom B) :
    EvaluationAtOneData φ := by
  refine
    { hom := fun N => restrictScalars φ N
      homogeneousEquiv := ?_
      map := ?_
      differential := ?_
      evaluation := ?_
      evaluation_apply := ?_
      evaluation_bijective := ?_
      evaluation_natural := ?_ }
  · intro N n
    let _ : Module (MulOpposite B.A) N.M := N.rmodule
    let _ : IsScalarTower R (MulOpposite B.A) N.M := N.isScalarTower
    let toMaps : N.grading n →ₗ[R] homogeneousMapSubmodule B (regularModule B) N n := {
      toFun x :=
        ⟨{ toFun := fun b => MulOpposite.op b • (x : N.M)
           map_add' := by intro b c; simp [add_smul]
           map_smul' := by
             intro r b
             change MulOpposite.op (r • b) • (x : N.M) =
               r • (MulOpposite.op b • (x : N.M))
             rw [Algebra.smul_def, MulOpposite.op_mul, mul_smul, ← MulOpposite.algebraMap_apply]
             rw [IsScalarTower.algebraMap_smul (R := R)
               (A := MulOpposite B.A) (M := N.M) r (x : N.M)]
             exact SMulCommClass.smul_comm (MulOpposite.op b) r (x : N.M) },
          ⟨by intro i b hb; simpa [add_comm] using N.smul_mem n i (x : N.M) b x.property hb,
           by
            intro a b
            change MulOpposite.op (b * a) • (x : N.M) =
              MulOpposite.op a •
                (MulOpposite.op b • (x : N.M))
            rw [← mul_smul]; simp [MulOpposite.op_mul]⟩⟩
      map_add' := by
        intro x y; apply Subtype.ext; ext b; simp [smul_add]
      map_smul' := by
        intro r x; apply Subtype.ext; ext b
        change MulOpposite.op b • (r • (x : N.M)) =
          r • (MulOpposite.op b • (x : N.M))
        exact SMulCommClass.smul_comm (MulOpposite.op b) r (x : N.M)
    }
    let fromMaps : homogeneousMapSubmodule B (regularModule B) N n →ₗ[R] N.grading n := {
      toFun f := ⟨f.1 1, by
        simpa [zero_add] using f.2.1 0 1 (SetLike.one_mem_graded B.grading)⟩
      map_add' := by intro f g; apply Subtype.ext; rfl
      map_smul' := by intro r f; apply Subtype.ext; rfl
    }
    exact LinearEquiv.ofLinearMap toMaps fromMaps (by
      ext f b
      have h := f.2.2 b 1
      change MulOpposite.op b • f.1 1 = f.1 b
      have hunit : MulOpposite.op b • (1 : B.A) = b := by
        simp [MulOpposite.smul_eq_mul_unop]
      rw [hunit] at h; exact h.symm) (by
      ext x
      let y : N.M := x.val
      change MulOpposite.op (1 : B.A) • y = y
      simp)
  · intro N N' g
    let _ : Module (MulOpposite B.A) N.M := N.rmodule
    let _ : Module (MulOpposite B.A) N'.M := N'.rmodule
    refine { toFun := g.toFun, map_smul := ?_, map_grading := ?_, map_d := g.map_d }
    · intro x a; exact g.map_smul x (φ.toAlgebraHom a)
    · intro n x hx; simpa [restrictScalars] using g.map_grading n x hx
  · intro N n f
    let _ : Module (MulOpposite B.A) N.M := N.rmodule
    let _ : Module (MulOpposite B.A) (restrictScalars φ N).M := N.rmodule
    let _ : IsScalarTower R (MulOpposite B.A) (restrictScalars φ N).M := N.isScalarTower
    let x : N.M := f.val
    have hx : x ∈ N.grading n := by change x ∈ (restrictScalars φ N).grading n; exact f.property
    apply LinearMap.ext; intro b
    change (MulOpposite.op b) • (N.d x) =
      N.d ((MulOpposite.op b) • x) -
        DifferentialGraded.gradedSign R n •
          ((MulOpposite.op (B.d b)) • x)
    rw [N.leibniz_apply n x hx (b : B.A)]
    rw [← Int.cast_smul_eq_zsmul R (n.negOnePow)
      ((MulOpposite.op (B.d b)) • x)]
    rw [DifferentialGraded.intCast_negOnePow]
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  · intro N; exact Hom.id (restrictScalars φ N)
  · intro N n f
    let _ : Module (MulOpposite B.A) N.M := N.rmodule
    let x : N.M := f.val
    change x = MulOpposite.op (1 : B.A) • x
    simp
  · intro N
    change Function.Bijective (fun x : (restrictScalars φ N).M => x)
    exact Function.bijective_id
  · intro N N' g; ext x; rfl

end DifferentialGradedModule
