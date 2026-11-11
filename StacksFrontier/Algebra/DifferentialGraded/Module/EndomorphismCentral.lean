module

public import StacksFrontier.Algebra.DGA.CentralAction
public import StacksFrontier.Algebra.DifferentialGraded.NonpositiveTruncation
public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismBimodule

/-!
# Central closed endomorphisms give central cocycles of the endomorphism algebra

Let `C` be a differential graded category over a commutative ring `R` and let `x` be an object
of `C`. A closed degree-zero endomorphism `f` of `x` which commutes, under composition, with every
homogeneous endomorphism of `x` is a central cocycle of degree zero of the endomorphism
differential graded algebra `End(x)` of [Stacks, Tag 09LE].

The case of interest is that of a right differential graded module `Q` over an algebra `B` and a
central element `w` of `B` of degree zero with `d w = 0`: right multiplication by `w` is right
`B`-linear and commutes with every homogeneous right `B`-linear endomorphism of `Q`, so it is a
central cocycle of `End(Q)`, and also of the endomorphism algebra of `Q` in the degree-`≤ 0`
truncation of the differential graded category of right differential graded `B`-modules.

## Main definitions

* `DifferentialGradedModule.centralSMulHomogeneous`: right multiplication by `w`, as a
  homogeneous map of degree zero.

## Main results

* `DGCategory.HomRepresentation.isCentralCocycle_algebraHom_symm`: a closed central degree-zero
  endomorphism of `x` is a central cocycle of `End(x)`.
* `DGCategory.HomRepresentation.algebraHom_symm_comp` and
  `DGCategory.HomRepresentation.algebraHom_symm_id`: the passage from degree-zero endomorphisms to
  elements of `End(x)` is multiplicative and unital.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DGCategory

universe w v u

variable {R : Type u} [CommRing R] {C : DGCategory.{w, v, u} R} {x : C.Obj}
  (H : HomRepresentation C x)

/-- **A closed central degree-zero endomorphism is a central cocycle of `End(x)`.** If `f` is a
degree-zero endomorphism of `x` with `d f = 0` which commutes with every homogeneous endomorphism
of `x`, then the corresponding element of the endomorphism algebra is central, of degree zero and
closed. -/
theorem HomRepresentation.isCentralCocycle_algebraHom_symm (f : C.Hom x x 0) (hf : C.d f = 0)
    (hcomm : ∀ (n : ℤ) (g : C.Hom x x n), C.comp (zero_add n) f g = C.comp (add_zero n) g f) :
    DifferentialGradedModule.IsCentralCocycle
      (((H.algebraHom 0).symm f : H.algebra.grading 0) : H.algebra.A) where
  comm b := by
    induction b using DirectSum.Decomposition.inductionOn H.algebra.grading with
    | zero => rw [mul_zero, zero_mul]
    | add b b' hb hb' => rw [mul_add, add_mul, hb, hb']
    | @homogeneous n b =>
      obtain ⟨c, hc, hcf⟩ := H.algebra_mul 0 n n (zero_add n) ((H.algebraHom 0).symm f) b
      obtain ⟨c', hc', hcf'⟩ := H.algebra_mul n 0 n (add_zero n) b ((H.algebraHom 0).symm f)
      rw [LinearEquiv.apply_symm_apply] at hcf hcf'
      have hcc : c = c' := (H.algebraHom n).injective (by rw [hcf, hcf', hcomm])
      rw [← hc, ← hc', hcc]
  mem := ((H.algebraHom 0).symm f).property
  d_eq := by
    have h := H.algebra_d 0 ((H.algebraHom 0).symm f)
    rw [LinearEquiv.apply_symm_apply, hf, ← map_zero (H.algebraHom (0 + 1))] at h
    exact congrArg Subtype.val ((H.algebraHom (0 + 1)).injective h)

/-- The passage from degree-zero endomorphisms of `x` to elements of `End(x)` is
multiplicative. -/
theorem HomRepresentation.algebraHom_symm_comp (f g : C.Hom x x 0) :
    (((H.algebraHom 0).symm (C.comp (add_zero 0) f g) : H.algebra.grading 0) : H.algebra.A) =
      ((H.algebraHom 0).symm f : H.algebra.A) * ((H.algebraHom 0).symm g : H.algebra.A) := by
  obtain ⟨c, hc, hcf⟩ := H.algebra_mul 0 0 0 (add_zero 0) ((H.algebraHom 0).symm f)
    ((H.algebraHom 0).symm g)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hcf
  rw [← hc, ← hcf, LinearEquiv.symm_apply_apply]

/-- The passage from degree-zero endomorphisms of `x` to elements of `End(x)` is unital. -/
theorem HomRepresentation.algebraHom_symm_id :
    (((H.algebraHom 0).symm (C.id x) : H.algebra.grading 0) : H.algebra.A) = 1 := by
  rw [← H.algebraHom_one, LinearEquiv.symm_apply_apply]

end DGCategory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {B : DifferentialGradedAlgebra.{u, u} R}

/-- Right multiplication by a central closed element of degree zero, as a homogeneous right
`B`-linear map of degree zero. -/
def centralSMulHomogeneous {w : B.A} (hw : IsCentralCocycle w)
    (Q : DifferentialGradedModule.{u, u, u} B) : HomogeneousMap B Q Q 0 :=
  ⟨(centralSMul hw Q).toFun, fun i y hy => by
      simpa only [add_zero] using (centralSMul hw Q).map_grading i y hy,
    fun a y => (centralSMul hw Q).map_smul y a⟩

/-- The homogeneous map `centralSMulHomogeneous hw Q` sends `y` to `y w`. -/
@[simp]
theorem centralSMulHomogeneous_apply {w : B.A} (hw : IsCentralCocycle w)
    (Q : DifferentialGradedModule.{u, u, u} B) (y : Q.M) :
    (centralSMulHomogeneous hw Q).1 y = MulOpposite.op w • y :=
  rfl

/-- Right multiplication by `w` is closed for the Hom differential. -/
theorem homogeneousMapDifferential_centralSMulHomogeneous {w : B.A} (hw : IsCentralCocycle w)
    (Q : DifferentialGradedModule.{u, u, u} B) :
    homogeneousMapDifferential B (centralSMulHomogeneous hw Q) = 0 := by
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  have h := LinearMap.congr_fun (centralSMul hw Q).map_d y
  simp only [LinearMap.comp_apply] at h
  rw [homogeneousMapDifferential_val, DifferentialGraded.gradedSign_zero, one_smul,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change Q.d ((centralSMul hw Q).toFun y) - (centralSMul hw Q).toFun (Q.d y) = 0
  rw [h, sub_self]

/-- Right multiplication by `w` commutes with every homogeneous right `B`-linear endomorphism. -/
theorem homogeneousMapComp_centralSMulHomogeneous {w : B.A} (hw : IsCentralCocycle w)
    (Q : DifferentialGradedModule.{u, u, u} B) (n : ℤ) (g : HomogeneousMap B Q Q n) :
    homogeneousMapComp B (zero_add n) (centralSMulHomogeneous hw Q) g =
      homogeneousMapComp B (add_zero n) g (centralSMulHomogeneous hw Q) :=
  Subtype.ext (LinearMap.ext fun y => (g.2.2 w y).symm)

/-- Right multiplication by `1` is the identity. -/
theorem centralSMulHomogeneous_one (h : IsCentralCocycle (1 : B.A))
    (Q : DifferentialGradedModule.{u, u, u} B) :
    centralSMulHomogeneous h Q = homogeneousMapId B Q :=
  Subtype.ext (LinearMap.ext fun y => by
    rw [centralSMulHomogeneous_apply, MulOpposite.op_one, one_smul]
    rfl)

/-- Right multiplication by a product of central elements is the composite. -/
theorem centralSMulHomogeneous_mul {w w' : B.A} (hw : IsCentralCocycle w)
    (hw' : IsCentralCocycle w') (h : IsCentralCocycle (w * w'))
    (Q : DifferentialGradedModule.{u, u, u} B) :
    centralSMulHomogeneous h Q = homogeneousMapComp B (add_zero 0)
      (centralSMulHomogeneous hw Q) (centralSMulHomogeneous hw' Q) :=
  Subtype.ext (LinearMap.ext fun y => by
    rw [homogeneousMapComp_val, LinearMap.comp_apply, centralSMulHomogeneous_apply,
      centralSMulHomogeneous_apply, centralSMulHomogeneous_apply, smul_smul,
      ← MulOpposite.op_mul, hw.comm w'])

/-- Right multiplication by zero is zero. -/
theorem centralSMulHomogeneous_zero (h : IsCentralCocycle (0 : B.A))
    (Q : DifferentialGradedModule.{u, u, u} B) : centralSMulHomogeneous h Q = 0 :=
  Subtype.ext (LinearMap.ext fun y => by
    rw [centralSMulHomogeneous_apply, MulOpposite.op_zero, zero_smul]
    rfl)

/-- Right multiplication by a sum is the sum. -/
theorem centralSMulHomogeneous_add {w w' : B.A} (hw : IsCentralCocycle w)
    (hw' : IsCentralCocycle w') (h : IsCentralCocycle (w + w'))
    (Q : DifferentialGradedModule.{u, u, u} B) :
    centralSMulHomogeneous h Q = centralSMulHomogeneous hw Q + centralSMulHomogeneous hw' Q :=
  Subtype.ext (LinearMap.ext fun y => by
    rw [centralSMulHomogeneous_apply, MulOpposite.op_add, add_smul]
    rfl)

/-- Right multiplication by the image of a scalar is multiplication by the scalar. -/
theorem centralSMulHomogeneous_algebraMap (r : R) (h : IsCentralCocycle (algebraMap R B.A r))
    (Q : DifferentialGradedModule.{u, u, u} B) :
    centralSMulHomogeneous h Q = r • homogeneousMapId B Q :=
  Subtype.ext (LinearMap.ext fun y => by
    rw [centralSMulHomogeneous_apply, ← MulOpposite.algebraMap_apply, algebraMap_smul]
    rfl)

end DifferentialGradedModule

end
