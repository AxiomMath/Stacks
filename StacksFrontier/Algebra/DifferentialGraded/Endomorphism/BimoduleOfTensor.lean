module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorInclusion
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.LeftModule

/-!
# A module over the graded tensor product is a differential graded bimodule

Let `A` and `B` be differential graded algebras over a commutative ring `R` and write
`C = Aᵒᵖ` for the graded opposite of `A`. A right differential graded module `N` over the graded
tensor product `C ⊗ B` restricts to a right `B`-module along the right inclusion, and to a right
`C`-module along the left inclusion; the latter is the same as a left `A`-module by graded
opposition, so it gives a left differential graded `A`-action on the complex underlying `N`. Those
two actions commute up to the Koszul sign, so `N` becomes a differential graded `(A, B)`-bimodule.

## Main definitions

* `DifferentialGradedModule.isoToCochainComplexIso`: an isomorphism of differential graded modules
  as an isomorphism of the underlying complexes.
* `DifferentialGradedModule.isoToLinearEquiv`: an isomorphism of differential graded modules as a
  linear equivalence of the underlying modules.
* `DifferentialGraded.Bimodule.oppAlgebra`: the graded opposite `C = Aᵒᵖ`.
* `DifferentialGraded.Bimodule.tensorAlgebra`: the graded tensor product `C ⊗ B`.
* `DifferentialGraded.Bimodule.ofTensorRightModule`: the underlying right `B`-module of `N`.
* `DifferentialGraded.Bimodule.ofTensorOppModule`: the underlying right `C`-module of `N`.
* `DifferentialGraded.Bimodule.ofTensorLeftModule`: the underlying left `A`-module of `N`.
* `DifferentialGraded.Bimodule.ofTensorCounitIso`: the identification of the right `C`-module
  attached to that left `A`-module with the underlying right `C`-module of `N`.
* `DifferentialGraded.Bimodule.ofTensorCochainIso`: the identification of its underlying complex
  with the complex underlying `N`.
* `DifferentialGraded.Bimodule.ofTensorAction`: the resulting left differential graded `A`-action.
* `DifferentialGraded.Bimodule.ofTensorModule`: the differential graded bimodule.

## Main results

* `DifferentialGraded.Bimodule.ofTensorModule_leftAction_apply`: on a homogeneous element, the
  left action is the action of `a ⊗ 1`, up to the Koszul sign.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
-/

@[expose] public section

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

namespace DifferentialGradedModule

/-- An isomorphism of differential graded modules induces an isomorphism of the underlying
complexes. -/
noncomputable def isoToCochainComplexIso {C : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule C} (e : M ≅ N) : M.toCochainComplex ≅ N.toCochainComplex := by
  let f (n : ℤ) : M.grading n ≃ₗ[R] N.grading n := {
    toFun := e.hom.gradedMap n
    invFun := e.inv.gradedMap n
    left_inv := fun x => Subtype.ext <|
      congrArg (fun g : DifferentialGradedModule.Hom M M => g.toFun x) e.hom_inv_id
    right_inv := fun x => Subtype.ext <|
      congrArg (fun g : DifferentialGradedModule.Hom N N => g.toFun x) e.inv_hom_id
    map_add' := fun x y => Subtype.ext <| e.hom.toFun.map_add (x : M.M) (y : M.M)
    map_smul' := fun r x => Subtype.ext <| e.hom.toFun.map_smul r (x : M.M) }
  refine HomologicalComplex.Hom.isoOfComponents (fun n => (f n).toModuleIso) ?_
  rintro n _ rfl
  simp only [DifferentialGradedModule.toCochainComplex_X,
    DifferentialGradedModule.toCochainComplex_d]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
  change N.d (e.hom.toFun (x : M.M)) = e.hom.toFun (M.d (x : M.M))
  simpa only [LinearMap.comp_apply] using
    (congrArg (fun g : M.M →ₗ[R] N.M => g (x : M.M)) e.hom.map_d).symm

/-- An isomorphism of differential graded modules induces a linear equivalence of the underlying
modules. -/
noncomputable def isoToLinearEquiv {C : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule C} (e : M ≅ N) : M.M ≃ₗ[R] N.M where
  toFun := e.hom.toFun
  invFun := e.inv.toFun
  left_inv x := congrArg (fun f : DifferentialGradedModule.Hom M M => f.toFun x) e.hom_inv_id
  right_inv x := congrArg (fun f : DifferentialGradedModule.Hom N N => f.toFun x) e.inv_hom_id
  map_add' := e.hom.toFun.map_add
  map_smul' := e.hom.toFun.map_smul

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

variable (A : DifferentialGradedAlgebra R) (B : DifferentialGradedAlgebra R)

/-- The graded opposite of `A`, as a differential graded algebra. -/
noncomputable abbrev oppAlgebra : DifferentialGradedAlgebra R :=
  (DifferentialGradedAlgebra.opposite R A).toDifferentialGradedAlgebra

/-- The graded tensor product of the graded opposite of `A` with `B`. -/
noncomputable abbrev tensorAlgebra : DifferentialGradedAlgebra R :=
  DifferentialGradedAlgebra.tensorProduct (oppAlgebra A) B

/-- The right differential graded `B`-module underlying a right module over
`tensorAlgebra A B`. -/
noncomputable abbrev ofTensorRightModule (N : DifferentialGradedModule (tensorAlgebra A B)) :
    DifferentialGradedModule B :=
  DifferentialGradedModule.tensorRestrictRight (oppAlgebra A) B N

/-- The right differential graded module over the graded opposite of `A` underlying a right module
over `tensorAlgebra A B`. -/
noncomputable abbrev ofTensorOppModule (N : DifferentialGradedModule (tensorAlgebra A B)) :
    DifferentialGradedModule (oppAlgebra A) :=
  DifferentialGradedModule.tensorRestrictLeft (oppAlgebra A) B N

/-- The left differential graded `A`-module underlying a right module over
`tensorAlgebra A B`. -/
noncomputable abbrev ofTensorLeftModule (N : DifferentialGradedModule (tensorAlgebra A B)) :
    LeftModule A :=
  (leftRightEquivalence R A).equivalence.inverse.obj (ofTensorOppModule A B N)

/-- The counit isomorphism identifying the right module over the graded opposite attached to
`ofTensorLeftModule` with `ofTensorOppModule`. -/
noncomputable abbrev ofTensorCounitIso (N : DifferentialGradedModule (tensorAlgebra A B)) :
    (leftRightEquivalence R A).equivalence.functor.obj (ofTensorLeftModule A B N) ≅
      ofTensorOppModule A B N :=
  (leftRightEquivalence R A).equivalence.counitIso.app (ofTensorOppModule A B N)

/-- The identification of the complex underlying `ofTensorLeftModule` with the complex underlying
`ofTensorRightModule`. -/
noncomputable abbrev ofTensorCochainIso (N : DifferentialGradedModule (tensorAlgebra A B)) :
    LeftModule.toCochainComplex A (ofTensorLeftModule A B N) ≅
      (ofTensorRightModule A B N).toCochainComplex :=
  (LeftModule.oppositeCochainIso A (ofTensorLeftModule A B N) ≪≫
    DifferentialGradedModule.isoToCochainComplexIso (ofTensorCounitIso A B N)) ≪≫
      eqToIso (by rfl)

/-- The left differential graded `A`-action on the complex underlying a right module over the
graded tensor product. -/
noncomputable abbrev ofTensorAction (N : DifferentialGradedModule (tensorAlgebra A B)) :
    A.LeftAction (ofTensorRightModule A B N).toCochainComplex :=
  LeftModule.leftAction A (ofTensorLeftModule A B N) _ (ofTensorCochainIso A B N)

/-- On a homogeneous element, the left `A`-action attached to a right module over the graded tensor
product is the action of `a ⊗ 1`, up to the Koszul sign. -/
theorem ofTensorModule_leftAction_apply (N : DifferentialGradedModule (tensorAlgebra A B))
    {m p : ℤ} (a : A.grading m) (x : (ofTensorRightModule A B N).grading p) :
    letI : Module (MulOpposite (tensorAlgebra A B).A) (ofTensorRightModule A B N).M := N.rmodule
    leftActionTotal A B (ofTensorRightModule A B N) (ofTensorAction A B N) (a : A.A) x.val =
      (m * p).negOnePow •
        ((MulOpposite.op (GradedTensorProduct.includeLeft (oppAlgebra A).grading B.grading
            ((DifferentialGradedAlgebra.opposite R A).equiv.symm (a : A.A))) :
              MulOpposite (tensorAlgebra A B).A) • x.val) := by
  let _ : Module (MulOpposite (tensorAlgebra A B).A) (ofTensorRightModule A B N).M := N.rmodule
  let M := ofTensorRightModule A B N
  let L := ofTensorLeftModule A B N
  let E := leftRightEquivalence R A
  let i := ofTensorCochainIso A B N
  let K := ofTensorAction A B N
  let c : (oppAlgebra A).grading m :=
    ⟨(DifferentialGradedAlgebra.opposite R A).equiv.symm (a : A.A), by
      rw [DifferentialGradedAlgebra.Opposite.mem_grading_iff]
      simp⟩
  let h := ofTensorCounitIso A B N
  let Q := E.equivalence.functor.obj L
  let xQ : Q.grading p := h.inv.gradedMap p x
  let xL : L.grading p := ⟨E.underlying L (xQ : Q.M), (E.grading L p (xQ : Q.M)).mp xQ.property⟩
  have hi' (q : ℤ) (y : L.grading q) :
      (i.hom.f q y).val = h.hom.toFun ((E.underlying L).symm y) := rfl
  have hh : h.hom.toFun (xQ : Q.M) = x.val :=
    LinearMap.congr_fun (congrArg DifferentialGradedModule.Hom.toFun h.inv_hom_id) x.val
  have hx : i.hom.f p xL = x :=
    Subtype.ext <| (congrArg h.hom.toFun ((E.underlying L).symm_apply_apply _)).trans hh
  have hEa := E.action L m p (c : (oppAlgebra A).A) xQ c.property xQ.property
  have hinv : (E.underlying L).symm ((a : A.A) • (xL : L.M)) =
      (m * p).negOnePow • (MulOpposite.op (c : (oppAlgebra A).A) • (xQ : Q.M)) := by
    apply (E.underlying L).injective
    rw [LinearEquiv.apply_symm_apply]
    rw [map_zsmul_unit, hEa, smul_smul, ← Int.negOnePow_add, Int.negOnePow_even _ (Even.add_self _),
      one_smul]
    simp only [c, LinearEquiv.apply_symm_apply, xL]
  rw [leftActionTotal_apply A B M K m a,
    DifferentialGradedModule.totalizeCochain_apply B M m p (K.action m a) x]
  have hv := LeftModule.leftAction_apply A L M.toCochainComplex i m p a xL
  rw [hx] at hv
  change ((K.action m a).v p (p + m) rfl x).val = _
  rw [hv, hi', hinv]
  rw [map_zsmul_unit, h.hom.map_smul, hh]
  rfl

/-- A right differential graded module over the graded tensor product of the graded opposite of `A`
with `B` is a differential graded `(A, B)`-bimodule. -/
noncomputable abbrev ofTensorModule (N : DifferentialGradedModule (tensorAlgebra A B)) :
    Bimodule A B := by
  classical
  refine ⟨ofTensorRightModule A B N, ⟨ofTensorAction A B N, ?_⟩⟩
  let _ : Module (MulOpposite ((oppAlgebra A).grading ᵍ⊗[R] B.grading))
      (ofTensorRightModule A B N).M := N.rmodule
  let _ : IsScalarTower R (MulOpposite ((oppAlgebra A).grading ᵍ⊗[R] B.grading))
      (ofTensorRightModule A B N).M := N.isScalarTower
  intro n a
  let M := ofTensorRightModule A B N
  let K := ofTensorAction A B N
  refine ⟨⟨leftActionTotal A B M K a, ?_, ?_⟩, ?_⟩
  · exact fun p x hx => leftActionTotal_apply_mem A B M K a ⟨x, hx⟩
  · intro b x
    induction b using DirectSum.Decomposition.inductionOn B.grading with
    | zero => simp
    | add b c hb hc => simp [add_smul, hb, hc]
    | @homogeneous q b =>
      induction x using DirectSum.Decomposition.inductionOn M.grading with
      | zero => simp
      | add x y hx hy => simp [smul_add, hx, hy]
      | @homogeneous p x =>
        let c : (oppAlgebra A).grading n :=
          ⟨(DifferentialGradedAlgebra.opposite R A).equiv.symm a, by
            rw [DifferentialGradedAlgebra.Opposite.mem_grading_iff]
            simp⟩
        let xb : M.grading (p + q) := ⟨MulOpposite.op (b : B.A) • (x : M.M),
          M.smul_mem p q x b x.property b.property⟩
        have h₁ := ofTensorModule_leftAction_apply A B N a xb
        have h₂ := ofTensorModule_leftAction_apply A B N a x
        change leftActionTotal A B M K a (xb : M.M) = _
        rw [h₁, h₂]
        change (n * (p + q)).negOnePow •
            (MulOpposite.op
                (GradedTensorProduct.includeLeft (oppAlgebra A).grading B.grading
                  (c : (oppAlgebra A).A)) •
              (MulOpposite.op
                  (GradedTensorProduct.includeRight (oppAlgebra A).grading B.grading (b : B.A)) •
                (x : M.M))) =
          MulOpposite.op
              (GradedTensorProduct.includeRight (oppAlgebra A).grading B.grading (b : B.A)) •
            ((n * p).negOnePow •
              (MulOpposite.op
                  (GradedTensorProduct.includeLeft (oppAlgebra A).grading B.grading
                    (c : (oppAlgebra A).A)) •
                (x : M.M)))
        rw [DifferentialGradedAlgebra.op_includeLeft_smul_op_includeRight_smul
          (oppAlgebra A) B c b]
        simp only [smul_smul, ← Int.negOnePow_add]
        have hs : n * (p + q) + n * q = n * p + (n * q + n * q) := by ring
        rw [hs, Int.negOnePow_add, Int.negOnePow_even _ (Even.add_self _), mul_one]
        simpa only [mul_smul] using smul_comm (n * p).negOnePow
          (MulOpposite.op
            (GradedTensorProduct.includeRight (oppAlgebra A).grading B.grading (b : B.A)))
          (MulOpposite.op
              (GradedTensorProduct.includeLeft (oppAlgebra A).grading B.grading
                (c : (oppAlgebra A).A)) •
            (x : M.M))
  · exact fun p x =>
      (DifferentialGradedModule.totalizeCochain_apply B M n p (K.action n a) x).symm.trans
        (congrArg (fun f : M.M →ₗ[R] M.M => f x) (leftActionTotal_apply A B M K n a).symm)

end DifferentialGraded.Bimodule
