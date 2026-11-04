module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CochainEvaluationLocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingDoubleEvaluation

/-!
# Associativity of the currying bijection

Let `(C, O)` be a ringed site and let `A`, `B`, `C`, `D` be complexes of `O`-modules.  Write
`unc` for the currying bijection `(A ⟶ SheafHom(B, D)) ≃ (Tot(A ⊗_O B) ⟶ D)`
(`AlgebraicGeometry.RingedSite.curryHomEquiv`) and `cur` for the currying isomorphism
`SheafHom(B, SheafHom(C, D)) ≅ SheafHom(Tot(B ⊗_O C), D)`.  For a morphism of complexes
`g : A ⟶ SheafHom(B, SheafHom(C, D))`,

`unc (unc g) = α ≫ unc (g ≫ cur)`

as morphisms `Tot(Tot(A ⊗_O B) ⊗_O C) ⟶ D`, where `α` is any morphism reassociating the
iterated local pure tensors; the associator of the total tensor complex is one.

## Main results

* `AlgebraicGeometry.RingedSite.curryHomEquiv_curryHomEquiv_of_reassociate`:
  `unc (unc g) = α ≫ unc (g ≫ cur)` for every morphism `α` reassociating the iterated local pure
  tensors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The composite of two morphisms of sheaves of modules acts on sections by composition. -/
private lemma comp_val_app_apply_aux
    {P Q S : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : P ⟶ Q)
    (ψ : Q ⟶ S) (W : X.Cᵒᵖ) (x : P.val.obj W) :
    (φ ≫ ψ).val.app W x = ψ.val.app W (φ.val.app W x) := rfl

/-- For complexes `A`, `B`, `C`, `D` of `O`-modules, a morphism
`g : A ⟶ SheafHom(B, SheafHom(C, D))`, and a morphism
`e : Tot(Tot(A ⊗_O B) ⊗_O C) ⟶ Tot(A ⊗_O Tot(B ⊗_O C))` carrying every iterated homogeneous
local pure tensor `(x ⊗ y) ⊗ z` to `x ⊗ (y ⊗ z)`,

`unc (unc g) = e ≫ unc (g ≫ cur)`,

where `unc` is `AlgebraicGeometry.RingedSite.curryHomEquiv` and `cur` is
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`. -/
theorem curryHomEquiv_curryHomEquiv_of_reassociate
    (A B C D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (g : A ⟶ (sheafHomComplex X B (sheafHomComplex X C D).obj).obj)
    (e : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)).obj C ⟶
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B).obj C))
    (he : ∀ (W : X.C) (a b d j : ℤ) (h : a + b + d = j) (h' : a + (b + d) = j)
      (x : (A.X a).val.obj (op W)) (y : (B.X b).val.obj (op W)) (z : (C.X d).val.obj (op W)),
      (e.f j).val.app (op W)
          (tensorComplexSection X (a + b) d j h (tensorComplexSection X a b (a + b) rfl x y) z) =
        tensorComplexSection X a (b + d) j h' x (tensorComplexSection X b d (b + d) rfl y z)) :
    curryHomEquiv X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) C D
        (curryHomEquiv X A B (sheafHomComplex X C D).obj g) =
      e ≫ curryHomEquiv X A (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B).obj C) D
        (g ≫ (sheafHomTensorCurryIso X B C D).hom) := by
  set χ := (curryHomEquiv X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
    C D).symm (e ≫ curryHomEquiv X A (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B).obj
      C) D (g ≫ (sheafHomTensorCurryIso X B C D).hom)) with hχ
  have hχ' : curryHomEquiv X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
      C D χ = e ≫ curryHomEquiv X A
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B).obj C) D
        (g ≫ (sheafHomTensorCurryIso X B C D).hom) :=
    Equiv.apply_symm_apply _ _
  rw [← hχ']
  refine congrArg (curryHomEquiv X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
    C D) ?_
  refine tensorComplexSection_hom_ext X A B (sheafHomComplex X C D).obj
    fun c t r htr W a b ↦ ?_
  subst htr
  refine homSection_ext X (sheafHomComplex X C D) W (t + r) fun p q hpq V i x ↦ ?_
  have key : ∀ (a' : (A.X t).val.obj (op V)) (b' : (B.X r).val.obj (op V)),
      applyHomSection X (sheafHomComplex X C D) V (t + r) p q hpq
          ((((curryHomEquiv X A B (sheafHomComplex X C D).obj) g).f (t + r)).val.app (op V)
            (tensorComplexSection X t r (t + r) rfl a' b')) x =
        applyHomSection X (sheafHomComplex X C D) V (t + r) p q hpq
          ((χ.f (t + r)).val.app (op V) (tensorComplexSection X t r (t + r) rfl a' b')) x := by
    intro a' b'
    rw [curryHomEquiv_val_app_tensorComplexSection X A B (sheafHomComplex X C D).obj g
        (t + r) t r rfl (by omega) V a' b',
      ← curryHomEquiv_val_app_tensorComplexSection X
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) C D χ q (t + r) p
        (by omega) hpq V, hχ', HomologicalComplex.comp_f, comp_val_app_apply_aux,
      he V t r p q (by omega) (by omega),
      curryHomEquiv_val_app_tensorComplexSection X A
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B).obj C) D _ q t (r + p)
        (by omega) (by omega) V, HomologicalComplex.comp_f, comp_val_app_apply_aux,
      sheafHomTensorCurryIso_hom_f, curryHom_app]
    exact (applyHomSectionOver_curryFun_tensorComplexSection X V _ r p (r + p) q (t + r) rfl
      (by omega) (by omega) hpq _ x).symm
  rw [applyHomSectionOver_restrict X (sheafHomComplex X C D) W V i (t + r) p q hpq,
    applyHomSectionOver_restrict X (sheafHomComplex X C D) W V i (t + r) p q hpq,
    ← PresheafOfModules.naturality_apply
      (((curryHomEquiv X A B (sheafHomComplex X C D).obj) g).f (t + r)).val i.op,
    ← PresheafOfModules.naturality_apply (χ.f (t + r)).val i.op,
    ← tensorComplexSection_restrict]
  exact key _ _

end AlgebraicGeometry.RingedSite

end
