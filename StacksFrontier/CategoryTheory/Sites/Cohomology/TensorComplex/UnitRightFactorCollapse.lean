module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitLeftFactorCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor

/-!
# The total tensor complex with the structure sheaf as its *right* factor

Let `(C, O)` be a ringed site and let `A` be a cochain complex of `O`-modules. The collapse

`Tot(A ⊗_O O[0]) ≅ A`

of the total tensor complex against the structure sheaf placed in degree zero, **with the
structure sheaf as the right tensor factor**, is the right unitor `ρ_ A` of the monoidal
structure of Tag 0FNG on cochain complexes, read at the spelling
`Stacks.SheafOfModules.Tensor.tensorComplex` that the currying isomorphism of Tag 0A90 is stated
for. On local pure tensors it sends `a ⊗ k` to `k • a`; there is no Koszul sign.

## Main definitions

* `AlgebraicGeometry.RingedSite.structureSheafComplexTensorRightIso`: the collapse
  `Tot(A ⊗_O O[0]) ≅ A`, at the `tensorComplex` spelling.

## Main results

* `AlgebraicGeometry.RingedSite.structureSheafComplexTensorRightIso_eq`: it *is* `ρ_ A`.
* `AlgebraicGeometry.RingedSite.rightUnitor_inv_f` and
  `AlgebraicGeometry.RingedSite.rightUnitor_inv_f_val_app`: the inverse collapse sends a local
  section `a` of `A^t` to the local pure tensor `a ⊗ 1`.
* `AlgebraicGeometry.RingedSite.rightUnitor_hom_f_val_app_one` and
  `AlgebraicGeometry.RingedSite.rightUnitor_hom_f_val_app`: the collapse sends `a ⊗ 1` to `a`
  and `a ⊗ k` to `k • a`.

## Implementation notes

The proofs past the first step are in term mode: the summand inclusion of the monoidal product is
spelled `HomologicalComplex.ιTensorObj` with the unit complex written
`HomologicalComplex.tensorUnit`, while `Stacks.SheafOfModules.Tensor.tensorComplexSection` is
spelled with `HomologicalComplex.ιMapBifunctor` and
`AlgebraicGeometry.RingedSite.structureSheafComplex`. The two are equal by `rfl`, but a goal
mentioning both is not type-correct at `implicit` transparency, so a rewriting tactic can fail
silently on it.

## References

* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The total tensor complex collapses against the structure sheaf in its RIGHT factor:**
`Tot(A ⊗_O O[0]) ≅ A`, the right unitor `ρ_ A` of the monoidal structure of Tag 0FNG on cochain
complexes, read at the `Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the total tensor
complex. -/
def structureSheafComplexTensorRightIso
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj (structureSheafComplex X) ≅ A :=
  ρ_ A

/-- The collapse is the right unitor. -/
theorem structureSheafComplexTensorRightIso_eq
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    structureSheafComplexTensorRightIso X A = ρ_ A :=
  rfl

/-! ### The collapse on local sections -/

/-- The component of the inverse right unitor is the right unitor of the degree-`t` term followed
by the summand inclusion. -/
theorem rightUnitor_inv_f (t : ℤ) :
    (ρ_ A).inv.f t =
      (ρ_ (A.X t)).inv ≫
        HomologicalComplex.ιMapBifunctor A (structureSheafComplex X)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t 0 t (by simp) := by
  have h1 : (ρ_ A).inv.f t =
      (ρ_ (A.X t)).inv ≫
        ((A.X t) ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv) ≫
          HomologicalComplex.ιTensorObj A
            (HomologicalComplex.tensorUnit
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
            t 0 t (add_zero t) :=
    HomologicalComplex.rightUnitor'_inv A t
  have h2 : ((A.X t) ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv) ≫
          HomologicalComplex.ιTensorObj A
            (HomologicalComplex.tensorUnit
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
            t 0 t (add_zero t) =
      HomologicalComplex.ιMapBifunctor A (structureSheafComplex X)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t 0 t (by simp) :=
    (congrArg (fun w => w ≫ HomologicalComplex.ιTensorObj A
        (HomologicalComplex.tensorUnit
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
        t 0 t (add_zero t)) (whiskerLeft_id _ _)).trans (Category.id_comp _)
  exact h1.trans (congrArg (fun z => (ρ_ (A.X t)).inv ≫ z) h2)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The inverse right unitor of `Mod(O)` sends a local section `a` to the image of `a ⊗ 1` under
the sheafification unit. -/
theorem sheafRightUnitor_inv_val_app
    (P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (W : X.C)
    (a : P.val.obj (op W)) :
    (ρ_ P).inv.val.app (op W) a =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (P.val ⊗ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val)).app (op W)
          (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)]
            (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))) := by
  rw [show (ρ_ P).inv = (Stacks.SheafOfModules.tensorSheafUnitRightIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property P).inv from
    congrArg Iso.inv (SheafOfModules.rightUnitor_sheafTensor_eq_iso X.O P)]
  exact Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property P (op W) a

/-- The inverse right unitor of complexes sends a local section `a` of `A^t` to the local pure
tensor of `a` with the unit section. -/
theorem rightUnitor_inv_f_val_app (t : ℤ) (W : X.C) (a : (A.X t).val.obj (op W)) :
    ((ρ_ A).inv.f t).val.app (op W) a =
      tensorComplexSection X t 0 t (add_zero t) a
        (structureSheafOne X W) :=
  (congrArg (fun φ => φ.val.app (op W) a) (rightUnitor_inv_f X A t)).trans
    ((AlgebraicGeometry.RingedSite.val_app_comp_apply X (ρ_ (A.X t)).inv
        (HomologicalComplex.ιMapBifunctor A (structureSheafComplex X)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t 0 t (by simp))
        (op W) a).trans
      (congrArg ((HomologicalComplex.ιMapBifunctor A (structureSheafComplex X)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t 0 t
            (by simp)).val.app (op W))
        (sheafRightUnitor_inv_val_app X (A.X t) W a)))

/-- The right unitor of complexes sends the local pure tensor of `a` with the unit section back
to `a`. -/
theorem rightUnitor_hom_f_val_app_one (t : ℤ) (W : X.C) (a : (A.X t).val.obj (op W)) :
    ((ρ_ A).hom.f t).val.app (op W)
        (tensorComplexSection X t 0 t (add_zero t) a
          (structureSheafOne X W)) = a :=
  (congrArg (((ρ_ A).hom.f t).val.app (op W))
      (rightUnitor_inv_f_val_app X A t W a).symm).trans
    ((AlgebraicGeometry.RingedSite.val_app_comp_apply X ((ρ_ A).inv.f t) ((ρ_ A).hom.f t)
        (op W) a).symm.trans
      (congrArg (fun (φ : A ⟶ A) => (φ.f t).val.app (op W) a) (ρ_ A).inv_hom_id))

/-- The right unitor of complexes sends the local pure tensor of `a` with a local section `k` of
`O` to `k • a`. -/
theorem rightUnitor_hom_f_val_app (t : ℤ) (W : X.C)
    (a : (A.X t).val.obj (op W))
    (k : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) :
    ((ρ_ A).hom.f t).val.app (op W)
        (tensorComplexSection X t 0 t (add_zero t) a k) = k • a := by
  have hk : tensorComplexSection X
        (K := A) (L := structureSheafComplex X) t 0 t (add_zero t) a k =
      k • tensorComplexSection X
        (K := A) (L := structureSheafComplex X) t 0 t (add_zero t) a
          (structureSheafOne X W) :=
    (congrArg (fun z => tensorComplexSection X t 0 t (add_zero t) a z)
        (show k = k • structureSheafOne X W from (mul_one k).symm)).trans
      (tensorComplexSection_smul_right X t 0 t (add_zero t) k a
        (structureSheafOne X W))
  exact (congrArg (((ρ_ A).hom.f t).val.app (op W)) hk).trans ((map_smul _ k _).trans
    (congrArg (fun z => k • z) (rightUnitor_hom_f_val_app_one X A t W a)))

end AlgebraicGeometry.RingedSite

end
