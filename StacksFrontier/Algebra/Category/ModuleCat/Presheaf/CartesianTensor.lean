module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Tensor

/-!
# The objectwise tensor product of two cartesian presheaves of modules is cartesian

Let `R` be a presheaf of commutative rings on a category `C` and let `F`, `G` be presheaves of
`R`-modules. If the restriction maps of `F` and of `G` along an arrow `f : X ⟶ Y` of `Cᵒᵖ` are
base changes, i.e. the comparisons `R Y ⊗_{R X} F X ⟶ F Y` and `R Y ⊗_{R X} G X ⟶ G Y`
(`Stacks.PresheafOfModules.restrictionBaseChange`) are isomorphisms, then so is the comparison
for the objectwise tensor product `F ⊗_R G` (`PresheafOfModules.tensorObj`).

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_tensorObj`: the objectwise tensor
  product of two presheaves of modules cartesian along `f` is cartesian along `f`.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- Two additive maps out of a tensor product that agree on pure tensors agree everywhere. -/
private theorem addMonoidHom_apply_eq_of_tmul_eq {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N]
    (f g : M ⊗[R] N →+ P) (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) (t : M ⊗[R] N) : f t = g t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul m n => exact h m n

/-- If the comparisons `R Y ⊗_{R X} F X ⟶ F Y` and `R Y ⊗_{R X} G X ⟶ G Y` along `f` are
isomorphisms, then so is the comparison `R Y ⊗_{R X} (F X ⊗_{R X} G X) ⟶ F Y ⊗_{R Y} G Y` of
the objectwise tensor product. -/
theorem isIso_restrictionBaseChange_tensorObj
    (F G : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange F f)]
    [IsIso (restrictionBaseChange G f)] :
    IsIso (restrictionBaseChange (_root_.PresheafOfModules.tensorObj F G) f) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let eF : TensorProduct (R.obj X) (R.obj Y) (F.obj X) ≃ₗ[R.obj Y] F.obj Y :=
    (asIso (restrictionBaseChange F f)).toLinearEquiv
  let eG : TensorProduct (R.obj X) (R.obj Y) (G.obj X) ≃ₗ[R.obj Y] G.obj Y :=
    (asIso (restrictionBaseChange G f)).toLinearEquiv
  let E : TensorProduct (R.obj X) (R.obj Y)
      (TensorProduct (R.obj X) (F.obj X) (G.obj X)) ≃ₗ[R.obj Y]
      TensorProduct (R.obj Y) (F.obj Y) (G.obj Y) :=
    (AlgebraTensorModule.distribBaseChange (R.obj X) (R.obj Y) (F.obj X) (G.obj X)).trans
      (TensorProduct.congr eF eG)
  have hF : ∀ (c : R.obj Y) (x : F.obj X), eF (c ⊗ₜ x) = c • F.map f x :=
    restrictionBaseChange_tmul F f
  have hG : ∀ (c : R.obj Y) (y : G.obj X), eG (c ⊗ₜ y) = c • G.map f y :=
    restrictionBaseChange_tmul G f
  let φ : R.obj Y ⊗[R.obj X] (F.obj X ⊗[R.obj X] G.obj X) →+ F.obj Y ⊗[R.obj Y] G.obj Y :=
    (restrictionBaseChange (_root_.PresheafOfModules.tensorObj F G) f).hom.toAddMonoidHom
  have hT : ∀ (c : R.obj Y) (w : TensorProduct (R.obj X) (F.obj X) (G.obj X)),
      φ (c ⊗ₜ w) = E (c ⊗ₜ w) := by
    intro c w
    refine addMonoidHom_apply_eq_of_tmul_eq (φ.comp (AddMonoidHom.mk' (c ⊗ₜ ·) (tmul_add c)))
      (E.toAddMonoidHom.comp (AddMonoidHom.mk' (c ⊗ₜ ·) (tmul_add c))) (fun x y => ?_) w
    change restrictionBaseChange (_root_.PresheafOfModules.tensorObj F G) f (c ⊗ₜ (x ⊗ₜ y)) =
      E (c ⊗ₜ (x ⊗ₜ y))
    let c'' : (R ⋙ forget₂ CommRingCat RingCat).obj Y := c
    have h0 := restrictionBaseChange_tmul (_root_.PresheafOfModules.tensorObj F G) f c
      (x ⊗ₜ y)
    have h2 : (_root_.PresheafOfModules.tensorObj F G).map f (x ⊗ₜ y) =
        F.map f x ⊗ₜ G.map f y :=
      _root_.PresheafOfModules.tensorObj_restrictₛₗ_tmul f x y
    have h4 : c'' • (F.map f x ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj Y] G.map f y) =
        (c'' • F.map f x) ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj Y] G.map f y :=
      TensorProduct.smul_tmul' c'' _ _
    have h1 : E (c ⊗ₜ (x ⊗ₜ y)) = eF (c ⊗ₜ x) ⊗ₜ eG ((1 : R.obj Y) ⊗ₜ y) := rfl
    have h3 : eF (c ⊗ₜ x) ⊗ₜ[R.obj Y] eG ((1 : R.obj Y) ⊗ₜ y) =
        (c • F.map f x) ⊗ₜ[R.obj Y] G.map f y := by
      rw [hF, hG, one_smul]
      rfl
    exact h0.trans ((congrArg (c'' • ·) h2).trans (h4.trans (h3.symm.trans h1.symm)))
  have key := addMonoidHom_apply_eq_of_tmul_eq φ E.toAddMonoidHom hT
  rw [show ⇑(restrictionBaseChange (_root_.PresheafOfModules.tensorObj F G) f) = ⇑E from
    funext key]
  exact E.bijective

end Stacks.PresheafOfModules
