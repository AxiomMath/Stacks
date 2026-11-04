module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexShift

/-!
# The shift comparison of the total tensor complex on local pure tensors

Let `X` be a ringed site and let `A`, `Z` be complexes of `O`-modules. The comparison

`Tot(A ⊗_O Z⟦k⟧) ≅ Tot(A ⊗_O Z)⟦k⟧`

of `AlgebraicGeometry.RingedSite.tensorTotalShiftIso₂` is built out of Mathlib's comparison for
the total complex of a bifunctor, and so is pinned on the *summand inclusions* of the underlying
bicomplex of presheaves. Everything in this development that consumes the total tensor complex
is instead pinned on the *local pure tensors* — `tensorTotalSection` and its reindexed form
`tensorTotalSectionAt`. This file computes the comparison in those terms:

`(t, r)`-pure tensor ↦ `(-1)^(t * k)` times the `(t, r + k)`-pure tensor,

which is the only form in which the comparison can be used against the interchange morphism or
the evaluation morphism.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalShiftIso₂_tensorTotalSection`: the computation above.
* `AlgebraicGeometry.RingedSite.tensorTotalSectionAt_eq_unit_ι`: the reindexed local pure tensor
  is the sheafification unit applied to a summand inclusion. Like
  `AlgebraicGeometry.RingedSite.tensorTotalSection_eq_unit_ι`, of which it is the general form,
  this holds by definition and is stated because it is the crossing between the layer in which
  the source is pinned and the layer in which the target is pinned.

## Implementation notes

The sign is Mathlib's, recorded at the presheaf level by
`AlgebraicGeometry.RingedSite.ι_underlyingTensorShiftIso₂_hom_f`; the work here is only to carry
that identity through the sheafification unit, which is possible in one step because the two
presheaf-level stages of the comparison were packaged together as
`AlgebraicGeometry.RingedSite.underlyingTensorShiftIso₂`. The remaining stage of
`tensorTotalShiftIso₂`, moving the shift out of the sheafification, has identity components and
so disappears definitionally.

The degrees are deliberately *not* matched up by an `eqToHom`: the target is read in the degree
`t + r + k` throughout, the source pure tensor being named by `tensorTotalSectionAt` with the
degree given explicitly. A statement phrased with `HomologicalComplex.XIsoOfEq` instead would
be equivalent, and useless, because every consumer would have to transport back.

## References

* [Stacks Project, Lemma 20.26.4 (Tag 06YS)](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  curriedTensorAdditive curriedTensorObjAdditive

variable (X : RingedSite.{u, u, u})

/-- The value on a local section of a morphism of presheaves of modules scaled by a unit of `ℤ`.
Only the sign `-1` is ever used, and only through `Int.negOnePow`, which is valued in `ℤˣ`. -/
private lemma units_smul_app_apply
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj} (u : ℤˣ)
    (φ : P ⟶ Q) (W : X.Cᵒᵖ) (x : P.obj W) :
    ((u • φ).app W) x = u • ((φ.app W) x) := by
  simp [Units.smul_def, PresheafOfModules.zsmul_app]

/-- **The reindexed local pure tensor is the sheafification unit applied to a summand
inclusion**, for any degree `c` with `t + r = c`. This is true by definition, and is the general
form of `AlgebraicGeometry.RingedSite.tensorTotalSection_eq_unit_ι`. -/
lemma tensorTotalSectionAt_eq_unit_ι
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) (t r c : ℤ)
    (h : t + r = c)
    (a : (A.X t).val.obj (op U)) (b : (B.X r).val.obj (op U)) :
    tensorTotalSectionAt X A B U t r c h a b =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((HomologicalComplex.mapBifunctor (underlyingPresheafComplex X A)
            (underlyingPresheafComplex X B)
            (MonoidalCategory.curriedTensor
              (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
            (ComplexShape.up ℤ)).X c)).app (op U)
        ((HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X A)
          (underlyingPresheafComplex X B)
          (MonoidalCategory.curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) t r c (by simpa using h)).app (op U)
            (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)) :=
  rfl

/-- **The shift comparison on a local pure tensor.** The comparison
`Tot(A ⊗_O Z⟦k⟧) ≅ Tot(A ⊗_O Z)⟦k⟧` sends the pure tensor of a degree-`t` section of `A` with a
degree-`r` section of `Z⟦k⟧` — that is, a degree-`r + k` section of `Z` — to `(-1)^(t * k)`
times the pure tensor of the same two sections read in the degree `t + r + k`. The sign is
Mathlib's; the content here is that nothing else happens, the sheafification and the passage to
underlying presheaves both commuting with the shift by identity maps. -/
lemma tensorTotalShiftIso₂_tensorTotalSection
    (A Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (k : ℤ) (U : X.C) (t r : ℤ)
    (a : (A.X t).val.obj (op U))
    (b : (((CategoryTheory.shiftFunctor
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) k).obj
        Z).X r).val.obj (op U)) :
    ((tensorTotalShiftIso₂ X A Z k).hom.f (t + r)).val.app (op U)
        (tensorTotalSection X A ((CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
          k).obj Z) U t r a b) =
      (t * k).negOnePow •
        tensorTotalSectionAt X A Z U t (r + k) (t + r + k) (by omega) a b := by
  have key : (((underlyingTensorShiftIso₂ X A Z k).hom.f (t + r)).app (op U))
      ((HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X A)
        (underlyingPresheafComplex X ((CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
          k).obj Z))
        (MonoidalCategory.curriedTensor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
        (ComplexShape.up ℤ) t r (t + r) rfl).app (op U)
          (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)) =
      (t * k).negOnePow •
        ((HomologicalComplex.ιMapBifunctor (underlyingPresheafComplex X A)
          (underlyingPresheafComplex X Z)
          (MonoidalCategory.curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (ComplexShape.up ℤ) t (r + k) (t + r + k) (by dsimp; omega)).app (op U)
            (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b)) := by
    refine Eq.trans
      (congrArg
        (fun z ↦ z.app (op U) (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b))
      (ι_underlyingTensorShiftIso₂_hom_f X A Z k t r)) ?_
    exact units_smul_app_apply X _ _ (op U) _
  rw [tensorTotalSection_eq_unit_ι, tensorTotalSectionAt_eq_unit_ι]
  refine Eq.trans (sheafification_map_unit_apply X
    ((underlyingTensorShiftIso₂ X A Z k).hom.f (t + r)) (op U) _) ?_
  rw [key, Units.smul_def, map_zsmul]
  rfl

end AlgebraicGeometry.RingedSite

end
