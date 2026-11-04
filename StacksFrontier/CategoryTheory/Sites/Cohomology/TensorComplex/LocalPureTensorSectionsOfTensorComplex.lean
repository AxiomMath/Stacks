module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalPureTensorSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections
import StacksCore.Tactic.StacksAttribute

/-!
# A section of the tensor complex is locally a finite sum of pure tensors

`AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection` says this for
`AlgebraicGeometry.RingedSite.tensorTotal`, the total complex of the presheaf-level bicomplex.
The consumers of the statement — the direct-summand step of Stacks 0FPV, and
`AlgebraicGeometry.RingedSite.tensorComplexMap_sum_tensorComplexSection_lift` which lifts such a
sum through a subcomplex — work with `Stacks.SheafOfModules.Tensor.tensorComplex`, the monoidal
tensor product of complexes of sheaves of modules.

This file crosses between the two spellings. The two complexes are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, and that identification matches the
pure tensors on the nose: `tensorTotalIsoTensorComplex_inv_tensorComplexSection`. So the sieve
statement transports, and the transport is exactly a conjugation by the comparison together with
`PresheafOfModules.naturality_apply` to move the restriction past it.

No reducibility bridge is involved: both sides are named complexes and the comparison between
them is an isomorphism proved elsewhere, used here as given.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive] [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (n : ℤ)

/-- **A section of the tensor complex is, on a covering sieve, a finite sum of pure tensors.**
The `AlgebraicGeometry.RingedSite.tensorTotal` form of this is
`AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection`; this is the same statement for
`Stacks.SheafOfModules.Tensor.tensorComplex`, which is the spelling its consumers use — in
particular `AlgebraicGeometry.RingedSite.tensorComplexMap_sum_tensorComplexSection_lift`, whose
index shape this matches. -/
public theorem exists_sieve_sum_tensorComplexSection (U : X.C)
    (s : ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B).X n).val.obj (op U)) :
    ∃ T : Sieve U, T ∈ X.J U ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ U), T.arrows g →
      ∃ (κ : Type) (_ : Fintype κ) (t r : κ → ℤ) (h : ∀ j, t j + r j = n)
        (a : ∀ j, (A.X (t j)).val.obj (op W)) (b : ∀ j, (B.X (r j)).val.obj (op W)),
        ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B).X n).val.map g.op s =
          ∑ j, tensorComplexSection X (t j) (r j) n (h j) (a j) (b j) := by
  obtain ⟨T, hT, hspec⟩ := exists_sieve_sum_tensorTotalSection X A B n U
    (((tensorTotalIsoTensorComplex X A B).inv.f n).val.app (op U) s)
  refine ⟨T, hT, ?_⟩
  intro W g hg
  obtain ⟨κ, hκ, t, r, h, a, b, hsum⟩ := hspec g hg
  refine ⟨κ, hκ, t, r, h, a, b, ?_⟩
  have hnat := PresheafOfModules.naturality_apply
    ((tensorTotalIsoTensorComplex X A B).inv.f n).val g.op s
  rw [← hnat] at hsum
  have hterms : ∀ j : κ, tensorTotalSectionAt X A B W (t j) (r j) n (h j) (a j) (b j) =
      ((tensorTotalIsoTensorComplex X A B).inv.f n).val.app (op W)
        (tensorComplexSection X (t j) (r j) n (h j) (a j) (b j)) := fun j =>
    (tensorTotalIsoTensorComplex_inv_tensorComplexSection X A B W (t j) (r j) n (h j)
      (a j) (b j)).symm
  rw [Finset.sum_congr rfl fun j _ => hterms j, ← map_sum] at hsum
  have hcomp : ((tensorTotalIsoTensorComplex X A B).inv.f n ≫
      (tensorTotalIsoTensorComplex X A B).hom.f n) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  have hid : ∀ z : ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B).X n).val.obj
        (op W),
      ((tensorTotalIsoTensorComplex X A B).hom.f n).val.app (op W)
          (((tensorTotalIsoTensorComplex X A B).inv.f n).val.app (op W) z) = z := by
    intro z
    have := congrArg (fun φ => (SheafOfModules.Hom.val φ).app (op W) z) hcomp
    simpa [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using this
  exact Function.LeftInverse.injective hid hsum

end AlgebraicGeometry.RingedSite

end
