module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinProjection

/-!
# Multiplication by a generator coming from a finite free sheaf, split into its coordinates

Let `A` be a sheaf of graded algebras on a site with a sheaf of commutative rings, let `I` be a
finite index type and let `c : ⊕_I 𝒪 ⟶ M₁` be a morphism out of the free sheaf of modules on `I`.
Composing with a degree-one generator `ι : M₁ ⟶ A_1` and multiplying,
`SheafOfModules.GradedAlgebra.generatorMul (c ≫ ι) k : (⊕_I 𝒪) ⊗ A_k ⟶ A_{1+k}`, carries
`e ⊗ y` to `(c ≫ ι)(e) · y`. Since `c` is determined by the family of global sections
`γ_j = (c ≫ ι)(e_j)` of `A_1`, that map is the sum over `j` of "take the `j`-th coordinate, then
multiply on the left by `γ_j`".

This is what lets the first map of the sequence of [Stacks, Tag 01CJ] be handled one equation at
a time: its source is a tensor product, so a morphism out of it cannot be tested on sections,
whereas each summand factors through left multiplication by a single degree-one global section.

## Main definitions

* `Stacks.SheafOfModules.freeCoordTensorPresheaf` and
  `Stacks.SheafOfModules.freeCoordTensorHom`: contraction with the `j`-th coordinate,
  `(⊕_I 𝒪) ⊗ N ⟶ N`, `e ⊗ y ↦ e_j · y`, on the objectwise tensor product of the underlying
  presheaves and on the tensor product of sheaves.

## Main results

* `Stacks.SheafOfModules.freeCoordTensorHom_unit`: the value of the contraction on the image of a
  pure tensor.
* `SheafOfModules.GradedAlgebra.generatorMul_eq_sum`: **multiplication by a generator coming from
  a finite free sheaf is the sum of the coordinate contractions followed by left multiplication
  by the corresponding global sections.**

## Implementation notes

The scalar laws of the contraction need the ring of sections to be commutative in one place
only — `e_j · (r · y) = r · (e_j · y)` — and that is available because the sheaf of rings is
`CategoryTheory.Sheaf.toRingCat J Osharp` for a sheaf `Osharp` of commutative rings, which is the
generality `SheafOfModules.GradedAlgebra.generatorMul` is stated in anyway. The other four laws
are the module axioms and the additivity of a coordinate functional.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf PresheafOfModules
open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Contraction with the `j`-th coordinate of a finite free sheaf of modules**, on the
objectwise tensor product of the underlying presheaves: `e ⊗ y ↦ e_j · y`. -/
noncomputable def freeCoordTensorPresheaf {I : Type w} [DecidableEq I]
    (N : SheafOfModules.{w} (toRingCat J Osharp)) (j : I) :
    tensorObj (_root_.SheafOfModules.free (R := toRingCat J Osharp) I).val N.val ⟶ N.val :=
  tensorMk (fun V s y => freeCoord (S := toRingCat J Osharp) V s j • y)
    (fun V s s' y => by
      rw [show freeCoord (S := toRingCat J Osharp) V (s + s') j
          = freeCoord (S := toRingCat J Osharp) V s j
            + freeCoord (S := toRingCat J Osharp) V s' j from
          ((freeProj j).val.app V).hom.map_add s s', add_smul])
    (fun V r s y => by
      rw [show freeCoord (S := toRingCat J Osharp) V (r • s) j
          = r * freeCoord (S := toRingCat J Osharp) V s j from
          ((freeProj j).val.app V).hom.map_smul r s, mul_smul])
    (fun _ s y y' => smul_add _ y y')
    (fun _ r _ _ => by rw [smul_smul, smul_smul, mul_comm])
    (fun {V _} f s y =>
      (N.val.map_smul f (freeCoord (S := toRingCat J Osharp) V s j) y).trans
        (congrArg (fun c => c • N.val.restrictₛₗ f y)
          (restrictₛₗ_naturality_apply (freeProj (S := toRingCat J Osharp) j).val f s).symm))

/-- **Contraction with the `j`-th coordinate of a finite free sheaf of modules**, as a morphism
of sheaves of modules `(⊕_I 𝒪) ⊗ N ⟶ N`. -/
noncomputable def freeCoordTensorHom {I : Type w} [DecidableEq I]
    (N : SheafOfModules.{w} (toRingCat J Osharp)) (j : I) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj
      (_root_.SheafOfModules.free I)).obj N ⟶ N :=
  tensorSheafDesc (freeCoordTensorPresheaf N j)

/-- The contraction with a coordinate, on the image of a pure tensor. -/
@[simp]
theorem freeCoordTensorHom_unit {I : Type w} [DecidableEq I]
    (N : SheafOfModules.{w} (toRingCat J Osharp)) (j : I) (V : Cᵒᵖ)
    (s : (_root_.SheafOfModules.free (R := toRingCat J Osharp) I).val.obj V)
    (y : N.val.obj V) :
    (freeCoordTensorHom N j).val.app V
        ((tensorSheafUnit (_root_.SheafOfModules.free I) N).app V (s ⊗ₜ y)) =
      freeCoord (S := toRingCat J Osharp) V s j • y :=
  (tensorSheafDesc_unit (freeCoordTensorPresheaf N j) V s y).trans
    (tensorMk_tmul _ _ _ _ _ _ _ _ _)

end Stacks.SheafOfModules

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Multiplication by a degree-one generator coming from a finite free sheaf of modules is the
sum of the coordinate contractions followed by left multiplication.** For `c : ⊕_I 𝒪 ⟶ M₁` and a
degree-one generator `ι : M₁ ⟶ A_1`, the map `e ⊗ y ↦ (c ≫ ι)(e) · y` is
`∑_j (e ⊗ y ↦ e_j · y) ≫ (y ↦ γ_j · y)`, where `γ_j` is the global section `(c ≫ ι)(e_j)` of
`A_1`. -/
theorem generatorMul_eq_sum {I : Type w} [DecidableEq I] [Fintype I]
    {M₁ : SheafOfModules.{w} (toRingCat J Osharp)}
    {A : GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (c : SheafOfModules.free I ⟶ M₁) (ι : M₁ ⟶ A.piece 1) (k : ℤ) :
    generatorMul (c ≫ ι) k =
      ∑ j : I, Stacks.SheafOfModules.freeCoordTensorHom (A.piece k) j ≫
        A.leftMul 1 k ((A.piece 1).freeHomEquiv (c ≫ ι) j) := by
  classical
  refine tensorSheaf_hom_ext fun V s y => ?_
  refine (generatorMul_unit (c ≫ ι) k V s y).trans ?_
  refine Eq.trans ?_ (Stacks.SheafOfModules.app_sum Finset.univ
    (fun j => Stacks.SheafOfModules.freeCoordTensorHom (A.piece k) j ≫
      A.leftMul 1 k ((A.piece 1).freeHomEquiv (c ≫ ι) j)) V _).symm
  refine Eq.trans (congrArg (fun z => (A.mul 1 k).flip.app V y z)
    (Stacks.SheafOfModules.app_eq_sum_smul_freeCoord (c ≫ ι) V s)) ?_
  refine (map_sum ((A.mul 1 k).flip.app V y) _ Finset.univ).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  exact ((A.mul 1 k).map_smul_left V _ _ y).trans
    (((A.mul 1 k).map_smul_right V _ _ y).symm.trans
      (congrArg (fun z => (A.mul 1 k).app V (((A.piece 1).freeHomEquiv (c ≫ ι) j).eval V) z)
        (Stacks.SheafOfModules.freeCoordTensorHom_unit (A.piece k) j V s y)).symm)

end SheafOfModules.GradedAlgebra

end
