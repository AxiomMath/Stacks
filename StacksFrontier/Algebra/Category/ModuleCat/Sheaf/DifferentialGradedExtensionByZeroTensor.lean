module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedExtensionByZeroTensor

/-!
# Extension by zero and the relative tensor product of differential graded modules

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let
`j : (Sh(C/U), O_U) ⟶ (Sh(C), O)` be the localization morphism. Let `(A, d)` be a sheaf of
differential graded `O`-algebras and `A_U = j^*A` its restriction to the slice site. For a right
differential graded `A_U`-module `M` and a left differential graded `A`-module `N` the source
asserts

`j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)`

as complexes of `O`-modules, functorially in `M` and in `N`. This file proves it.

## Main definitions

* `SheafOfModules.dgExtendTensorIso` is the isomorphism of complexes of `O`-modules
  `j_!M ⊗_A N ≅ j_!(M ⊗_{A_U} N|_U)`, degreewise the isomorphism of Tag 0FRB.

## Main results

* `SheafOfModules.RelativeTensor.dgTensor_d_tmul`: the differential of `P ⊗_A N` on a local
  section `x ⊗ y`, namely `d(x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy`.
* `SheafOfModules.extendTensorInvTranspose_comm`: the comparison of Tag 0FRB commutes with the
  differentials. This is the content the source leaves out, and it is what makes the degreewise
  isomorphism an isomorphism of complexes.
* `SheafOfModules.dgExtendTensorIso_hom_f` and `SheafOfModules.dgExtendTensorIso_inv_f`: the
  isomorphism is degreewise the one of Tag 0FRB, which with
  `SheafOfModules.extendTensorHom_tmul_unit` pins it down on local sections: it sends
  `j_!x ⊗ y` to `j_!(x ⊗ y)`.
* `SheafOfModules.dgExtendTensorIso_naturality_left` and
  `SheafOfModules.dgExtendTensorIso_naturality_right`: the isomorphism is natural in `M` and in
  `N`, which is the functoriality the source asserts. Naturality is stated in each degree, as in
  Tag 0FRB, because the relative tensor product of differential graded modules is available as a
  functor of its right argument only.

## Implementation notes

**Which objects the statement is about.** `j_!M ⊗_A N` and `M ⊗_{A_U} N|_U` are the relative
tensor products of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRelativeTensor.lean`, complexes
of sheaves of modules whose degree `n` is the relative tensor product of the underlying graded
modules and whose differential is `d(x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy`; `j_!` of the second
is applied degreewise, which is `(SheafOfModules.extendSheaf O U).mapHomologicalComplex`. The
degreewise isomorphism, its naturality in `M` and in `N` and its description on local sections
are Tag 0FRB, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedExtensionByZeroTensor.lean`; the differential
graded statement adds exactly the compatibility with the differentials, which is what the source
says is omitted.

**How the compatibility is proved.** It is checked on the *inverse* comparison, and there on its
adjoint transpose `SheafOfModules.extendTensorInvTranspose`, a morphism out of
`M ⊗_{A_U} N|_U` on the slice site. That reduction — the adjunction `j_{U!} ⊣ j_U^*` is a
bijection on Hom-sets, so a square of morphisms out of `j_!(M ⊗_{A_U} N|_U)` may be transposed —
is what makes the universal property of the relative tensor product directly applicable: the
transposed square is an identity of two morphisms out of a relative tensor product, so
`SheafOfModules.RelativeTensor.gradedTensor_hom_ext` reduces it to the local sections `x ⊗ y`,
where both sides are computed by `dgTensor_d_tmul` and the two descriptions of the comparison on
`x ⊗ y`. No bilinear extensionality is needed, unlike in the graded statement, because a square
of *linear* maps is all that has to be matched.

**Base and universes.** As for Tag 0FRB the ringed site is unbundled as a sheaf of commutative
rings `O` on an arbitrary site, the module universe is `max u v m`, forced by the
extension-by-zero adjunction, and the slice site carries its own sheafification hypotheses,
without which the right-hand side is not defined.

## References

* [Stacks Project, Tag 0FRX](https://stacks.math.columbia.edu/tag/0FRX)
* [Stacks Project, Tag 0FRB](https://stacks.math.columbia.edu/tag/0FRB)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open scoped TensorProduct

universe m w v u

namespace SheafOfModules

/-! ### The differential of a relative tensor product on a local section -/

namespace RelativeTensor

section Diff

universe t₁ m₁ v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t₁} RingCat.{t₁})] {Osharp : Sheaf J CommRingCat.{t₁}}
  {A : DifferentialGradedAlgebra.{t₁, m₁} (toRingCat J Osharp)}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasWeakSheafify J AddCommGrpCat.{m₁}]

/-- **The differential of `P ⊗_A N` on a local section `x ⊗ y`:**
`d(x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy`.

This is Tag 0FRM read on a local section. No `@[stacks 0FRM]` attribute is carried here: that
tag is already registered on
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensor`,
and a second site for it in this module would claim a tag this file does not own. -/
theorem dgTensor_d_tmul (P : DifferentialGradedModule.{t₁, m₁, m₁} A)
    (N : LeftDifferentialGradedModule.{t₁, m₁, m₁} A) (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gP P).piece p.1.1).val.obj X) (y : ((gN N).piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app ((dgTensor P N).d n (n + 1)).val X
        (tmul (gP P) (gN N) n p X x y) =
      tmul (gP P) (gN N) (n + 1) (tensorIndexShiftLeft p) X
          ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X x) y +
        (Int.negOnePow p.1.1 : ℤ) • tmul (gP P) (gN N) (n + 1) (tensorIndexShiftRight p) X x
          ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X y) := by
  have hd : (dgTensor P N).d n (n + 1) =
      (PresheafOfModules.sheafification (R := toRingCat J Osharp)
        (𝟙 (toRingCat J Osharp).obj)).map (dgTensorDiffPre P N n) :=
    congrArg (fun φ : gradedTensorPre (gP P) (gN N) n ⟶ gradedTensorPre (gP P) (gN N) (n + 1) =>
      (PresheafOfModules.sheafification (R := toRingCat J Osharp)
        (𝟙 (toRingCat J Osharp).obj)).map φ) (CochainComplex.of_d _ _ n)
  rw [hd]
  refine (PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (dgTensorDiffPre P N n) X _).trans ?_
  have hstep : PresheafOfModules.Hom.app (dgTensorDiffPre P N n) X
        (PresheafOfModules.Hom.app (gradedTensorπ (gP P) (gN N) n) X
          (PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) p) X (x ⊗ₜ y))) =
      PresheafOfModules.Hom.app (gradedTensorπ (gP P) (gN N) (n + 1)) X
        (PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) (tensorIndexShiftLeft p)) X
            ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X x ⊗ₜ y) +
          (Int.negOnePow p.1.1 : ℤ) •
            PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) (tensorIndexShiftRight p)) X
              (x ⊗ₜ (N.complex.d p.1.2 (p.1.2 + 1)).val.app X y)) :=
    ((PresheafOfModules.comp_app_apply (gradedTensorπ (gP P) (gN N) n)
      (dgTensorDiffPre P N n) X _).symm.trans
        ((PresheafOfModules.hom_congr_apply' (gradedTensorπ_dgTensorDiffPre N n) X _).trans
          (PresheafOfModules.comp_app_apply (dgTensorSumDiff P N n)
            (gradedTensorπ (gP P) (gN N) (n + 1)) X _))).trans
      (congrArg (fun t => PresheafOfModules.Hom.app (gradedTensorπ (gP P) (gN N) (n + 1)) X t)
        (dgTensorSumDiff_tensorSumι_apply P N p X x y))
  rw [hstep, map_add, map_zsmul, map_add, map_zsmul]
  rfl

end Diff

end RelativeTensor

/-! ### Extension by zero and the differential: Tag 0FRX -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{w}) (U : C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]
  (A : DifferentialGradedAlgebra.{w, max u v m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
  (M : DifferentialGradedModule.{w, max u v m, max u v m} (A.over U))
  (N : LeftDifferentialGradedModule.{w, max u v m, max u v m} A)

/-- `j_!M ⊗_A N`, as a complex of `O`-modules. -/
noncomputable abbrev dgExtendTensor :
    CochainComplex
      (SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ℤ :=
  RelativeTensor.dgTensor (dgExtensionByZero.{m} O U A M) N

/-- The differential of `j_!M ⊗_A N` on a local section `x ⊗ y`, with the degree-`n` piece of
`j_!M` written as the extension by zero of the degree-`n` piece of `M`. -/
theorem dgExtendTensor_d_tmul (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gradedExtensionByZero.{m} O U A.toGradedAlgebra
      (GradedModule.ofDifferentialGraded M)).piece p.1.1).val.obj X)
    (y : ((LeftGradedModule.ofDifferentialGraded N).piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app ((dgExtendTensor.{m} O U A M N).d n (n + 1)).val X
        (RelativeTensor.tmul (gradedExtensionByZero.{m} O U A.toGradedAlgebra
          (GradedModule.ofDifferentialGraded M))
          (LeftGradedModule.ofDifferentialGraded N) n p X x y) =
      RelativeTensor.tmul (gradedExtensionByZero.{m} O U A.toGradedAlgebra
            (GradedModule.ofDifferentialGraded M))
            (LeftGradedModule.ofDifferentialGraded N) (n + 1)
            (RelativeTensor.tensorIndexShiftLeft p) X
          (((extendSheaf.{m} O U).map (M.gradedDiff p.1.1 (p.1.1 + 1))).val.app X x) y +
        (Int.negOnePow p.1.1 : ℤ) • RelativeTensor.tmul
          (gradedExtensionByZero.{m} O U A.toGradedAlgebra
            (GradedModule.ofDifferentialGraded M))
          (LeftGradedModule.ofDifferentialGraded N) (n + 1)
          (RelativeTensor.tensorIndexShiftRight p) X x
          ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X y) :=
  RelativeTensor.dgTensor_d_tmul (dgExtensionByZero.{m} O U A M) N n p X x y

variable [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v m}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v m}]

/-- `M ⊗_{A_U} N|_U`, as a complex of `O_U`-modules. -/
noncomputable abbrev dgSliceTensor :
    CochainComplex
      (SheafOfModules.{max u v m}
        (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U)) ℤ :=
  RelativeTensor.dgTensor (J := J.over U) (Osharp := O.over U) M (N.over U)

/-- `j_!(M ⊗_{A_U} N|_U)`, as a complex of `O`-modules: extension by zero applied
degreewise. -/
noncomputable abbrev dgExtendSliceTensor :
    CochainComplex
      (SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) ℤ :=
  ((extendSheaf.{m} O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (dgSliceTensor.{m} O U A M N)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}] in
/-- The differential of `M ⊗_{A_U} N|_U` on a local section `x ⊗ y`, with the two factors
written as the restrictions of the underlying graded modules of `M` and of `N`. -/
theorem dgSliceTensor_d_tmul (n : ℤ) (p : TensorIndex n) (V : (Over U)ᵒᵖ)
    (z : ((GradedModule.ofDifferentialGraded M).piece p.1.1).val.obj V)
    (y : (((LeftGradedModule.ofDifferentialGraded N).over U).piece p.1.2).val.obj V) :
    PresheafOfModules.Hom.app ((dgSliceTensor.{m} O U A M N).d n (n + 1)).val V
        (RelativeTensor.tmul (J := J.over U) (Osharp := O.over U)
          (GradedModule.ofDifferentialGraded M)
          ((LeftGradedModule.ofDifferentialGraded N).over U) n p V z y) =
      RelativeTensor.tmul (J := J.over U) (Osharp := O.over U)
            (GradedModule.ofDifferentialGraded M)
            ((LeftGradedModule.ofDifferentialGraded N).over U) (n + 1)
            (RelativeTensor.tensorIndexShiftLeft p) V
          ((M.gradedDiff p.1.1 (p.1.1 + 1)).val.app V z) y +
        (Int.negOnePow p.1.1 : ℤ) • RelativeTensor.tmul (J := J.over U) (Osharp := O.over U)
          (GradedModule.ofDifferentialGraded M)
          ((LeftGradedModule.ofDifferentialGraded N).over U) (n + 1)
          (RelativeTensor.tensorIndexShiftRight p) V z
          ((N.complex.d p.1.2 (p.1.2 + 1)).val.app (op V.unop.left) y) :=
  RelativeTensor.dgTensor_d_tmul (J := J.over U) (Osharp := O.over U) M (N.over U) n p V z y

/-- **The adjoint transpose of the inverse comparison commutes with the differentials.** This is
the compatibility the source leaves out, transposed across the adjunction `j_{U!} ⊣ j_U^*` to a
square of morphisms out of `M ⊗_{A_U} N|_U`, where the universal property of the relative tensor
product applies. -/
theorem extendTensorInvTranspose_comm (n : ℤ) :
    extendTensorInvTranspose.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
          (LeftGradedModule.ofDifferentialGraded N) n ≫
        (overFunctor.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).map
          ((dgExtendTensor.{m} O U A M N).d n (n + 1)) =
      (dgSliceTensor.{m} O U A M N).d n (n + 1) ≫
        extendTensorInvTranspose.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
          (LeftGradedModule.ofDifferentialGraded N) (n + 1) := by
  refine RelativeTensor.gradedTensor_hom_ext (J := J.over U) (Osharp := O.over U)
    (GradedModule.ofDifferentialGraded M) ((LeftGradedModule.ofDifferentialGraded N).over U)
    fun p V z y ↦ ?_
  have hL := congrArg (fun t => PresheafOfModules.Hom.app
      ((dgExtendTensor.{m} O U A M N).d n (n + 1)).val (op V.unop.left) t)
    (extendTensorInvTranspose_tmul.{m} O U A.toGradedAlgebra
      (GradedModule.ofDifferentialGraded M) (LeftGradedModule.ofDifferentialGraded N) n p V z y)
  have hL2 := dgExtendTensor_d_tmul.{m} O U A M N n p (op V.unop.left)
    (((extendSheafAdjunction.{m} O U).unit.app
      ((GradedModule.ofDifferentialGraded M).piece p.1.1)).val.app V z) y
  have hL3 := congrArg (fun t =>
      RelativeTensor.tmul (gradedExtensionByZero.{m} O U A.toGradedAlgebra
            (GradedModule.ofDifferentialGraded M))
            (LeftGradedModule.ofDifferentialGraded N) (n + 1)
            (RelativeTensor.tensorIndexShiftLeft p) (op V.unop.left) t y +
        (Int.negOnePow p.1.1 : ℤ) • RelativeTensor.tmul
          (gradedExtensionByZero.{m} O U A.toGradedAlgebra
            (GradedModule.ofDifferentialGraded M))
          (LeftGradedModule.ofDifferentialGraded N) (n + 1)
          (RelativeTensor.tensorIndexShiftRight p) (op V.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app
            ((GradedModule.ofDifferentialGraded M).piece p.1.1)).val.app V z)
          ((N.complex.d p.1.2 (p.1.2 + 1)).val.app (op V.unop.left) y))
    (extendSheaf_map_unit.{m} O U (M.gradedDiff p.1.1 (p.1.1 + 1)) V z)
  set T := extendTensorInvTranspose.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M) (LeftGradedModule.ofDifferentialGraded N) (n + 1)
  have hR := congrArg (fun t => PresheafOfModules.Hom.app T.val V t)
    (dgSliceTensor_d_tmul.{m} O U A M N n p V z y)
  have hR3 := extendTensorInvTranspose_tmul.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M) (LeftGradedModule.ofDifferentialGraded N) (n + 1)
    (RelativeTensor.tensorIndexShiftLeft p) V
    ((M.gradedDiff p.1.1 (p.1.1 + 1)).val.app V z) y
  have hR4 := extendTensorInvTranspose_tmul.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M) (LeftGradedModule.ofDifferentialGraded N) (n + 1)
    (RelativeTensor.tensorIndexShiftRight p) V z
    ((N.complex.d p.1.2 (p.1.2 + 1)).val.app (op V.unop.left) y)
  refine (hL.trans (hL2.trans hL3)).trans (Eq.symm (hR.trans
    ((map_add (homSections T V) _ _).trans ?_)))
  exact congrArg₂ (· + ·) hR3 ((map_zsmul (homSections T V) _ _).trans (congrArg _ hR4))

/-- **The inverse comparison commutes with the differentials.** -/
theorem extendTensorInv_comm (n : ℤ) :
    extendTensorInv.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
          (LeftGradedModule.ofDifferentialGraded N) n ≫
        (dgExtendTensor.{m} O U A M N).d n (n + 1) =
      (dgExtendSliceTensor.{m} O U A M N).d n (n + 1) ≫
        extendTensorInv.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
          (LeftGradedModule.ofDifferentialGraded N) (n + 1) := by
  have key : ∀ k : ℤ,
      (extendSheafAdjunction.{m} O U).homEquiv
          (sliceTensor.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
            (LeftGradedModule.ofDifferentialGraded N) k)
          (extendTensor.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
            (LeftGradedModule.ofDifferentialGraded N) k)
          (extendTensorInv.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
            (LeftGradedModule.ofDifferentialGraded N) k) =
        extendTensorInvTranspose.{m} O U A.toGradedAlgebra
          (GradedModule.ofDifferentialGraded M)
          (LeftGradedModule.ofDifferentialGraded N) k :=
    fun k => Equiv.apply_symm_apply _ _
  refine ((extendSheafAdjunction.{m} O U).homEquiv
    (sliceTensor.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
      (LeftGradedModule.ofDifferentialGraded N) n)
    (extendTensor.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
      (LeftGradedModule.ofDifferentialGraded N) (n + 1))).injective ?_
  refine ((extendSheafAdjunction.{m} O U).homEquiv_naturality_right
    (extendTensorInv.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
      (LeftGradedModule.ofDifferentialGraded N) n)
    ((dgExtendTensor.{m} O U A M N).d n (n + 1))).trans ?_
  refine (congrArg (fun t => t ≫ (overFunctor.{max u v m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U).map
    ((dgExtendTensor.{m} O U A M N).d n (n + 1))) (key n)).trans ?_
  refine (extendTensorInvTranspose_comm.{m} O U A M N n).trans ?_
  refine (congrArg (fun t => (dgSliceTensor.{m} O U A M N).d n (n + 1) ≫ t)
    (key (n + 1)).symm).trans ?_
  exact ((extendSheafAdjunction.{m} O U).homEquiv_naturality_left
    ((dgSliceTensor.{m} O U A M N).d n (n + 1))
    (extendTensorInv.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
      (LeftGradedModule.ofDifferentialGraded N) (n + 1))).symm

/-- **Tag 0FRX.** The relative tensor product of the extension by zero of a right differential
graded `A_U`-module `M` with a left differential graded `A`-module `N` is the extension by zero
of the relative tensor product of `M` with the restriction of `N`:
`j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)` as complexes of `O`-modules. In each degree it is the
isomorphism of Tag 0FRB, which sends the local section `j_!x ⊗ y` to `j_!(x ⊗ y)` and is natural
in `M` and in `N`; what is proved here is that it commutes with the differentials. -/
@[stacks 0FRX "j_! M ⊗_A N = j_!(M ⊗_{A_U} N|_U) as complexes of O-modules"]
noncomputable def dgExtendTensorIso :
    dgExtendTensor.{m} O U A M N ≅ dgExtendSliceTensor.{m} O U A M N :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun n => (extendTensorIso.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
      (LeftGradedModule.ofDifferentialGraded N) n).symm)
    (fun i j hij => by
      obtain rfl : j = i + 1 := hij.symm
      exact extendTensorInv_comm.{m} O U A M N i)).symm

/-- The degree `n` component of the forward map of `dgExtendTensorIso` is the degreewise map
`extendTensorHom`. -/
@[simp]
theorem dgExtendTensorIso_hom_f (n : ℤ) :
    (dgExtendTensorIso.{m} O U A M N).hom.f n =
      extendTensorHom.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
        (LeftGradedModule.ofDifferentialGraded N) n := rfl

/-- The degree `n` component of the inverse map of `dgExtendTensorIso` is the degreewise map
`extendTensorInv`. -/
@[simp]
theorem dgExtendTensorIso_inv_f (n : ℤ) :
    (dgExtendTensorIso.{m} O U A M N).inv.f n =
      extendTensorInv.{m} O U A.toGradedAlgebra (GradedModule.ofDifferentialGraded M)
        (LeftGradedModule.ofDifferentialGraded N) n := rfl

/-- **Tag 0FRX, functoriality in the right differential graded module.** In every degree the
identification `j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)` commutes with a homomorphism `M ⟶ M'` of right
differential graded `A_U`-modules; its components are the degreewise maps of the relative tensor
products induced by `j_!M ⟶ j_!M'`, respectively by `M ⟶ M'`. -/
@[stacks 0FRX "functoriality of j_! M ⊗_A N = j_!(M ⊗_{A_U} N|_U) in M, in each degree"]
theorem dgExtendTensorIso_naturality_left
    {M' : DifferentialGradedModule.{w, max u v m, max u v m} (A.over U)} (h : M ⟶ M') (n : ℤ) :
    RelativeTensor.gradedTensorMapRight (gradedExtensionByZeroMap.{m} O U A.toGradedAlgebra
          (GradedModule.ofDifferentialGradedMap h))
          (LeftGradedModule.ofDifferentialGraded N) n ≫
        (dgExtendTensorIso.{m} O U A M' N).hom.f n =
      (dgExtendTensorIso.{m} O U A M N).hom.f n ≫ (extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMapRight (J := J.over U) (Osharp := O.over U)
          (GradedModule.ofDifferentialGradedMap h)
          ((LeftGradedModule.ofDifferentialGraded N).over U) n) :=
  extendTensorHom_naturality_left.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M) (LeftGradedModule.ofDifferentialGraded N)
    (GradedModule.ofDifferentialGradedMap h) n

/-- **Tag 0FRX, functoriality in the left differential graded module.** In every degree the
identification `j_!M ⊗_A N = j_!(M ⊗_{A_U} N|_U)` commutes with a homomorphism `N ⟶ N'` of left
differential graded `A`-modules. -/
@[stacks 0FRX "functoriality of j_! M ⊗_A N = j_!(M ⊗_{A_U} N|_U) in N, in each degree"]
theorem dgExtendTensorIso_naturality_right
    {N' : LeftDifferentialGradedModule.{w, max u v m, max u v m} A} (f : N ⟶ N') (n : ℤ) :
    RelativeTensor.gradedTensorMap (gradedExtensionByZero.{m} O U A.toGradedAlgebra
          (GradedModule.ofDifferentialGraded M))
          (LeftGradedModule.ofDifferentialGradedMap f) n ≫
        (dgExtendTensorIso.{m} O U A M N').hom.f n =
      (dgExtendTensorIso.{m} O U A M N).hom.f n ≫ (extendSheaf.{m} O U).map
        (RelativeTensor.gradedTensorMap (J := J.over U) (Osharp := O.over U)
          (GradedModule.ofDifferentialGraded M)
          (LeftGradedModule.overMap (LeftGradedModule.ofDifferentialGradedMap f) U) n) :=
  extendTensorHom_naturality_right.{m} O U A.toGradedAlgebra
    (GradedModule.ofDifferentialGraded M) (LeftGradedModule.ofDifferentialGraded N)
    (LeftGradedModule.ofDifferentialGradedMap f) n

end SheafOfModules

end
