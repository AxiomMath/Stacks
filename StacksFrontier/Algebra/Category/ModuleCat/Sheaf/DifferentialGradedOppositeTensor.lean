module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedOppositeModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedExtensionByZeroTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative tensor product read over the opposite algebra

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras, let `M`
be a right differential graded `A`-module and let `P` be a right differential graded
`A.op`-module. Interchanging the two factors of a tensor product and twisting by the Koszul
sign identifies

`P ⊗_{A.op} M.opLeft ≅ M ⊗_A P.unopLeft`

as cochain complexes of sheaves of `O`-modules: on local sections of degrees `p` and `q` the
isomorphism sends `u ⊗ w` to `(-1)^{p q} w ⊗ u`.

## Main definitions

* `SheafOfModules.RelativeTensor.opSwap` is the comparison in one degree, `opUnswap` the
  comparison in the other direction and `SheafOfModules.RelativeTensor.dgTensorOpIso` the
  isomorphism of cochain complexes they assemble into.
* `SheafOfModules.RelativeTensor.dgTensorD` is the differential of the relative tensor product
  with its source and target read as the graded tensor products they are, so that every
  computation on local sections speaks of one and the same object in each degree.

## Main results

* `SheafOfModules.RelativeTensor.dgTensorD_tmul` computes the differential of the relative
  tensor product on a local section `u ⊗ w`, with the degrees read as the graded tensor
  products.
* `SheafOfModules.RelativeTensor.opSwap_tmul` computes the comparison on a local section, and
  `SheafOfModules.RelativeTensor.acyclic_dgTensor_of_acyclic_dgTensor_op` transports acyclicity
  across the isomorphism.

## Implementation notes

The comparison is built in each degree from the universal property of the relative tensor
product: the family `(u, w) ↦ (-1)^{p q} w ⊗ u` is bilinear because `w ⊗ u` is, and it is
balanced because the balance relation on the other side is the balance relation of `A` with the
two interchanged actions substituted — the computation is three applications of the Koszul sign
and the identity `(-1)^{r s}(-1)^{s t}(-1)^{s r} = (-1)^{(r + s) t}` modulo squares. The
inverse is the same construction with the roles of the two factors exchanged, so the two
composites are the identity by the uniqueness half of the universal property.

The degrees of the relative tensor product carry two spellings, `(P ⊗_A N).X n` and the graded
tensor product itself, which are the same object but not the same expression; `dgTensorD` fixes
the second one, and every statement below uses it, so that the rewrites of a computation never
have to cross between them.

The compatibility with the differentials is checked on local sections as well, through
`dgTensorD_tmul`: both the source and the target differential send `u ⊗ w` to
`du ⊗ w + (-1)^{deg u} u ⊗ dw`, and the signs match because
`(-1)^{p}(-1)^{p (q + 1)} = (-1)^{p q}` and `(-1)^{(p + 1) q} = (-1)^{p q}(-1)^{q}`.

## References

* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t m v u

attribute [local implicit_reducible] SheafOfModules.DifferentialGradedAlgebra.op
  SheafOfModules.GradedModule.ofDifferentialGraded
  SheafOfModules.LeftGradedModule.ofDifferentialGraded
  SheafOfModules.DifferentialGradedModule.opLeft
  SheafOfModules.DifferentialGradedModule.unopLeft
  SheafOfModules.LeftDifferentialGradedModule.opRight

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-! ### Local sections of the relative tensor product -/

section Graded

variable {B : GradedAlgebra.{t, m} (toRingCat J Osharp)} (F : GradedModule.{t, m, m} B)
  (G : LeftGradedModule.{t, m, m} B)

/-- A local section of the relative tensor product takes an integer multiple in its second
factor to an integer multiple. -/
theorem tmul_zsmul_right (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) (ε : ℤ)
    (u : (F.piece p.1.1).val.obj X) (w : (G.piece p.1.2).val.obj X) :
    tmul F G n p X u (ε • w) = ε • tmul F G n p X u w :=
  ((tmulBalanced F G n).app p).app_zsmul_right ε X u w

end Graded

/-! ### The differential on local sections -/

/-- The sheafification unit after the projection of the presentation, on sections: it is
additive and compatible with integer multiples. -/
theorem tmulθ_add_zsmul {B : GradedAlgebra.{t, m} (toRingCat J Osharp)}
    (F : GradedModule.{t, m, m} B) (G : LeftGradedModule.{t, m, m} B) (n : ℤ) (X : Cᵒᵖ) (ε : ℤ)
    (a b : (tensorSum F G n).obj X) :
    PresheafOfModules.Hom.app (gradedTensorUnit F G n) X
        (PresheafOfModules.Hom.app (gradedTensorπ F G n) X (a + ε • b)) =
      PresheafOfModules.Hom.app (gradedTensorUnit F G n) X
          (PresheafOfModules.Hom.app (gradedTensorπ F G n) X a) +
        ε • PresheafOfModules.Hom.app (gradedTensorUnit F G n) X
          (PresheafOfModules.Hom.app (gradedTensorπ F G n) X b) := by
  rw [map_add (ConcreteCategory.hom (PresheafOfModules.Hom.app (gradedTensorπ F G n) X)),
    map_zsmul (ConcreteCategory.hom (PresheafOfModules.Hom.app (gradedTensorπ F G n) X)),
    map_add (ConcreteCategory.hom (PresheafOfModules.Hom.app (gradedTensorUnit F G n) X)),
    map_zsmul (ConcreteCategory.hom (PresheafOfModules.Hom.app (gradedTensorUnit F G n) X))]

variable {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- The differential of the relative tensor product, with its source and target read as the
graded tensor products they are. -/
noncomputable abbrev dgTensorD (P : DifferentialGradedModule.{t, m, m} A)
    (N : LeftDifferentialGradedModule.{t, m, m} A) (n : ℤ) :
    gradedTensor (gP P) (gN N) n ⟶ gradedTensor (gP P) (gN N) (n + 1) :=
  (dgTensor P N).d n (n + 1)

/-- **The differential of the relative tensor product on a local section**, with the degrees
read as the graded tensor products they are: it sends `u ⊗ w` to
`du ⊗ w + (-1)^{deg u} u ⊗ dw`. -/
theorem dgTensorD_tmul (P : DifferentialGradedModule.{t, m, m} A)
    (N : LeftDifferentialGradedModule.{t, m, m} A) (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (u : ((gP P).piece p.1.1).val.obj X) (w : ((gN N).piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (dgTensorD P N n).val X (tmul (gP P) (gN N) n p X u w) =
      tmul (gP P) (gN N) (n + 1) (tensorIndexShiftLeft p) X
          ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u) w +
        (Int.negOnePow p.1.1 : ℤ) •
          tmul (gP P) (gN N) (n + 1) (tensorIndexShiftRight p) X u
            ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X w) :=
  dgTensor_d_tmul P N n p X u w

/-! ### The interchange -/

/-- The interchanged summand index. -/
abbrev swapIndex {n : ℤ} (q : TensorIndex n) : TensorIndex n :=
  ⟨(q.1.2, q.1.1), (Int.add_comm q.1.2 q.1.1).trans q.2⟩

variable (M : DifferentialGradedModule.{t, m, m} A)
  (P : DifferentialGradedModule.{t, m, m} A.op)

/-- **The interchanging bilinear family.** On local sections of degrees `p` and `q` it sends
`(u, w)` to `(-1)^{p q} w ⊗ u`; it is balanced because the balance relation of `A.op` becomes
the balance relation of `A` once the two interchanged actions are written out. -/
noncomputable def opSwapBalanced (n : ℤ) :
    Balanced (gP P) (gN M.opLeft) (gradedTensor (gP M) (gN P.unopLeft) n).val n where
  app q :=
    (((tmulBalanced (gP M) (gN P.unopLeft) n).app (swapIndex q)).flip).intSmul
      (Int.negOnePow (q.1.1 * q.1.2))
  balanced := by
    rintro ⟨⟨r, s, t⟩, hrst⟩ X u α w
    have hrst' : r + s + t = n := hrst
    have hn : t + s + r = n := by omega
    have hbal : tmul (gP M) (gN P.unopLeft) n ⟨(t + s, r), hn⟩ X
          ((M.mul t s).app X w α) u =
        tmul (gP M) (gN P.unopLeft) n ⟨(t, s + r), by omega⟩ X w
          ((P.unopLeftMul s r).app X α u) :=
      (tmulBalanced (gP M) (gN P.unopLeft) n).balanced ⟨(t, s, r), hn⟩ X w α u
    have hsign : (Int.negOnePow (r * (s + t)) : ℤ) * (Int.negOnePow (s * t) : ℤ) *
        (Int.negOnePow (s * r) : ℤ) = (Int.negOnePow ((r + s) * t) : ℤ) := by
      rw [← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add, ← Int.negOnePow_add,
        show r * (s + t) + s * t + s * r = (r + s) * t + 2 * (s * r) by ring,
        Int.negOnePow_add, Int.negOnePow_two_mul, _root_.mul_one]
    change (Int.negOnePow ((r + s) * t) : ℤ) •
        tmul (gP M) (gN P.unopLeft) n ⟨(t, r + s), by omega⟩ X w ((P.mul r s).app X u α) =
      (Int.negOnePow (r * (s + t)) : ℤ) •
        tmul (gP M) (gN P.unopLeft) n ⟨(s + t, r), by omega⟩ X
          ((M.opLeftMul s t).app X α w) u
    rw [M.opLeftMul_app, tmul_cast_left, tmul_zsmul_left, hbal, P.unopLeftMul_app,
      tmul_cast_right, tmul_zsmul_right, smul_smul, smul_smul, hsign]
    all_goals omega

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
/-- A morphism of sheaves of modules is additive on local sections. -/
theorem hom_val_app_add {K K' : SheafOfModules.{m} (toRingCat J Osharp)} (φ : K ⟶ K')
    (X : Cᵒᵖ) (z z' : K.val.obj X) :
    PresheafOfModules.Hom.app φ.val X (z + z') =
      PresheafOfModules.Hom.app φ.val X z + PresheafOfModules.Hom.app φ.val X z' :=
  map_add (ConcreteCategory.hom (PresheafOfModules.Hom.app φ.val X)) z z'

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify J AddCommGrpCat] in
/-- A morphism of sheaves of modules commutes with integer multiples of local sections. -/
theorem hom_val_app_zsmul {K K' : SheafOfModules.{m} (toRingCat J Osharp)} (φ : K ⟶ K')
    (X : Cᵒᵖ) (ε : ℤ) (z : K.val.obj X) :
    PresheafOfModules.Hom.app φ.val X (ε • z) = ε • PresheafOfModules.Hom.app φ.val X z :=
  map_zsmul (ConcreteCategory.hom (PresheafOfModules.Hom.app φ.val X)) ε z

/-- The differential of the relative tensor product is additive on local sections. -/
theorem dgTensorD_add (P' : DifferentialGradedModule.{t, m, m} A)
    (N' : LeftDifferentialGradedModule.{t, m, m} A) (n : ℤ) (X : Cᵒᵖ)
    (z z' : (gradedTensor (gP P') (gN N') n).val.obj X) :
    PresheafOfModules.Hom.app (dgTensorD P' N' n).val X (z + z') =
      PresheafOfModules.Hom.app (dgTensorD P' N' n).val X z +
        PresheafOfModules.Hom.app (dgTensorD P' N' n).val X z' :=
  hom_val_app_add _ X z z'

/-- The differential of the relative tensor product commutes with integer multiples of local
sections. -/
theorem dgTensorD_zsmul (P' : DifferentialGradedModule.{t, m, m} A)
    (N' : LeftDifferentialGradedModule.{t, m, m} A) (n : ℤ) (X : Cᵒᵖ) (ε : ℤ)
    (z : (gradedTensor (gP P') (gN N') n).val.obj X) :
    PresheafOfModules.Hom.app (dgTensorD P' N' n).val X (ε • z) =
      ε • PresheafOfModules.Hom.app (dgTensorD P' N' n).val X z :=
  hom_val_app_zsmul _ X ε z

/-- The interchanging bilinear family in the other direction. -/
noncomputable def opUnswapBalanced (n : ℤ) :
    Balanced (gP M) (gN P.unopLeft) (gradedTensor (gP P) (gN M.opLeft) n).val n where
  app q :=
    (((tmulBalanced (gP P) (gN M.opLeft) n).app (swapIndex q)).flip).intSmul
      (Int.negOnePow (q.1.1 * q.1.2))
  balanced := by
    rintro ⟨⟨r, s, t⟩, hrst⟩ X x α y
    have hrst' : r + s + t = n := hrst
    have hn : t + s + r = n := by omega
    have hbal : tmul (gP P) (gN M.opLeft) n ⟨(t + s, r), hn⟩ X
          ((P.mul t s).app X y α) x =
        tmul (gP P) (gN M.opLeft) n ⟨(t, s + r), by omega⟩ X y
          ((M.opLeftMul s r).app X α x) :=
      (tmulBalanced (gP P) (gN M.opLeft) n).balanced ⟨(t, s, r), hn⟩ X y α x
    have hsign : (Int.negOnePow (r * (s + t)) : ℤ) * (Int.negOnePow (s * t) : ℤ) *
        (Int.negOnePow (s * r) : ℤ) = (Int.negOnePow ((r + s) * t) : ℤ) := by
      rw [← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add, ← Int.negOnePow_add,
        show r * (s + t) + s * t + s * r = (r + s) * t + 2 * (s * r) by ring,
        Int.negOnePow_add, Int.negOnePow_two_mul, _root_.mul_one]
    change (Int.negOnePow ((r + s) * t) : ℤ) •
        tmul (gP P) (gN M.opLeft) n ⟨(t, r + s), by omega⟩ X y ((M.mul r s).app X x α) =
      (Int.negOnePow (r * (s + t)) : ℤ) •
        tmul (gP P) (gN M.opLeft) n ⟨(s + t, r), by omega⟩ X
          ((P.unopLeftMul s t).app X α y) x
    rw [P.unopLeftMul_app, tmul_cast_left, tmul_zsmul_left, hbal, M.opLeftMul_app,
      tmul_cast_right, tmul_zsmul_right, smul_smul, smul_smul, hsign]
    all_goals omega

/-- **The interchange in one degree**, from the relative tensor product over `A.op` to the
relative tensor product over `A`. -/
noncomputable def opSwap (n : ℤ) :
    gradedTensor (gP P) (gN M.opLeft) n ⟶ gradedTensor (gP M) (gN P.unopLeft) n :=
  (opSwapBalanced M P n).desc (gP P) (gN M.opLeft)

/-- **The interchange in one degree**, in the other direction. -/
noncomputable def opUnswap (n : ℤ) :
    gradedTensor (gP M) (gN P.unopLeft) n ⟶ gradedTensor (gP P) (gN M.opLeft) n :=
  (opUnswapBalanced M P n).desc (gP M) (gN P.unopLeft)

/-- The interchange on a local section: it sends `u ⊗ w` to `(-1)^{p q} w ⊗ u`. -/
theorem opSwap_tmul (n : ℤ) (q : TensorIndex n) (X : Cᵒᵖ)
    (u : ((gP P).piece q.1.1).val.obj X) (w : ((gN M.opLeft).piece q.1.2).val.obj X) :
    PresheafOfModules.Hom.app (opSwap M P n).val X (tmul (gP P) (gN M.opLeft) n q X u w) =
      (Int.negOnePow (q.1.1 * q.1.2) : ℤ) •
        tmul (gP M) (gN P.unopLeft) n (swapIndex q) X w u :=
  Balanced.desc_tmul (gP P) (gN M.opLeft) (opSwapBalanced M P n) q X u w

/-- The interchange in the other direction on a local section: it sends `x ⊗ y` to
`(-1)^{p q} y ⊗ x`. -/
theorem opUnswap_tmul (n : ℤ) (q : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gP M).piece q.1.1).val.obj X) (y : ((gN P.unopLeft).piece q.1.2).val.obj X) :
    PresheafOfModules.Hom.app (opUnswap M P n).val X (tmul (gP M) (gN P.unopLeft) n q X x y) =
      (Int.negOnePow (q.1.1 * q.1.2) : ℤ) •
        tmul (gP P) (gN M.opLeft) n (swapIndex q) X y x :=
  Balanced.desc_tmul (gP M) (gN P.unopLeft) (opUnswapBalanced M P n) q X x y

/-- The two interchanges are inverse to one another. -/
theorem opSwap_opUnswap (n : ℤ) : opSwap M P n ≫ opUnswap M P n = 𝟙 _ := by
  refine gradedTensor_hom_ext (gP P) (gN M.opLeft) fun q X u w ↦ ?_
  change PresheafOfModules.Hom.app (opUnswap M P n).val X
      (PresheafOfModules.Hom.app (opSwap M P n).val X
        (tmul (gP P) (gN M.opLeft) n q X u w)) = tmul (gP P) (gN M.opLeft) n q X u w
  rw [opSwap_tmul, hom_val_app_zsmul, opUnswap_tmul, smul_smul, Int.mul_comm q.1.2 q.1.1,
    negOnePow_mul_negOnePow, one_smul]

/-- The two interchanges are inverse to one another. -/
theorem opUnswap_opSwap (n : ℤ) : opUnswap M P n ≫ opSwap M P n = 𝟙 _ := by
  refine gradedTensor_hom_ext (gP M) (gN P.unopLeft) fun q X x y ↦ ?_
  change PresheafOfModules.Hom.app (opSwap M P n).val X
      (PresheafOfModules.Hom.app (opUnswap M P n).val X
        (tmul (gP M) (gN P.unopLeft) n q X x y)) = tmul (gP M) (gN P.unopLeft) n q X x y
  rw [opUnswap_tmul, hom_val_app_zsmul, opSwap_tmul, smul_smul, Int.mul_comm q.1.2 q.1.1,
    negOnePow_mul_negOnePow, one_smul]

/-- **The interchange commutes with the differentials.** -/
theorem opSwap_comm_d (n : ℤ) :
    opSwap M P n ≫ dgTensorD M P.unopLeft n = dgTensorD P M.opLeft n ≫ opSwap M P (n + 1) := by
  refine gradedTensor_hom_ext (gP P) (gN M.opLeft) fun q X u w ↦ ?_
  have hsign₁ : (Int.negOnePow (q.1.1 * q.1.2) : ℤ) * (Int.negOnePow q.1.2 : ℤ) =
      (Int.negOnePow ((q.1.1 + 1) * q.1.2) : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    ring
  have hsign₂ : (Int.negOnePow q.1.1 : ℤ) * (Int.negOnePow (q.1.1 * (q.1.2 + 1)) : ℤ) =
      (Int.negOnePow (q.1.1 * q.1.2) : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add,
      show q.1.1 + q.1.1 * (q.1.2 + 1) = q.1.1 * q.1.2 + 2 * q.1.1 by ring, Int.negOnePow_add,
      Int.negOnePow_two_mul, _root_.mul_one]
  change PresheafOfModules.Hom.app (dgTensorD M P.unopLeft n).val X
      (PresheafOfModules.Hom.app (opSwap M P n).val X
        (tmul (gP P) (gN M.opLeft) n q X u w)) =
    PresheafOfModules.Hom.app (opSwap M P (n + 1)).val X
      (PresheafOfModules.Hom.app (dgTensorD P M.opLeft n).val X
        (tmul (gP P) (gN M.opLeft) n q X u w))
  rw [opSwap_tmul, dgTensorD_zsmul, dgTensorD_tmul, dgTensorD_tmul, hom_val_app_add,
    hom_val_app_zsmul, opSwap_tmul, opSwap_tmul, smul_add, smul_smul, smul_smul, hsign₁,
    hsign₂]
  exact add_comm _ _

/-- **The relative tensor product read over the opposite algebra.** Interchanging the two
factors and twisting by the Koszul sign identifies `P ⊗_{A.op} M.opLeft` with
`M ⊗_A P.unopLeft`. -/
@[stacks 0FRM "the relative tensor product of the opposite algebra, interchanged"]
noncomputable def dgTensorOpIso : dgTensor P M.opLeft ≅ dgTensor M P.unopLeft :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      { hom := opSwap M P n
        inv := opUnswap M P n
        hom_inv_id := opSwap_opUnswap M P n
        inv_hom_id := opUnswap_opSwap M P n })
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      exact opSwap_comm_d M P i)

/-- Acyclicity transported across the interchange: if the relative tensor product over `A.op`
is acyclic then so is the relative tensor product over `A`. -/
theorem acyclic_dgTensor_of_acyclic_dgTensor_op (h : (dgTensor P M.opLeft).Acyclic) :
    (dgTensor M P.unopLeft).Acyclic := fun i ↦
  (_root_.exactAt_iff_of_quasiIsoAt (dgTensorOpIso M P).hom i).1 (h i)

end RelativeTensor

end SheafOfModules

end
