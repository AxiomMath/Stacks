module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensor
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The relative tensor product of differential graded modules over a sheaf of algebras

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of differential graded
`O`-algebras, let `P` be a right differential graded `A`-module and let `N` be a left
differential graded `A`-module. The relative tensor product `P ⊗_A N` is the relative tensor
product of the underlying graded modules, with the differential
`d(x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy`.

## Main definitions

* `SheafOfModules.RelativeTensor.dgTensorSumDiff` is the signed differential on the direct sum
  `⨁_{p + q = n} P^p ⊗_O N^q`, and `SheafOfModules.RelativeTensor.relationSumDiff` is its
  counterpart on the direct sum of relations.
* `SheafOfModules.RelativeTensor.dgTensorDiff` is the induced differential on `P ⊗_A N`, and
  `SheafOfModules.RelativeTensor.dgTensor` is `P ⊗_A N` as a cochain complex of sheaves of
  modules.
* `SheafOfModules.RelativeTensor.IsKFlat` is condition (2) in the definition of a good
  differential graded module.
* `SheafOfModules.RelativeTensor.dgTensorPreMap` is the map of complexes induced by a morphism of
  right differential graded modules, and `SheafOfModules.RelativeTensor.dgTensorFunctor` is the
  functor `- ⊗_A N` from right differential graded `A`-modules to complexes of `O`-modules.

## Main results

* `SheafOfModules.RelativeTensor.dgTensorSumDiff_balance`: the signed differential is compatible
  with the balance maps, which is what makes it descend to the relative tensor product. The
  content is the two Leibniz rules, for the right action on `P` and the left action on `N`.

## Implementation notes

The differential is produced on the direct sum `⨁_{p + q = n} P^p ⊗_O N^q` and descended to the
cokernel of the balance map; the hypothesis of the descent is the compatibility with the balance
map of degree `n + 1`, not merely the vanishing of a composite, so the differential of the
relative tensor product is *constructed* rather than asserted to exist.

Degrees indexing the two sides of a Leibniz rule agree only propositionally: `(r + 1) + s` and
`(r + s) + 1` are equal integers but not definitionally equal, so the module containing `(dx)a`
is not the module containing `d(xa)`. The transports this forces are `SheafOfModules.gradedCast`,
exactly as in the Leibniz fields of `SheafOfModules.DifferentialGradedModule`, and they are
removed from the computation by `SheafOfModules.RelativeTensor.tensorSumι_cast_left` and
`tensorSumι_cast_right`, which identify a summand inclusion applied to a transported section
with the inclusion of the summand of the untransported degree.

## References

* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

namespace RelativeTensor

section Cast

variable {A : GradedAlgebra.{t, m} (toRingCat J Osharp)} (P : GradedModule.{t, m, m} A)
  (N : LeftGradedModule.{t, m, m} A)

/-- The inclusion of a summand applied to a section transported along an equality of degrees in
the first factor is the inclusion of the summand of the untransported degree. -/
theorem tensorSumι_cast_left {p p' q n : ℤ} (hp : p = p') (h : p + q = n) (X : Cᵒᵖ)
    (u : (P.piece p).val.obj X) (w : (N.piece q).val.obj X) :
    PresheafOfModules.Hom.app
        (tensorSumι P N (⟨(p', q), by rw [← hp]; exact h⟩ : TensorIndex n)) X
        (gradedCast (fun k ↦ (P.piece k).val.obj X) hp u ⊗ₜ w) =
      PresheafOfModules.Hom.app (tensorSumι P N (⟨(p, q), h⟩ : TensorIndex n)) X (u ⊗ₜ w) := by
  subst hp
  rfl

/-- The inclusion of a summand applied to a section transported along an equality of degrees in
the second factor is the inclusion of the summand of the untransported degree. -/
theorem tensorSumι_cast_right {p q q' n : ℤ} (hq : q = q') (h : p + q = n) (X : Cᵒᵖ)
    (u : (P.piece p).val.obj X) (w : (N.piece q).val.obj X) :
    PresheafOfModules.Hom.app
        (tensorSumι P N (⟨(p, q'), by rw [← hq]; exact h⟩ : TensorIndex n)) X
        (u ⊗ₜ gradedCast (fun k ↦ (N.piece k).val.obj X) hq w) =
      PresheafOfModules.Hom.app (tensorSumι P N (⟨(p, q), h⟩ : TensorIndex n)) X (u ⊗ₜ w) := by
  subst hq
  rfl

/-- The balance map on the inclusion of a summand of the direct sum of relations. -/
theorem balanceMap_relationSumι_apply {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.piece i.1.1).val.obj X) (a : (A.piece i.1.2.1).val.obj X)
    (y : (N.piece i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (balanceMap P N n) X
        (PresheafOfModules.Hom.app (relationSumι P N i) X (x ⊗ₜ (a ⊗ₜ y))) =
      leftTerm P N i X x a y - rightTerm P N i X x a y := by
  refine (PresheafOfModules.hom_congr_apply' (relationSumι_balanceMap P N i) X
    (x ⊗ₜ (a ⊗ₜ y))).trans ?_
  exact balanceSummandMap_tmul P N i X x a y

end Cast

variable {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  (P : DifferentialGradedModule.{t, m, m} A) (N : LeftDifferentialGradedModule.{t, m, m} A)

/-- The summand index `(p + 1, q)` in degree `n + 1`. -/
abbrev tensorIndexShiftLeft {n : ℤ} (p : TensorIndex n) : TensorIndex (n + 1) :=
  ⟨(p.1.1 + 1, p.1.2), by change p.1.1 + 1 + p.1.2 = n + 1; have := p.2; omega⟩

/-- The summand index `(p, q + 1)` in degree `n + 1`. -/
abbrev tensorIndexShiftRight {n : ℤ} (p : TensorIndex n) : TensorIndex (n + 1) :=
  ⟨(p.1.1, p.1.2 + 1), by change p.1.1 + (p.1.2 + 1) = n + 1; have := p.2; omega⟩

/-- The relation index `(r + 1, s, t)` in degree `n + 1`. -/
abbrev relationIndexShift₁ {n : ℤ} (i : RelationIndex n) : RelationIndex (n + 1) :=
  ⟨(i.1.1 + 1, i.1.2.1, i.1.2.2), by
    change i.1.1 + 1 + i.1.2.1 + i.1.2.2 = n + 1
    have := i.2; omega⟩

/-- The relation index `(r, s + 1, t)` in degree `n + 1`. -/
abbrev relationIndexShift₂ {n : ℤ} (i : RelationIndex n) : RelationIndex (n + 1) :=
  ⟨(i.1.1, i.1.2.1 + 1, i.1.2.2), by
    change i.1.1 + (i.1.2.1 + 1) + i.1.2.2 = n + 1
    have := i.2; omega⟩

/-- The relation index `(r, s, t + 1)` in degree `n + 1`. -/
abbrev relationIndexShift₃ {n : ℤ} (i : RelationIndex n) : RelationIndex (n + 1) :=
  ⟨(i.1.1, i.1.2.1, i.1.2.2 + 1), by
    change i.1.1 + i.1.2.1 + (i.1.2.2 + 1) = n + 1
    have := i.2; omega⟩

/-- The underlying right graded module of `P`. -/
noncomputable abbrev gP : GradedModule.{t, m, m} A.toGradedAlgebra :=
  GradedModule.ofDifferentialGraded P

/-- The underlying left graded module of `N`. -/
noncomputable abbrev gN : LeftGradedModule.{t, m, m} A.toGradedAlgebra :=
  LeftGradedModule.ofDifferentialGraded N

/-- The right action of the underlying graded module of `P` is the multiplication of `P`. -/
@[simp]
theorem gP_smul (n i : ℤ) (U : Cᵒᵖ) : (gP P).smul n i U = (P.mul n i).app U := rfl

/-- The left action of the underlying graded module of `N` is the multiplication of `N`. -/
@[simp]
theorem gN_smul (i n : ℤ) (U : Cᵒᵖ) : (gN N).smul i n U = (N.mul i n).app U := rfl

/-- The signed differential on the summand `P^p ⊗_O N^q`, with values in the direct sum of
degree `n + 1`: it sends `x ⊗ y` to `dx ⊗ y + (-1)^p x ⊗ dy`. -/
noncomputable def dgTensorSummandDiff {n : ℤ} (p : TensorIndex n) :
    tensorSummand (gP P) (gN N) p ⟶ tensorSum (gP P) (gN N) (n + 1) :=
  PresheafOfModules.tensorSignedDiff (Int.negOnePow p.1.1 : ℤ)
    (P.complex.d p.1.1 (p.1.1 + 1)).val (N.complex.d p.1.2 (p.1.2 + 1)).val
    (tensorSumι (gP P) (gN N) (tensorIndexShiftLeft p))
    (tensorSumι (gP P) (gN N) (tensorIndexShiftRight p))

/-- The signed differential on the direct sum `⨁_{p + q = n} P^p ⊗_O N^q`. -/
noncomputable def dgTensorSumDiff (n : ℤ) :
    tensorSum (gP P) (gN N) n ⟶ tensorSum (gP P) (gN N) (n + 1) :=
  Sigma.desc fun p ↦ dgTensorSummandDiff P N p

/-- The signed differential on a summand sends `u ⊗ w` to `du ⊗ w + (-1)^p u ⊗ dw`. -/
theorem dgTensorSummandDiff_tmul {n : ℤ} (p : TensorIndex n) (X : Cᵒᵖ)
    (u : (P.complex.X p.1.1).val.obj X) (w : (N.complex.X p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (dgTensorSummandDiff P N p) X (u ⊗ₜ w) =
      PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) (tensorIndexShiftLeft p)) X
          ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u ⊗ₜ w) +
        (Int.negOnePow p.1.1 : ℤ) •
          PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) (tensorIndexShiftRight p)) X
            (u ⊗ₜ (N.complex.d p.1.2 (p.1.2 + 1)).val.app X w) :=
  PresheafOfModules.tensorSignedDiff_tmul _ _ _ _ _ X u w

/-- The signed differential on the direct sum restricts on each summand to the signed
differential of that summand. -/
theorem tensorSumι_dgTensorSumDiff {n : ℤ} (p : TensorIndex n) :
    tensorSumι (gP P) (gN N) p ≫ dgTensorSumDiff P N n = dgTensorSummandDiff P N p :=
  Sigma.ι_comp_desc _ _

/-- The signed differential on the direct sum, applied to the image of `u ⊗ w` under the
inclusion of a summand, is `du ⊗ w + (-1)^p u ⊗ dw`. -/
theorem dgTensorSumDiff_tensorSumι_apply {n : ℤ} (p : TensorIndex n) (X : Cᵒᵖ)
    (u : ((gP P).piece p.1.1).val.obj X) (w : ((gN N).piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (dgTensorSumDiff P N n) X
        (PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) p) X (u ⊗ₜ w)) =
      PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) (tensorIndexShiftLeft p)) X
          ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u ⊗ₜ w) +
        (Int.negOnePow p.1.1 : ℤ) •
          PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) (tensorIndexShiftRight p)) X
            (u ⊗ₜ (N.complex.d p.1.2 (p.1.2 + 1)).val.app X w) := by
  refine (PresheafOfModules.hom_congr_apply'
    (Sigma.ι_comp_desc (f := fun p : TensorIndex n ↦ tensorSummand (gP P) (gN N) p)
      (fun p ↦ dgTensorSummandDiff P N p) p) X (u ⊗ₜ w)).trans ?_
  exact PresheafOfModules.tensorSignedDiff_tmul _ _ _ _ _ X u w

/-- The signed differential on the summand `P^r ⊗_O A^s ⊗_O N^t` of the direct sum of relations,
with values in the direct sum of relations of degree `n + 1`. -/
noncomputable def relationSummandDiff {n : ℤ} (i : RelationIndex n) :
    relationSummand (gP P) (gN N) i ⟶ relationSum (gP P) (gN N) (n + 1) :=
  PresheafOfModules.tensorSignedDiff₃ (Int.negOnePow i.1.1 : ℤ)
    (Int.negOnePow (i.1.1 + i.1.2.1) : ℤ)
    (P.complex.d i.1.1 (i.1.1 + 1)).val (A.complex.d i.1.2.1 (i.1.2.1 + 1)).val
    (N.complex.d i.1.2.2 (i.1.2.2 + 1)).val
    (relationSumι (gP P) (gN N) (relationIndexShift₁ i))
    (relationSumι (gP P) (gN N) (relationIndexShift₂ i))
    (relationSumι (gP P) (gN N) (relationIndexShift₃ i))

/-- The signed differential on a summand of the direct sum of relations sends `x ⊗ a ⊗ y` to
`dx ⊗ a ⊗ y + (-1)^r x ⊗ da ⊗ y + (-1)^{r + s} x ⊗ a ⊗ dy`. -/
theorem relationSumDiff_relationSumι_apply_aux {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : ((gP P).piece i.1.1).val.obj X) (a : (A.complex.X i.1.2.1).val.obj X)
    (y : ((gN N).piece i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (relationSummandDiff P N i) X (x ⊗ₜ (a ⊗ₜ y)) =
      PresheafOfModules.Hom.app (relationSumι (gP P) (gN N) (relationIndexShift₁ i)) X
          ((P.complex.d i.1.1 (i.1.1 + 1)).val.app X x ⊗ₜ (a ⊗ₜ y)) +
        ((Int.negOnePow i.1.1 : ℤ) •
            PresheafOfModules.Hom.app
              (relationSumι (gP P) (gN N) (relationIndexShift₂ i)) X
              (x ⊗ₜ ((A.complex.d i.1.2.1 (i.1.2.1 + 1)).val.app X a ⊗ₜ y)) +
          (Int.negOnePow (i.1.1 + i.1.2.1) : ℤ) •
            PresheafOfModules.Hom.app
              (relationSumι (gP P) (gN N) (relationIndexShift₃ i)) X
              (x ⊗ₜ (a ⊗ₜ (N.complex.d i.1.2.2 (i.1.2.2 + 1)).val.app X y))) :=
  PresheafOfModules.tensorSignedDiff₃_tmul _ _ _ _ _ _ _ _ X x a y

/-- The signed differential on the direct sum of relations. -/
noncomputable def relationSumDiff (n : ℤ) :
    relationSum (gP P) (gN N) n ⟶ relationSum (gP P) (gN N) (n + 1) :=
  Sigma.desc fun i ↦ relationSummandDiff P N i

/-- The signed differential on the direct sum of relations restricts on each summand to the
signed differential of that summand. -/
theorem relationSumι_relationSumDiff {n : ℤ} (i : RelationIndex n) :
    relationSumι (gP P) (gN N) i ≫ relationSumDiff P N n = relationSummandDiff P N i :=
  Sigma.ι_comp_desc _ _

/-- The signed differential applied to the local section `xa ⊗ y`, expanded by the Leibniz rule
for the right action on `P`. -/
theorem dgTensorSumDiff_leftTerm {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.complex.X i.1.1).val.obj X) (a : (A.complex.X i.1.2.1).val.obj X)
    (y : (N.complex.X i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (dgTensorSumDiff P N n) X (leftTerm (gP P) (gN N) i X x a y) =
      (leftTerm (gP P) (gN N) (relationIndexShift₁ i) X
            ((P.complex.d i.1.1 (i.1.1 + 1)).val.app X x) a y +
          (Int.negOnePow i.1.1 : ℤ) • leftTerm (gP P) (gN N) (relationIndexShift₂ i) X x
            ((A.complex.d i.1.2.1 (i.1.2.1 + 1)).val.app X a) y) +
        (Int.negOnePow (i.1.1 + i.1.2.1) : ℤ) •
          leftTerm (gP P) (gN N) (relationIndexShift₃ i) X x a
            ((N.complex.d i.1.2.2 (i.1.2.2 + 1)).val.app X y) := by
  refine (dgTensorSumDiff_tensorSumι_apply P N (leftIndex i) X
    ((P.mul i.1.1 i.1.2.1).app X x a) y).trans ?_
  refine congrArg₂ (fun v w ↦ v + w) ?_ rfl
  refine (congrArg (fun v ↦ PresheafOfModules.Hom.app
      (tensorSumι (gP P) (gN N) (tensorIndexShiftLeft (leftIndex i))) X (v ⊗ₜ y))
    (P.leibniz i.1.1 i.1.2.1 X x a)).trans ?_
  refine (PresheafOfModules.app_tmul_add_left _ X _ _ y).trans ?_
  refine congrArg₂ (fun v w ↦ v + w)
    (tensorSumι_cast_left (gP P) (gN N) (add_right_comm i.1.1 1 i.1.2.1) _ X _ y) ?_
  refine (PresheafOfModules.app_tmul_zsmul_left _ X _ _ y).trans ?_
  exact congrArg (fun v ↦ (Int.negOnePow i.1.1 : ℤ) • v)
    (tensorSumι_cast_left (gP P) (gN N) (add_assoc i.1.1 i.1.2.1 1).symm _ X _ y)

/-- The signed differential applied to the local section `x ⊗ ay`, expanded by the Leibniz rule
for the left action on `N`. -/
theorem dgTensorSumDiff_rightTerm {n : ℤ} (i : RelationIndex n) (X : Cᵒᵖ)
    (x : (P.complex.X i.1.1).val.obj X) (a : (A.complex.X i.1.2.1).val.obj X)
    (y : (N.complex.X i.1.2.2).val.obj X) :
    PresheafOfModules.Hom.app (dgTensorSumDiff P N n) X (rightTerm (gP P) (gN N) i X x a y) =
      rightTerm (gP P) (gN N) (relationIndexShift₁ i) X
          ((P.complex.d i.1.1 (i.1.1 + 1)).val.app X x) a y +
        (Int.negOnePow i.1.1 : ℤ) •
          (rightTerm (gP P) (gN N) (relationIndexShift₂ i) X x
              ((A.complex.d i.1.2.1 (i.1.2.1 + 1)).val.app X a) y +
            (Int.negOnePow i.1.2.1 : ℤ) •
              rightTerm (gP P) (gN N) (relationIndexShift₃ i) X x a
                ((N.complex.d i.1.2.2 (i.1.2.2 + 1)).val.app X y)) := by
  refine (dgTensorSumDiff_tensorSumι_apply P N (rightIndex i) X x
    ((N.mul i.1.2.1 i.1.2.2).app X a y)).trans ?_
  refine congrArg₂ (fun v w ↦ v + w) rfl (congrArg (fun v ↦ (Int.negOnePow i.1.1 : ℤ) • v) ?_)
  refine (congrArg (fun v ↦ PresheafOfModules.Hom.app
      (tensorSumι (gP P) (gN N) (tensorIndexShiftRight (rightIndex i))) X (x ⊗ₜ v))
    (N.leibniz i.1.2.1 i.1.2.2 X a y)).trans ?_
  refine (PresheafOfModules.app_tmul_add_right _ X x _ _).trans ?_
  refine congrArg₂ (fun v w ↦ v + w)
    (tensorSumι_cast_right (gP P) (gN N) (add_right_comm i.1.2.1 1 i.1.2.2) _ X x _) ?_
  refine (PresheafOfModules.app_tmul_zsmul_right _ X _ x _).trans ?_
  exact congrArg (fun v ↦ (Int.negOnePow i.1.2.1 : ℤ) • v)
    (tensorSumι_cast_right (gP P) (gN N) (add_assoc i.1.2.1 i.1.2.2 1).symm _ X x _)

/-- The signed differential of the direct sums is compatible with the balance maps: this is the
two Leibniz rules, and it is what makes the differential descend to `P ⊗_A N`. -/
@[stacks 0FRM "the differential is well defined: it kills `xa ⊗ y - x ⊗ ay`"]
theorem dgTensorSumDiff_balance (n : ℤ) :
    balanceMap (gP P) (gN N) n ≫ dgTensorSumDiff P N n =
      relationSumDiff P N n ≫ balanceMap (gP P) (gN N) (n + 1) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, relationSumι_balanceMap, ← Category.assoc, relationSumι_relationSumDiff]
  refine PresheafOfModules.tensorObj₃_hom_ext fun X x a y ↦ ?_
  refine (PresheafOfModules.comp_app_apply (balanceSummandMap (gP P) (gN N) i)
    (dgTensorSumDiff P N n) X (x ⊗ₜ (a ⊗ₜ y))).trans ?_
  refine Eq.trans ?_ (PresheafOfModules.comp_app_apply (relationSummandDiff P N i)
    (balanceMap (gP P) (gN N) (n + 1)) X (x ⊗ₜ (a ⊗ₜ y))).symm
  rw [balanceSummandMap_tmul, relationSumDiff_relationSumι_apply_aux, map_sub, map_add, map_add,
    map_zsmul, map_zsmul]
  refine (congrArg₂ (fun v w ↦ v - w) (dgTensorSumDiff_leftTerm P N i X x a y)
    (dgTensorSumDiff_rightTerm P N i X x a y)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun v w ↦ v + w)
    (balanceMap_relationSumι_apply (gP P) (gN N) (relationIndexShift₁ i) X
      ((P.complex.d i.1.1 (i.1.1 + 1)).val.app X x) a y)
    (congrArg₂ (fun v w ↦ v + w)
      (congrArg (fun v ↦ (Int.negOnePow i.1.1 : ℤ) • v)
        (balanceMap_relationSumι_apply (gP P) (gN N) (relationIndexShift₂ i) X x
          ((A.complex.d i.1.2.1 (i.1.2.1 + 1)).val.app X a) y))
      (congrArg (fun v ↦ (Int.negOnePow (i.1.1 + i.1.2.1) : ℤ) • v)
        (balanceMap_relationSumι_apply (gP P) (gN N) (relationIndexShift₃ i) X x a
          ((N.complex.d i.1.2.2 (i.1.2.2 + 1)).val.app X y))))).symm
  simp only [Int.negOnePow_add, Units.val_mul, smul_smul, smul_sub, smul_add]
  abel

/-- The signed differential on the direct sums squares to zero: the two middle terms cancel
because the sign changes with the degree. -/
theorem dgTensorSumDiff_comp (n : ℤ) :
    dgTensorSumDiff P N n ≫ dgTensorSumDiff P N (n + 1) = 0 := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  rw [← Category.assoc, tensorSumι_dgTensorSumDiff, comp_zero]
  refine PresheafOfModules.tensorObj_hom_ext fun X u w ↦ ?_
  have hP : (P.complex.d (p.1.1 + 1) (p.1.1 + 1 + 1)).val.app X
      ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u) = 0 :=
    congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app X u)
      (P.complex.d_comp_d p.1.1 (p.1.1 + 1) (p.1.1 + 1 + 1))
  have hN : (N.complex.d (p.1.2 + 1) (p.1.2 + 1 + 1)).val.app X
      ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X w) = 0 :=
    congrArg (fun φ ↦ (SheafOfModules.Hom.val φ).app X w)
      (N.complex.d_comp_d p.1.2 (p.1.2 + 1) (p.1.2 + 1 + 1))
  have z1 : PresheafOfModules.Hom.app
      (tensorSumι (gP P) (gN N) (tensorIndexShiftLeft (tensorIndexShiftLeft p))) X
      ((P.complex.d (p.1.1 + 1) (p.1.1 + 1 + 1)).val.app X
        ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u) ⊗ₜ w) = 0 :=
    (congrArg (fun v ↦ PresheafOfModules.Hom.app
      (tensorSumι (gP P) (gN N) (tensorIndexShiftLeft (tensorIndexShiftLeft p))) X
        (v ⊗ₜ w)) hP).trans (PresheafOfModules.app_tmul_zero_left _ X w)
  have z2 : PresheafOfModules.Hom.app
      (tensorSumι (gP P) (gN N) (tensorIndexShiftRight (tensorIndexShiftRight p))) X
      (u ⊗ₜ (N.complex.d (p.1.2 + 1) (p.1.2 + 1 + 1)).val.app X
        ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X w)) = 0 :=
    (congrArg (fun v ↦ PresheafOfModules.Hom.app
      (tensorSumι (gP P) (gN N) (tensorIndexShiftRight (tensorIndexShiftRight p))) X
        (u ⊗ₜ v)) hN).trans (PresheafOfModules.app_tmul_zero_right _ X u)
  have hzero : PresheafOfModules.Hom.app
      (0 : tensorSummand (gP P) (gN N) p ⟶ tensorSum (gP P) (gN N) (n + 1 + 1)) X
        (u ⊗ₜ w) = 0 := by
    simp only [PresheafOfModules.zero_app]
    rfl
  rw [hzero]
  refine (PresheafOfModules.comp_app_apply (dgTensorSummandDiff P N p)
    (dgTensorSumDiff P N (n + 1)) X (u ⊗ₜ w)).trans ?_
  refine (congrArg (fun v ↦ PresheafOfModules.Hom.app (dgTensorSumDiff P N (n + 1)) X v)
    (dgTensorSummandDiff_tmul P N p X u w)).trans ?_
  rw [map_add, map_zsmul,
    dgTensorSumDiff_tensorSumι_apply P N (tensorIndexShiftLeft p) X
      ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u) w,
    dgTensorSumDiff_tensorSumι_apply P N (tensorIndexShiftRight p) X u
      ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X w),
    z1, z2]
  dsimp only [tensorIndexShiftLeft, tensorIndexShiftRight]
  rw [Int.negOnePow_succ, Units.val_neg, neg_smul]
  simp only [smul_zero, zero_add, add_zero]
  abel

/-- The differential of degree `n` of the relative tensor product `P ⊗_A N`, as a morphism of
presheaves of modules: the descent of the signed differential to the cokernel of the balance
map. -/
@[stacks 0FRM "the differential `d (x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy`"]
noncomputable def dgTensorDiffPre (n : ℤ) :
    gradedTensorPre (gP P) (gN N) n ⟶ gradedTensorPre (gP P) (gN N) (n + 1) :=
  cokernel.desc (balanceMap (gP P) (gN N) n)
    (dgTensorSumDiff P N n ≫ gradedTensorπ (gP P) (gN N) (n + 1)) (by
      rw [← Category.assoc, dgTensorSumDiff_balance, Category.assoc, cokernel.condition,
        comp_zero])

/-- The differential of the relative tensor product squares to zero. -/
theorem dgTensorDiffPre_comp (n : ℤ) :
    dgTensorDiffPre P N n ≫ dgTensorDiffPre P N (n + 1) = 0 := by
  refine (cancel_epi (gradedTensorπ (gP P) (gN N) n)).mp ?_
  rw [← Category.assoc, dgTensorDiffPre, cokernel.π_desc, Category.assoc, dgTensorDiffPre,
    cokernel.π_desc, ← Category.assoc, dgTensorSumDiff_comp, zero_comp, comp_zero]

/-- The relative tensor product `P ⊗_A N` as a cochain complex of presheaves of modules. -/
noncomputable def dgTensorPre :
    CochainComplex (PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) ℤ :=
  CochainComplex.of (fun n ↦ gradedTensorPre (gP P) (gN N) n) (dgTensorDiffPre P N)
    (dgTensorDiffPre_comp P N)

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- Module sheafification is additive: it is a left adjoint, hence preserves binary coproducts,
which in a preadditive category with binary biproducts forces additivity. -/
instance sheafification_additive :
    (PresheafOfModules.sheafification (R := toRingCat J Osharp)
      (𝟙 (toRingCat J Osharp).obj)).Additive :=
  have : PreservesBinaryBiproducts (PresheafOfModules.sheafification
      (R := toRingCat J Osharp) (𝟙 (toRingCat J Osharp).obj)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The relative tensor product `P ⊗_A N` of a right differential graded `A`-module with a left
differential graded `A`-module, as a cochain complex of sheaves of modules. -/
@[stacks 0FRM "the relative tensor product as a complex of `O`-modules"]
noncomputable def dgTensor : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ :=
  ((PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (dgTensorPre P N)

/-- The term of degree `n` of `P ⊗_A N` is the relative tensor product of the underlying graded
modules in degree `n`. -/
@[simp]
theorem dgTensor_X (n : ℤ) : (dgTensor P N).X n = gradedTensor (gP P) (gN N) n := rfl

end Sheafify

section KFlat

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- Condition (2) in the definition of a good differential graded module: `P` is K-flat, that
is, `P ⊗_A N` is acyclic for every acyclic left differential graded `A`-module `N`. -/
def IsKFlat (P : DifferentialGradedModule.{t, m, m} A) : Prop :=
  ∀ N : LeftDifferentialGradedModule.{t, m, m} A,
    N.complex.Acyclic → (dgTensor P N).Acyclic

end KFlat

end RelativeTensor

namespace RelativeTensor

variable {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}
  {P P' P'' : DifferentialGradedModule.{t, m, m} A}
  (N : LeftDifferentialGradedModule.{t, m, m} A)

/-- The homomorphism of underlying right graded modules of a morphism of right differential
graded modules. -/
noncomputable abbrev gMap (h : P ⟶ P') : gP P ⟶ gP P' :=
  GradedModule.ofDifferentialGradedMap h

/-- The differential of the relative tensor product is induced by the signed differential on the
direct sum. -/
theorem gradedTensorπ_dgTensorDiffPre (n : ℤ) :
    gradedTensorπ (gP P) (gN N) n ≫ dgTensorDiffPre P N n =
      dgTensorSumDiff P N n ≫ gradedTensorπ (gP P) (gN N) (n + 1) :=
  cokernel.π_desc _ _ _

/-- The signed differential on the direct sums is compatible with a morphism of right
differential graded modules: this is the Leibniz rule for the morphism, which commutes with the
differentials. -/
theorem tensorSumMapRight_dgTensorSumDiff (h : P ⟶ P') (n : ℤ) :
    tensorSumMapRight (gMap h) (gN N) n ≫ dgTensorSumDiff P' N n =
      dgTensorSumDiff P N n ≫ tensorSumMapRight (gMap h) (gN N) (n + 1) := by
  refine Sigma.hom_ext _ _ fun p ↦ ?_
  refine PresheafOfModules.tensorObj_hom_ext fun X u w ↦ ?_
  have hd : PresheafOfModules.Hom.app ((gMap h).app (p.1.1 + 1)).val X
        ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u) =
      (P'.complex.d p.1.1 (p.1.1 + 1)).val.app X
        (PresheafOfModules.Hom.app ((gMap h).app p.1.1).val X u) :=
    (congrArg (fun φ : P.complex.X p.1.1 ⟶ P'.complex.X (p.1.1 + 1) ↦
      (SheafOfModules.Hom.val φ).app X u)
        (h.toHomologicalComplex.comm p.1.1 (p.1.1 + 1))).symm
  have hLHS : PresheafOfModules.Hom.app (dgTensorSumDiff P' N n) X
        (PresheafOfModules.Hom.app (tensorSumMapRight (gMap h) (gN N) n) X
          (PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) p) X (u ⊗ₜ w))) =
      PresheafOfModules.Hom.app
            (tensorSumι (gP P') (gN N) (tensorIndexShiftLeft p)) X
            ((P'.complex.d p.1.1 (p.1.1 + 1)).val.app X
              (PresheafOfModules.Hom.app ((gMap h).app p.1.1).val X u) ⊗ₜ w) +
        (Int.negOnePow p.1.1 : ℤ) •
          PresheafOfModules.Hom.app
            (tensorSumι (gP P') (gN N) (tensorIndexShiftRight p)) X
            (PresheafOfModules.Hom.app ((gMap h).app p.1.1).val X u ⊗ₜ
              (N.complex.d p.1.2 (p.1.2 + 1)).val.app X w) :=
    (congrArg (fun v ↦ PresheafOfModules.Hom.app (dgTensorSumDiff P' N n) X v)
      (tensorSumMapRight_tensorSumι_apply (gMap h) (gN N) p X u w)).trans
        (dgTensorSumDiff_tensorSumι_apply P' N p X _ w)
  have hRHS : PresheafOfModules.Hom.app (tensorSumMapRight (gMap h) (gN N) (n + 1)) X
        (PresheafOfModules.Hom.app (dgTensorSumDiff P N n) X
          (PresheafOfModules.Hom.app (tensorSumι (gP P) (gN N) p) X (u ⊗ₜ w))) =
      PresheafOfModules.Hom.app
            (tensorSumι (gP P') (gN N) (tensorIndexShiftLeft p)) X
            (PresheafOfModules.Hom.app ((gMap h).app (p.1.1 + 1)).val X
              ((P.complex.d p.1.1 (p.1.1 + 1)).val.app X u) ⊗ₜ w) +
        (Int.negOnePow p.1.1 : ℤ) •
          PresheafOfModules.Hom.app
            (tensorSumι (gP P') (gN N) (tensorIndexShiftRight p)) X
            (PresheafOfModules.Hom.app ((gMap h).app p.1.1).val X u ⊗ₜ
              (N.complex.d p.1.2 (p.1.2 + 1)).val.app X w) := by
    refine (congrArg (fun v ↦ PresheafOfModules.Hom.app
      (tensorSumMapRight (gMap h) (gN N) (n + 1)) X v)
        (dgTensorSumDiff_tensorSumι_apply P N p X u w)).trans ?_
    refine (map_add _ _ _).trans ?_
    refine congrArg₂ (fun v v' ↦ v + v')
      (tensorSumMapRight_tensorSumι_apply (gMap h) (gN N) (tensorIndexShiftLeft p) X _ w) ?_
    refine (map_zsmul _ _ _).trans ?_
    exact congrArg (fun v ↦ (Int.negOnePow p.1.1 : ℤ) • v)
      (tensorSumMapRight_tensorSumι_apply (gMap h) (gN N) (tensorIndexShiftRight p) X u _)
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  exact congrArg₂ (fun v v' ↦ v + v')
    (congrArg (fun z ↦ PresheafOfModules.Hom.app
      (tensorSumι (gP P') (gN N) (tensorIndexShiftLeft p)) X (z ⊗ₜ w)) hd.symm) rfl

/-- The induced map of relative tensor products commutes with the differentials. -/
theorem gradedTensorMapPreRight_dgTensorDiffPre (h : P ⟶ P') (n : ℤ) :
    gradedTensorMapPreRight (gMap h) (gN N) n ≫ dgTensorDiffPre P' N n =
      dgTensorDiffPre P N n ≫ gradedTensorMapPreRight (gMap h) (gN N) (n + 1) := by
  refine (cancel_epi (gradedTensorπ (gP P) (gN N) n)).mp ?_
  have e₁ : gradedTensorπ (gP P) (gN N) n ≫
        (gradedTensorMapPreRight (gMap h) (gN N) n ≫ dgTensorDiffPre P' N n) =
      (tensorSumMapRight (gMap h) (gN N) n ≫ dgTensorSumDiff P' N n) ≫
        gradedTensorπ (gP P') (gN N) (n + 1) := by
    rw [← Category.assoc, gradedTensorπ_gradedTensorMapPreRight, Category.assoc,
      gradedTensorπ_dgTensorDiffPre, ← Category.assoc]
  have e₂ : gradedTensorπ (gP P) (gN N) n ≫
        (dgTensorDiffPre P N n ≫ gradedTensorMapPreRight (gMap h) (gN N) (n + 1)) =
      (dgTensorSumDiff P N n ≫ tensorSumMapRight (gMap h) (gN N) (n + 1)) ≫
        gradedTensorπ (gP P') (gN N) (n + 1) := by
    rw [← Category.assoc, gradedTensorπ_dgTensorDiffPre, Category.assoc,
      gradedTensorπ_gradedTensorMapPreRight, ← Category.assoc]
  rw [e₁, e₂, tensorSumMapRight_dgTensorSumDiff]

/-- The map `P ⊗_A N ⟶ P' ⊗_A N` of cochain complexes of presheaves of modules induced by a
morphism of right differential graded modules. -/
noncomputable def dgTensorPreMap (h : P ⟶ P') : dgTensorPre P N ⟶ dgTensorPre P' N :=
  CochainComplex.ofHom (fun n ↦ gradedTensorMapPreRight (gMap h) (gN N) n) fun n ↦ by
    have e : ∀ (Q : DifferentialGradedModule.{t, m, m} A) (i : ℤ),
        (dgTensorPre Q N).d i (i + 1) = dgTensorDiffPre Q N i := fun Q i ↦
      CochainComplex.of_d _ _ i
    rw [e, e]
    exact gradedTensorMapPreRight_dgTensorDiffPre N h n

/-- In each degree, the map of relative tensor products induced by a morphism of right
differential graded modules is the map induced by the underlying graded morphism. -/
@[simp]
theorem dgTensorPreMap_f (h : P ⟶ P') (n : ℤ) :
    (dgTensorPreMap N h).f n = gradedTensorMapPreRight (gMap h) (gN N) n := rfl

/-- The identity morphism induces the identity of the relative tensor product. -/
theorem dgTensorPreMap_id (Q : DifferentialGradedModule.{t, m, m} A) :
    dgTensorPreMap N (𝟙 Q) = 𝟙 (dgTensorPre Q N) := by
  ext n
  rw [dgTensorPreMap_f, gMap, GradedModule.ofDifferentialGradedMap_id,
    gradedTensorMapPreRight_id]
  rfl

/-- The map of relative tensor products induced by a composite is the composite of the induced
maps. -/
theorem dgTensorPreMap_comp (h : P ⟶ P') (h' : P' ⟶ P'') :
    dgTensorPreMap N (h ≫ h') = dgTensorPreMap N h ≫ dgTensorPreMap N h' := by
  ext n
  rw [dgTensorPreMap_f, gMap, GradedModule.ofDifferentialGradedMap_comp,
    gradedTensorMapPreRight_comp]
  rfl

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- Module sheafification applied degreewise to a cochain complex of presheaves of modules. -/
noncomputable abbrev sheafifyComplex :
    CochainComplex (PresheafOfModules.{m} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) ℤ ⥤
      CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ :=
  (PresheafOfModules.sheafification (R := toRingCat J Osharp)
    (𝟙 (toRingCat J Osharp).obj)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The functor `- ⊗_A N` from right differential graded `A`-modules to complexes of
`O`-modules, for a fixed left differential graded `A`-module `N`. -/
@[stacks 0FRM "the functor `- ⊗_A N` to complexes of `O`-modules"]
noncomputable def dgTensorFunctor :
    DifferentialGradedModule.{t, m, m} A ⥤
      CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ where
  obj Q := dgTensor Q N
  map h := sheafifyComplex.map (dgTensorPreMap N h)
  map_id Q := by rw [dgTensorPreMap_id]; exact sheafifyComplex.map_id _
  map_comp h h' := by rw [dgTensorPreMap_comp]; exact sheafifyComplex.map_comp _ _

/-- In each degree, the functor `- ⊗_A N` sends a morphism of right differential graded modules
to the map of relative tensor products induced by the underlying graded morphism. -/
@[simp]
theorem dgTensorFunctor_map_f (h : P ⟶ P') (n : ℤ) :
    ((dgTensorFunctor N).map h).f n = gradedTensorMapRight (gMap h) (gN N) n := rfl

end Sheafify

end RelativeTensor

end SheafOfModules
