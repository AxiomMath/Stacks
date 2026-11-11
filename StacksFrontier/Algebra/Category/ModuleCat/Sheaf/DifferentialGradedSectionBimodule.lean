module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleComposition

/-!
# The differential graded bimodule of sections of a sheaf of differential graded bimodules

Let `A` and `B` be sheaves of differential graded algebras on a site, let `N` be a differential
graded `(A, B)`-bimodule and let `U` be an object of the site. Section
[Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP) observes that the sections
`N(U) = ⨁ n, N^n(U)` form a differential graded `(A(U), B(U))`-bimodule. The right
`B(U)`-module is `SheafOfModules.DifferentialGradedModule.sectionModule` of the underlying right
module; this file constructs the left `A(U)`-action, `a x` on summands being the left action of
`N` read on sections, and checks that it is a left differential graded action by right
`B(U)`-linear maps.

## Main definitions

* `SheafOfModules.DifferentialGradedBimodule.sectionLeftAct`: the left action of `A(U)` on
  `N(U)`, as an additive map in each variable.
* `SheafOfModules.DifferentialGradedBimodule.sectionLeftMulHom`: left multiplication by a
  homogeneous element of `A(U)`, as a homogeneous right `B(U)`-linear map of `N(U)`.
* `SheafOfModules.DifferentialGradedBimodule.sectionBimodule`: **the differential graded
  `(A(U), B(U))`-bimodule `N(U)`.**

## Main results

* `SheafOfModules.DifferentialGradedBimodule.sectionLeftMulHom_one`, `sectionLeftMulHom_mul`
  and `sectionLeftMulHom_d`: the unit acts as the identity, products act as composites, and the
  differential of `A(U)` acts by the differential of the hom complex; these are the unit law, the
  associativity and the left Leibniz rule of `N`, read on sections.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum CochainComplex.HomComplex

universe t a v u

namespace SheafOfModules.DifferentialGradedBimodule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} (N : DifferentialGradedBimodule.{t, a, a} A B)
  (U : Cᵒᵖ)

/-- The left action of a homogeneous section of `A` on the sections of `N`. -/
def sectionLeftActOn (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) :
    N.toRightModule.totalSections U →+ N.toRightModule.totalSections U :=
  DirectSum.toAddMonoid fun p ↦
    (DirectSum.of (N.toRightModule.sectionsPiece U) (n + p)).comp ((N.leftMul n p).app U x)

/-- A homogeneous section `x` of `A` acting on a homogeneous section `y` of `N` is the summand
given by the left action of `N`. -/
theorem sectionLeftActOn_of (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) (p : ℤ)
    (y : N.toRightModule.sectionsPiece U p) :
    N.sectionLeftActOn U n x (DirectSum.of (N.toRightModule.sectionsPiece U) p y) =
      DirectSum.of (N.toRightModule.sectionsPiece U) (n + p) ((N.leftMul n p).app U x y) :=
  DirectSum.toAddMonoid_of _ p y

/-- The left action of a homogeneous section, additive in that section. -/
def sectionLeftActOnHom (n : ℤ) :
    A.toGradedAlgebra.sectionsPiece U n →+
      (N.toRightModule.totalSections U →+ N.toRightModule.totalSections U) :=
  AddMonoidHom.mk' (N.sectionLeftActOn U n) fun x x' ↦
    DirectSum.addHom_ext fun p y ↦ by
      rw [AddMonoidHom.add_apply, sectionLeftActOn_of, sectionLeftActOn_of, sectionLeftActOn_of,
        Stacks.BilinearMap.map_add_left (N.leftMul n p) U x x' y, map_add]

/-- **The left action of the section algebra `A(U)` on the sections of `N` over `U`**, as an
additive map in each variable. -/
def sectionLeftAct :
    A.toGradedAlgebra.totalSections U →+
      (N.toRightModule.totalSections U →+ N.toRightModule.totalSections U) :=
  DirectSum.toAddMonoid (N.sectionLeftActOnHom U)

/-- On homogeneous sections, the left action is the left action of `N`. -/
theorem sectionLeftAct_of_of (n : ℤ) (x : A.toGradedAlgebra.sectionsPiece U n) (p : ℤ)
    (y : N.toRightModule.sectionsPiece U p) :
    N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n x)
        (DirectSum.of (N.toRightModule.sectionsPiece U) p y) =
      DirectSum.of (N.toRightModule.sectionsPiece U) (n + p) ((N.leftMul n p).app U x y) := by
  rw [sectionLeftAct, DirectSum.toAddMonoid_of]
  exact N.sectionLeftActOn_of U n x p y

/-- A homogeneous section of degree `n` of `A` raises the degree of the sections of `N` by `n`. -/
theorem sectionLeftAct_mem {n : ℤ} (b : A.toGradedAlgebra.sectionsPiece U n) (i : ℤ)
    (x : N.toRightModule.sectionsPiece U i) :
    N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n b)
        (DirectSum.of (N.toRightModule.sectionsPiece U) i x) ∈
      Stacks.ExternalGrading.intSummand (N.toRightModule.sectionsPiece U) (i + n) := by
  rw [sectionLeftAct_of_of, ← of_gradedCast (add_comm n i)]
  exact Stacks.ExternalGrading.of_mem_intSummand _ (i + n) _

/-- **The left action commutes with the right action**: `a (x c) = (a x) c`. -/
theorem sectionLeftAct_act {n : ℤ} (b : A.toGradedAlgebra.sectionsPiece U n)
    (x : N.toRightModule.totalSections U) (c : B.toGradedAlgebra.totalSections U) :
    N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n b)
        (N.toRightModule.act U x c) =
      N.toRightModule.act U
        (N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n b) x) c := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | of p y =>
      induction c using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add c c' hc hc' => simp only [map_add, hc, hc']
      | of q z =>
          rw [DifferentialGradedModule.act_of, DifferentialGradedModule.actOn_of,
            sectionLeftAct_of_of, sectionLeftAct_of_of, DifferentialGradedModule.act_of,
            DifferentialGradedModule.actOn_of]
          exact of_heq (add_assoc n p q).symm (N.left_right_assoc n p q U b y z).symm

/-- **The unit acts as the identity.** -/
theorem sectionLeftAct_one (x : N.toRightModule.totalSections U) :
    N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (A.one.eval U)) x =
      x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]
  | add x y hx hy => rw [map_add, hx, hy]
  | of p y =>
      rw [sectionLeftAct_of_of]
      exact of_heq (zero_add p) (N.one_left p U y)

/-- **The left action is associative.** -/
theorem sectionLeftAct_mul {n m : ℤ} (b : A.toGradedAlgebra.sectionsPiece U n)
    (c : A.toGradedAlgebra.sectionsPiece U m) (x : N.toRightModule.totalSections U) :
    N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) (n + m)
        ((A.toGradedAlgebra.mul n m).app U b c)) x =
      N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n b)
        (N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) m c) x) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | of p y =>
      rw [sectionLeftAct_of_of, sectionLeftAct_of_of, sectionLeftAct_of_of]
      exact of_heq (add_assoc n m p) (N.left_assoc n m p U b c y).symm

/-- **The left Leibniz rule on sections**: `(d a) x = d (a x) - (-1)^n a (d x)`. -/
theorem sectionLeftAct_d {n : ℤ} (b : A.toGradedAlgebra.sectionsPiece U n)
    (x : N.toRightModule.totalSections U) :
    N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) (n + 1)
        ((A.complex.d n (n + 1)).val.app U b)) x =
      N.toRightModule.sectionD U
          (N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n b) x) -
        (n.negOnePow : ℤ) •
          N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n b)
            (N.toRightModule.sectionD U x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero, sub_zero]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]; abel
  | of p y =>
      rw [sectionLeftAct_of_of, sectionLeftAct_of_of, DifferentialGradedModule.sectionD_of,
        DifferentialGradedModule.sectionD_of, sectionLeftAct_of_of,
        DifferentialGradedModule.sectionDApp_apply, DifferentialGradedModule.sectionDApp_apply]
      change _ = DirectSum.of (N.toRightModule.sectionsPiece U) (n + p + 1)
          ((N.complex.d (n + p) (n + p + 1)).val.app U ((N.leftMul n p).app U b y)) - _
      rw [N.leibniz_left n p U b y, map_add, of_gradedCast, map_zsmul, of_gradedCast]
      abel

/-- Left multiplication by an element of the degree-`n` summand of `A(U)`, as a homogeneous right
`B(U)`-linear map of degree `n` of `N(U)`. -/
def sectionLeftMulHom {n : ℤ} (b : (A.sectionAlgebra U).grading n) :
    _root_.DifferentialGradedModule.HomogeneousMap (B.sectionAlgebra U)
      (N.toRightModule.sectionModule U) (N.toRightModule.sectionModule U) n :=
  ⟨DifferentialGradedModule.uliftIntLinear (N.sectionLeftAct U b.1), by
    obtain ⟨_, b', rfl⟩ := b
    refine ⟨fun i x hx => ?_, fun c x => ?_⟩
    · obtain ⟨x', rfl⟩ := hx
      exact N.sectionLeftAct_mem U b' i x'
    · exact N.sectionLeftAct_act U b' x c⟩

/-- The underlying map of `sectionLeftMulHom b` is the left action of `b`. -/
theorem sectionLeftMulHom_apply {n : ℤ} (b : (A.sectionAlgebra U).grading n)
    (x : N.toRightModule.totalSections U) :
    (N.sectionLeftMulHom U b).1 x = N.sectionLeftAct U b.1 x :=
  rfl

/-- Left multiplication is additive in the multiplier. -/
theorem sectionLeftMulHom_add {n : ℤ} (b b' : (A.sectionAlgebra U).grading n) :
    N.sectionLeftMulHom U (b + b') = N.sectionLeftMulHom U b + N.sectionLeftMulHom U b' :=
  Subtype.ext (LinearMap.ext fun x =>
    DFunLike.congr_fun (map_add (N.sectionLeftAct U) b.1 b'.1) x)

/-- Left multiplication is linear in the multiplier over the lifted integers. -/
theorem sectionLeftMulHom_smul {n : ℤ} (r : ULift.{a, 0} ℤ) (b : (A.sectionAlgebra U).grading n) :
    N.sectionLeftMulHom U (r • b) = r • N.sectionLeftMulHom U b :=
  Subtype.ext (LinearMap.ext fun x =>
    DFunLike.congr_fun (map_zsmul (N.sectionLeftAct U) r.down b.1) x)

/-- **The unit of `A(U)` acts as the identity**: the unit law of the left action of `N`, read on
sections. -/
theorem sectionLeftMulHom_one :
    N.sectionLeftMulHom U
        (⟨1, SetLike.one_mem_graded (A.sectionAlgebra U).grading⟩ :
          (A.sectionAlgebra U).grading 0) =
      (_root_.DifferentialGradedModule.dgCategory (B.sectionAlgebra U)).id
        (N.toRightModule.sectionModule U) := by
  have h1 : (1 : A.toGradedAlgebra.totalSections U) =
      DirectSum.of (A.toGradedAlgebra.sectionsPiece U) 0 (A.one.eval U) :=
    (DirectSum.of_zero_one (A.toGradedAlgebra.sectionsPiece U)).symm
  exact Subtype.ext (LinearMap.ext fun x =>
    (congrArg (fun a => N.sectionLeftAct U a x) h1).trans (N.sectionLeftAct_one U x))

/-- **A product of homogeneous elements of `A(U)` acts as the composite of their actions**: the
associativity of the left action of `N`, read on sections. -/
theorem sectionLeftMulHom_mul {n m : ℤ} (b : (A.sectionAlgebra U).grading n)
    (c : (A.sectionAlgebra U).grading m) :
    N.sectionLeftMulHom U
        (⟨b.1 * c.1, SetLike.mul_mem_graded b.property c.property⟩ :
          (A.sectionAlgebra U).grading (n + m)) =
      (_root_.DifferentialGradedModule.dgCategory (B.sectionAlgebra U)).comp
        (rfl : n + m = n + m) (N.sectionLeftMulHom U b) (N.sectionLeftMulHom U c) := by
  obtain ⟨_, b', rfl⟩ := b
  obtain ⟨_, c', rfl⟩ := c
  exact Subtype.ext (LinearMap.ext fun x =>
    (congrArg (fun a => N.sectionLeftAct U a x)
      (GradedAlgebra.of_mul_of_eq A.toGradedAlgebra U n m b' c')).trans
      (N.sectionLeftAct_mul U b' c' x))

/-- **The differential of `A(U)` acts by the differential of the hom complex**: the left Leibniz
rule of `N`, read on sections. -/
theorem sectionLeftMulHom_d {n : ℤ} (b : (A.sectionAlgebra U).grading n) :
    N.sectionLeftMulHom U
        (⟨(A.sectionAlgebra U).d b, (A.sectionAlgebra U).d_mem n b b.property⟩ :
          (A.sectionAlgebra U).grading (n + 1)) =
      (_root_.DifferentialGradedModule.dgCategory (B.sectionAlgebra U)).d
        (N.sectionLeftMulHom U b) := by
  obtain ⟨_, b', rfl⟩ := b
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  have hs : ∀ y : (N.toRightModule.sectionModule U).M,
      DifferentialGraded.gradedSign (ULift.{a, 0} ℤ) n • y = (n.negOnePow : ℤ) • y := fun y => by
    rw [← DifferentialGraded.intCast_negOnePow, Int.cast_smul_eq_zsmul]
  refine ((congrArg (fun a => N.sectionLeftAct U a x)
    (DifferentialGradedAlgebra.sectionAlgebra_d_of A U n b')).trans
    (N.sectionLeftAct_d U b' x)).trans ?_
  exact congrArg (fun z => N.toRightModule.sectionD U
    (N.sectionLeftAct U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) n b') x) - z)
    (hs _).symm

/-- **The left differential graded action of `A(U)` on the sections of `N` over `U`**, a
homogeneous element acting by left multiplication. -/
def sectionLeftAction :
    (A.sectionAlgebra U).LeftAction (N.toRightModule.sectionModule U).toCochainComplex where
  action n :=
    { toFun := fun b => _root_.DifferentialGradedModule.homogeneousMapCochain (B.sectionAlgebra U)
        (N.toRightModule.sectionModule U) n (N.sectionLeftMulHom U b)
      map_add' := fun b b' =>
        (congrArg (_root_.DifferentialGradedModule.homogeneousMapCochain (B.sectionAlgebra U)
          (N.toRightModule.sectionModule U) n) (N.sectionLeftMulHom_add U b b')).trans
          (_root_.DifferentialGradedModule.homogeneousMapCochain_add _ _ n _ _)
      map_smul' := fun r b =>
        (congrArg (_root_.DifferentialGradedModule.homogeneousMapCochain (B.sectionAlgebra U)
          (N.toRightModule.sectionModule U) n) (N.sectionLeftMulHom_smul U r b)).trans
          (_root_.DifferentialGradedModule.homogeneousMapCochain_smul _ _ n r _) }
  map_one :=
    (congrArg (_root_.DifferentialGradedModule.homogeneousMapCochain (B.sectionAlgebra U)
      (N.toRightModule.sectionModule U) 0) (N.sectionLeftMulHom_one U)).trans
      (_root_.DifferentialGradedModule.homogeneousMapCochain_id _ _)
  map_mul n m b c :=
    (congrArg (_root_.DifferentialGradedModule.homogeneousMapCochain (B.sectionAlgebra U)
      (N.toRightModule.sectionModule U) (n + m)) (N.sectionLeftMulHom_mul U b c)).trans
      (_root_.DifferentialGradedModule.homogeneousMapCochain_comp _ _ rfl _ _)
  map_d n b :=
    (congrArg (_root_.DifferentialGradedModule.homogeneousMapCochain (B.sectionAlgebra U)
      (N.toRightModule.sectionModule U) (n + 1)) (N.sectionLeftMulHom_d U b)).trans
      (_root_.DifferentialGradedModule.homogeneousMapCochain_differential _ _ n _)

/-- **The sections `N(U) = ⨁ n, N^n(U)` of a differential graded `(A, B)`-bimodule `N` over `U`
form a differential graded `(A(U), B(U))`-bimodule**: the right `B(U)`-module of sections of the
underlying right module, with the left action of `A(U)` read on sections, which is by right
`B(U)`-linear maps. -/
@[stacks 0FRP "N(U) = ⊕ N^n(U) is a differential graded (A(U), B(U))-bimodule"]
def sectionBimodule : DifferentialGraded.Bimodule (A.sectionAlgebra U) (B.sectionAlgebra U) where
  rightModule := N.toRightModule.sectionModule U
  leftAction := ⟨N.sectionLeftAction U, fun n b =>
    ⟨N.sectionLeftMulHom U b, fun p x =>
      _root_.DifferentialGradedModule.homogeneousMapCochain_v' (B.sectionAlgebra U)
        (N.toRightModule.sectionModule U) n (N.sectionLeftMulHom U b) p (p + n) rfl x⟩⟩

end SheafOfModules.DifferentialGradedBimodule
