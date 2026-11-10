module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleAdmissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap

/-! # Tensoring a graded homomorphism of bimodules

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`, let
`s : N ⟶ N'` be a homomorphism of *graded* differential graded `(A, B)`-bimodules — a degree-zero
map of the underlying graded right `B`-modules commuting with the left `A`-action, not required to
commute with the differentials — and let `M` be a right differential graded `A`-module. Then `s`
induces a degree-zero map `M ⊗_A N ⟶ M ⊗_A N'` of graded right differential graded `B`-modules,
sending `x ⊗ y` to `x ⊗ s y`.

The universal property of Tag 09LM produces *homomorphisms* out of `M ⊗_A N`, which must commute
with the differentials, so it cannot be applied to `(x, y) ↦ x ⊗ s y`: that bilinear map fails the
graded Leibniz rule precisely because `s` does. What produces the map instead is the all-degrees
form of Tag 09LN, `DifferentialGraded.Bimodule.exists_tensorHomComplexIso`, in degree zero: the
degree-zero homogeneous maps `M ⊗_A N ⟶ M ⊗_A N'` are the degree-zero homogeneous maps
`M ⟶ Hom^•_B(N, M ⊗_A N')`, and `x ↦ (y ↦ x ⊗ s y)` is one of those — it is right `B`-linear in
`y` because the pure tensors are and `s` is, and right `A`-linear in `x` because the pure tensors
are balanced and `s` commutes with the left action.

This is what lets an admissible short exact sequence of bimodules be tensored: its splittings are
graded homomorphisms of bimodules and nothing weaker.

## Main definitions

* `DifferentialGraded.Bimodule.gradedPairHom`: the homogeneous map `y ↦ x ⊗ s y` attached to a
  homogeneous element of `M`.
* `DifferentialGraded.Bimodule.tensorGradedCurry`: the degree-zero homogeneous map
  `M ⟶ Hom^•_B(N, M ⊗_A N')` it assembles to.
* `DifferentialGraded.Bimodule.tensorGradedHomOfBimodule`: **`M ⊗_A s`**, as a degree-zero map
  of graded right differential graded `B`-modules.

## Main results

* `DifferentialGraded.Bimodule.tensorGradedHomOfBimodule_pure`: it carries `x ⊗ y` to `x ⊗ s y`.
* `DifferentialGraded.Bimodule.tensorGradedHomOfBimodule_toGradedHom`: tensoring a homomorphism of
  bimodules, then forgetting the differential, is tensoring the graded homomorphism underlying
  it.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product and its universal property, [Tag 09LN](https://stacks.math.columbia.edu/tag/09LN) the
  tensor–Hom identification used in degree zero, and
  [Tag 09JT](https://stacks.math.columbia.edu/tag/09JT) admissible sequences, whose splittings are
  graded homomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### Extensionality for the presented internal hom -/

/-- Two homogeneous elements of the internal hom of the same degree whose associated homogeneous
maps agree are equal. -/
theorem homModule_val_ext_of_mem (N : Bimodule A B)
    (P : DifferentialGradedModule.{u, u, u} B) (m : ℤ)
    {z w : (homPresentation N P).module.M}
    (hz : z ∈ (homPresentation N P).module.grading m)
    (hw : w ∈ (homPresentation N P).module.grading m)
    (h : ∀ y : N.rightModule.M,
      ((homPresentation N P).homogeneousEquiv m ⟨z, hz⟩).1 y =
        ((homPresentation N P).homogeneousEquiv m ⟨w, hw⟩).1 y) : z = w :=
  congrArg Subtype.val (((homPresentation N P).homogeneousEquiv m).injective
    (Subtype.ext (LinearMap.ext h)))

/-- The homogeneous map that an element of the internal hom presents does not depend on which of
two equal degrees it is read in. -/
theorem homogeneousEquiv_congr_index (N : Bimodule A B)
    (P : DifferentialGradedModule.{u, u, u} B) {i j : ℤ} (hij : i = j)
    (z : (homPresentation N P).module.M)
    (hi : z ∈ (homPresentation N P).module.grading i)
    (hj : z ∈ (homPresentation N P).module.grading j) (y : N.rightModule.M) :
    ((homPresentation N P).homogeneousEquiv i ⟨z, hi⟩).1 y =
      ((homPresentation N P).homogeneousEquiv j ⟨z, hj⟩).1 y := by
  subst hij
  rfl

/-! ### The pairing `(x, y) ↦ x ⊗ s y` -/

/-- For a graded homomorphism `s : N ⟶ N'` of bimodules and a homogeneous `x ∈ M^p` the map
`y ↦ x ⊗ s y` is a homogeneous right `B`-linear map `N ⟶ M ⊗_A N'` of degree `p + 0`. -/
def gradedPairHom (N N' : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (s : GradedHom A B N N') {p : ℤ} (x : M.grading p) :
    HomogeneousMap B N.rightModule (tensorObj N' M) (p + 0) :=
  ⟨((tensorPure N' M).toLinearMap (x : M.M)).comp s.rightHom.toFun, by
    rw [mem_homogeneousMapSubmodule]
    refine ⟨fun q y hy => ?_, fun b y => ?_⟩
    · have h := (tensorPure N' M).map_grading p q x
        (⟨s.rightHom.toFun y, s.rightHom.map_grading q y hy⟩ : N'.rightModule.grading q)
      rwa [show p + q = q + (p + 0) from by ring] at h
    · change (tensorPure N' M).toLinearMap (x : M.M)
        (s.rightHom.toFun (MulOpposite.op b • y)) = _
      rw [s.rightHom.map_smul y b]
      exact (tensorPure N' M).map_right (x : M.M) (s.rightHom.toFun y) b⟩

/-- The pairing `y ↦ x ⊗ s y`, evaluated at `y`. -/
@[simp] theorem gradedPairHom_val (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') {p : ℤ}
    (x : M.grading p) (y : N.rightModule.M) :
    (gradedPairHom N N' M s x).1 y =
      (tensorPure N' M).toLinearMap (x : M.M) (s.rightHom.toFun y) := rfl

/-- The pairing `y ↦ x ⊗ s y` is additive in `x`. -/
theorem gradedPairHom_add (N N' : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (s : GradedHom A B N N') {p : ℤ} (x x' : M.grading p) :
    gradedPairHom N N' M s (x + x') =
      gradedPairHom N N' M s x + gradedPairHom N N' M s x' :=
  Subtype.ext (LinearMap.ext fun y => by
    change (tensorPure N' M).toLinearMap ((x : M.M) + (x' : M.M)) _ = _
    rw [map_add]
    rfl)

/-- The pairing `y ↦ x ⊗ s y` is `R`-linear in `x`. -/
theorem gradedPairHom_smul (N N' : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (s : GradedHom A B N N') {p : ℤ} (r : R) (x : M.grading p) :
    gradedPairHom N N' M s (r • x) = r • gradedPairHom N N' M s x :=
  Subtype.ext (LinearMap.ext fun y => by
    change (tensorPure N' M).toLinearMap (r • (x : M.M)) _ = _
    rw [map_smul]
    rfl)

/-! ### The assembled map into the internal hom -/

/-- The degree-`p` component of `x ↦ (y ↦ x ⊗ s y)`. -/
def gradedCurryComponent (N N' : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (s : GradedHom A B N N') (p : ℤ) :
    M.grading p →ₗ[R] (homPresentation N (tensorObj N' M)).module.M where
  toFun x :=
    ((((homPresentation N (tensorObj N' M)).homogeneousEquiv (p + 0)).symm
      (gradedPairHom N N' M s x)) : (homPresentation N (tensorObj N' M)).module.M)
  map_add' x x' := by
    change ((((homPresentation N (tensorObj N' M)).homogeneousEquiv (p + 0)).symm
      (gradedPairHom N N' M s (x + x'))) :
        (homPresentation N (tensorObj N' M)).module.M) = _
    rw [gradedPairHom_add, map_add]
    rfl
  map_smul' r x := by
    change ((((homPresentation N (tensorObj N' M)).homogeneousEquiv (p + 0)).symm
      (gradedPairHom N N' M s (r • x))) :
        (homPresentation N (tensorObj N' M)).module.M) = _
    rw [gradedPairHom_smul, map_smul]
    rfl

/-- The underlying linear map of `x ↦ (y ↦ x ⊗ s y)`. -/
def gradedCurryLinear (N N' : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (s : GradedHom A B N N') :
    M.M →ₗ[R] (homPresentation N (tensorObj N' M)).module.M :=
  (DirectSum.toModule R ℤ _ (gradedCurryComponent N N' M s)).comp
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- On a homogeneous `x ∈ M^p` the map `x ↦ (y ↦ x ⊗ s y)` is its degree-`p` component. -/
theorem gradedCurryLinear_apply (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') (p : ℤ) (x : M.M)
    (hx : x ∈ M.grading p) :
    gradedCurryLinear N N' M s x =
      ((((homPresentation N (tensorObj N' M)).homogeneousEquiv (p + 0)).symm
        (gradedPairHom N N' M s ⟨x, hx⟩)) :
          (homPresentation N (tensorObj N' M)).module.M) := by
  change (DirectSum.toModule R ℤ _ (gradedCurryComponent N N' M s))
    ((DirectSum.decomposeLinearEquiv M.grading) ((⟨x, hx⟩ : M.grading p) : M.M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  rfl

/-- The map `x ↦ (y ↦ x ⊗ s y)` carries `M^p` into the degree-`p + 0` part of the internal
hom. -/
theorem gradedCurryLinear_mem (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') (p : ℤ) (x : M.M)
    (hx : x ∈ M.grading p) :
    gradedCurryLinear N N' M s x ∈
      (homPresentation N (tensorObj N' M)).module.grading (p + 0) := by
  rw [gradedCurryLinear_apply N N' M s p x hx]
  exact ((((homPresentation N (tensorObj N' M)).homogeneousEquiv (p + 0)).symm
    (gradedPairHom N N' M s ⟨x, hx⟩))).property

/-- The homogeneous map that the value at a homogeneous element presents is `y ↦ x ⊗ s y`. -/
theorem homogeneousEquiv_gradedCurryLinear (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') (p : ℤ) (x : M.M)
    (hx : x ∈ M.grading p) (y : N.rightModule.M) :
    ((homPresentation N (tensorObj N' M)).homogeneousEquiv (p + 0)
        ⟨gradedCurryLinear N N' M s x, gradedCurryLinear_mem N N' M s p x hx⟩).1 y =
      (tensorPure N' M).toLinearMap x (s.rightHom.toFun y) := by
  have h : (⟨gradedCurryLinear N N' M s x, gradedCurryLinear_mem N N' M s p x hx⟩ :
        (homPresentation N (tensorObj N' M)).module.grading (p + 0)) =
      ((homPresentation N (tensorObj N' M)).homogeneousEquiv (p + 0)).symm
        (gradedPairHom N N' M s ⟨x, hx⟩) :=
    Subtype.ext (gradedCurryLinear_apply N N' M s p x hx)
  rw [h, LinearEquiv.apply_symm_apply]
  rfl

/-- The assembled map respects the right `A`-action on homogeneous elements: the pure tensors are
balanced over `A` and `s` commutes with the left `A`-action. -/
theorem gradedCurryLinear_op_smul_homogeneous (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') (p m : ℤ) (x : M.M)
    (hx : x ∈ M.grading p) (a : A.A) (ha : a ∈ A.grading m) :
    gradedCurryLinear N N' M s (MulOpposite.op a • x) =
      MulOpposite.op a • gradedCurryLinear N N' M s x := by
  have hsm : MulOpposite.op a • x ∈ M.grading (p + m) := M.smul_mem p m x a hx ha
  have hL : gradedCurryLinear N N' M s (MulOpposite.op a • x) ∈
      (homPresentation N (tensorObj N' M)).module.grading (p + m + 0) :=
    gradedCurryLinear_mem N N' M s (p + m) _ hsm
  have hR0 : MulOpposite.op a • gradedCurryLinear N N' M s x ∈
      (homPresentation N (tensorObj N' M)).module.grading (p + 0 + m) :=
    (homPresentation N (tensorObj N' M)).module.smul_mem (p + 0) m _ a
      (gradedCurryLinear_mem N N' M s p x hx) ha
  have hR : MulOpposite.op a • gradedCurryLinear N N' M s x ∈
      (homPresentation N (tensorObj N' M)).module.grading (p + m + 0) := by
    rwa [show p + 0 + m = p + m + 0 from by ring] at hR0
  refine homModule_val_ext_of_mem N (tensorObj N' M) (p + m + 0) hL hR fun y => ?_
  induction y using DirectSum.Decomposition.inductionOn N.rightModule.grading with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | @homogeneous q y =>
    rw [homogeneousEquiv_gradedCurryLinear N N' M s (p + m) _ hsm,
      homogeneousEquiv_congr_index N (tensorObj N' M) (show p + m + 0 = p + 0 + m from by ring)
        _ hR hR0,
      (homPresentation N (tensorObj N' M)).map_smul (p + 0) m q
        ⟨gradedCurryLinear N N' M s x, gradedCurryLinear_mem N N' M s p x hx⟩ ⟨a, ha⟩ y,
      homogeneousEquiv_gradedCurryLinear N N' M s p x hx]
    rw [s.map_left m q ⟨a, ha⟩ y]
    exact (tensorPure N' M).balance p q m ⟨x, hx⟩
      ⟨s.rightHom.toFun (y : N.rightModule.M),
        s.rightHom.map_grading q (y : N.rightModule.M) y.property⟩ ⟨a, ha⟩

/-- **The map `x ↦ (y ↦ x ⊗ s y)`**, as a degree-zero homogeneous right `A`-linear map
`M ⟶ Hom^•_B(N, M ⊗_A N')`. -/
def tensorGradedCurry (N N' : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (s : GradedHom A B N N') :
    HomogeneousMap A M (homPresentation N (tensorObj N' M)).module 0 :=
  ⟨gradedCurryLinear N N' M s, by
    rw [mem_homogeneousMapSubmodule]
    refine ⟨fun i x hx => gradedCurryLinear_mem N N' M s i x hx, fun a x => ?_⟩
    induction x using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp
    | @homogeneous p x =>
      induction a using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | @homogeneous m a =>
        exact gradedCurryLinear_op_smul_homogeneous N N' M s p m (x : M.M) x.property
          (a : A.A) a.property
      | add a b hb hc =>
        simpa only [MulOpposite.op_add, add_smul, map_add] using congrArg₂ (· + ·) hb hc
    | add x y hx hy => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy⟩

/-! ### The tensored graded homomorphism -/

/-- **`M ⊗_A s`, as a degree-zero homogeneous map.** The all-degrees form of Tag 09LN in degree
zero turns `x ↦ (y ↦ x ⊗ s y)` into a degree-zero homogeneous right `B`-linear map
`M ⊗_A N ⟶ M ⊗_A N'`. -/
def tensorGradedHomogeneous (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') :
    HomogeneousMap B (tensorObj N M) (tensorObj N' M) 0 :=
  ((exists_tensorHomComplexIso N M (tensorObj N' M)).choose 0).symm
    (tensorGradedCurry N N' M s)

/-- **`M ⊗_A s` carries `x ⊗ y` to `x ⊗ s y`.** -/
theorem tensorGradedHomogeneous_pure (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') (x : M.M)
    (y : N.rightModule.M) :
    (tensorGradedHomogeneous N N' M s).1 ((tensorPure N M).toLinearMap x y) =
      (tensorPure N' M).toLinearMap x (s.rightHom.toFun y) := by
  induction x using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | @homogeneous p x =>
    obtain ⟨hpure, -⟩ := (exists_tensorHomComplexIso N M (tensorObj N' M)).choose_spec
    have hinv : (exists_tensorHomComplexIso N M (tensorObj N' M)).choose 0
        (tensorGradedHomogeneous N N' M s) = tensorGradedCurry N N' M s :=
      LinearEquiv.apply_symm_apply _ _
    have h := hpure 0 p (tensorGradedHomogeneous N N' M s) (x : M.M) x.property y
    rw [hinv] at h
    rw [← h]
    exact homogeneousEquiv_gradedCurryLinear N N' M s p (x : M.M) x.property y

/-- **`M ⊗_A s`**, as a degree-zero map of graded right differential graded `B`-modules. -/
def tensorGradedHomOfBimodule (N N' : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (s : GradedHom A B N N') :
    DifferentialGradedModule.GradedHom (tensorObj N M) (tensorObj N' M) where
  toFun := (tensorGradedHomogeneous N N' M s).1
  map_smul x b := (tensorGradedHomogeneous N N' M s).2.2 b x
  map_grading i x hx := by
    have h := (tensorGradedHomogeneous N N' M s).2.1 i x hx
    rwa [add_zero] at h

/-- The underlying map of `M ⊗_A s`. -/
@[simp] theorem tensorGradedHomOfBimodule_toFun (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') :
    (tensorGradedHomOfBimodule N N' M s).toFun = (tensorGradedHomogeneous N N' M s).1 := rfl

/-- **`M ⊗_A s` carries `x ⊗ y` to `x ⊗ s y`.** -/
theorem tensorGradedHomOfBimodule_pure (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (s : GradedHom A B N N') (x : M.M)
    (y : N.rightModule.M) :
    (tensorGradedHomOfBimodule N N' M s).toFun ((tensorPure N M).toLinearMap x y) =
      (tensorPure N' M).toLinearMap x (s.rightHom.toFun y) :=
  tensorGradedHomogeneous_pure N N' M s x y

/-- Tensoring a homomorphism of bimodules and then forgetting the differential is tensoring the
graded homomorphism underlying it: both carry `x ⊗ y` to `x ⊗ f y`. -/
theorem tensorGradedHomOfBimodule_toGradedHom (N N' : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) (f : N ⟶ N') :
    (tensorGradedHomOfBimodule N N' M (Hom.toGradedHom A B f)).toFun =
      (tensorHomOfBimoduleHom f M).toFun := by
  refine tensorObj_linearMap_ext N M _ _ fun x y => ?_
  rw [tensorGradedHomOfBimodule_pure, tensorHomOfBimoduleHom_pure]
  rfl

end DifferentialGraded.Bimodule

end
