module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Yoneda

/-!
# The Yoneda lemma for right differential graded modules

Let `C` be a differential graded category over a commutative ring `R`, let `X` be an object of
`C` and let `M` be a right differential graded `C`-module. Evaluation at the identity of `X` is
an isomorphism from the Hom complex of the representable module `h_X = C(-, X)` into `M` onto
the complex `M X`: in each degree it is an `R`-linear equivalence, and it commutes with the
differentials. Its inverse sends an element `a` of `M X` of degree `p` to the right action
`b ↦ a · b`, which is a homogeneous morphism precisely by associativity of the action.

Taking `M = h_Y` gives that the differential graded Yoneda functor
`DGCategory.yonedaDGFunctor` is fully faithful: postcomposition is an `R`-linear equivalence
from the degree-`m` morphisms `X ⟶ Y` onto the degree-`m` homogeneous morphisms
`h_X ⟶ h_Y`.

## Main definitions

* `DGCategory.yonedaEval`: evaluation at the identity, as an `R`-linear equivalence
  `Hom^p(h_X, M) ≃ₗ[R] M X p`.
* `DGCategory.yonedaPostcompEquiv`: the inverse equivalence at `M = h_Y`, exhibiting
  postcomposition as an isomorphism onto the homogeneous morphisms of representables.

## Main results

* `DGCategory.yonedaEval_homD`: evaluation at the identity commutes with the differentials, so
  it is an isomorphism of complexes.
* `DGCategory.yonedaEval_yonedaPostcomp` and `DGCategory.yonedaPostcompEquiv_apply`: the
  equivalence is postcomposition, so `DGCategory.yonedaDGFunctor` is fully faithful in every
  degree.

## Implementation notes

The two halves of the bijection are the two unit axioms of a right module read in opposite
directions: that the reconstructed morphism agrees with the original is
`DGCategory.RightModule.app_act` applied to `C.id_comp`, and that evaluation undoes the
reconstruction is `DGCategory.RightModule.act_id`. The compatibility with the differential uses
only that the identity of `X` is closed, `DGCategory.d_id`.

The module `M` is taken in the universe of the homogeneous morphisms of `C`, because that is
where the representable module `h_X` lives and a homogeneous morphism is only defined between
two modules in the same universe. A module in a larger universe would first have to be compared
with a universe lift of `C`; nothing here depends on that comparison.
-/

@[expose] public section

namespace DGCategory

universe v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-! ### Evaluation at the identity -/

/-- The underlying graded map of the homogeneous morphism `h_X ⟶ M` attached to an element of
`M X`: it is the right action of that element. -/
def yonedaOfElemFun {M : RightModule.{v} C} {X : C.Obj} {p : ℤ} (a : M.obj X p) :
    RightModule.GradedMap (yonedaRightModule C X) M p := fun T =>
  { toFun := fun b => M.act (show p + T.i = T.j by have := T.hij; omega) a b
    map_add' := fun b c => M.act_add_right _ a b c
    map_smul' := fun c b => M.act_smul_right _ c a b }

/-- The homogeneous morphism `h_X ⟶ M` of degree `p` attached to an element of `M X` of degree
`p`: the right action of that element. Its compatibility with the action of `C` is
associativity, `DGCategory.RightModule.assoc`. -/
def yonedaOfElem {M : RightModule.{v} C} {X : C.Obj} {p : ℤ} (a : M.obj X p) :
    RightModule.HomogeneousMap (yonedaRightModule C X) M p := by
  refine ⟨yonedaOfElemFun a, ?_⟩
  intro z w i j n k l hij hik hjl hkl b g
  exact M.assoc hik (show p + k = l by omega) (show p + i = j by omega) hjl a b g

/-- The component of `DGCategory.yonedaOfElem a` at `b` is the right action of `a` on `b`. -/
@[simp] theorem app_yonedaOfElem {M : RightModule.{v} C} {X : C.Obj} {p : ℤ} (a : M.obj X p)
    {z : C.Obj} {i j : ℤ} (h : i + p = j) (b : (yonedaRightModule C X).obj z i) :
    RightModule.app (yonedaOfElem a) h b = M.act (show p + i = j by omega) a b :=
  rfl

/-- **The Yoneda lemma for right differential graded modules.** Evaluation at the identity of
`X` is an `R`-linear equivalence from the degree-`p` homogeneous morphisms `h_X ⟶ M` onto the
degree-`p` part of `M X`; its inverse is the right action. -/
def yonedaEval (M : RightModule.{v} C) (X : C.Obj) (p : ℤ) :
    RightModule.HomogeneousMap (yonedaRightModule C X) M p ≃ₗ[R] M.obj X p where
  toFun φ := RightModule.app φ (zero_add p) (C.id X)
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun a := yonedaOfElem a
  left_inv φ := by
    refine RightModule.hom_ext fun z i j e b => ?_
    rw [app_yonedaOfElem]
    have hact := RightModule.app_act φ (zero_add p) (show (0 : ℤ) + i = i by omega)
      (show p + i = j by omega) e (C.id X) b
    rw [show (yonedaRightModule C X).act (show (0 : ℤ) + i = i by omega) (C.id X) b = b from
      C.id_comp b] at hact
    exact hact.symm
  right_inv a := by
    change M.act (show p + 0 = p by omega) a (C.id X) = a
    exact M.act_id a

/-- `DGCategory.yonedaEval` sends a homogeneous morphism `h_X ⟶ M` to its value at the identity
of `X`. -/
@[simp] theorem yonedaEval_apply (M : RightModule.{v} C) (X : C.Obj) (p : ℤ)
    (φ : RightModule.HomogeneousMap (yonedaRightModule C X) M p) :
    yonedaEval M X p φ = RightModule.app φ (zero_add p) (C.id X) := rfl

/-- The inverse of `DGCategory.yonedaEval` sends an element of `M X` to `DGCategory.yonedaOfElem`
of it, the right action of that element. -/
@[simp] theorem yonedaEval_symm_apply (M : RightModule.{v} C) (X : C.Obj) (p : ℤ)
    (a : M.obj X p) : (yonedaEval M X p).symm a = yonedaOfElem a := rfl

/-- Evaluation at the identity commutes with the differentials: the equivalences of
`DGCategory.yonedaEval` are an isomorphism of complexes `Hom^•(h_X, M) ≅ M X`. -/
theorem yonedaEval_homD (M : RightModule.{v} C) (X : C.Obj) (p : ℤ)
    (φ : RightModule.HomogeneousMap (yonedaRightModule C X) M p) :
    yonedaEval M X (p + 1) (RightModule.homD φ) = M.d rfl (yonedaEval M X p φ) := by
  rw [yonedaEval_apply, yonedaEval_apply, RightModule.app_homD,
    show (yonedaRightModule C X).d (rfl : (0 : ℤ) + 1 = 0 + 1) (C.id X) = C.d (C.id X) from rfl,
    C.d_id X, RightModule.app_zero, smul_zero, sub_zero,
    RightModule.d_app φ (zero_add p) (rfl : p + 1 = p + 1)
      (show (0 : ℤ) + p + 1 = p + 1 by omega)]

/-! ### Full faithfulness of the differential graded Yoneda functor -/

/-- Evaluating postcomposition with `f : X ⟶ Y` at the identity of `X` recovers `f`. -/
theorem yonedaEval_yonedaPostcomp {X Y : C.Obj} {m : ℤ} (f : C.Hom X Y m) :
    yonedaEval (yonedaRightModule C Y) X m (yonedaPostcomp C f) = f := by
  rw [yonedaEval_apply, app_yonedaPostcomp]
  exact C.comp_id f

/-- **The differential graded Yoneda functor is fully faithful.** Postcomposition is an
`R`-linear equivalence from the degree-`m` morphisms `X ⟶ Y` of `C` onto the degree-`m`
homogeneous morphisms `h_X ⟶ h_Y` of right differential graded `C`-modules. -/
def yonedaPostcompEquiv (C : DGCategory.{v, u} R) (X Y : C.Obj) (m : ℤ) :
    C.Hom X Y m ≃ₗ[R]
      RightModule.HomogeneousMap (yonedaRightModule C X) (yonedaRightModule C Y) m :=
  (yonedaEval (yonedaRightModule C Y) X m).symm

/-- `DGCategory.yonedaPostcompEquiv` is postcomposition, `DGCategory.yonedaPostcomp`. -/
@[simp] theorem yonedaPostcompEquiv_apply (C : DGCategory.{v, u} R) {X Y : C.Obj} {m : ℤ}
    (f : C.Hom X Y m) : yonedaPostcompEquiv C X Y m f = yonedaPostcomp C f :=
  (yonedaEval (yonedaRightModule C Y) X m).symm_apply_eq.2
    (yonedaEval_yonedaPostcomp f).symm

/-- The inverse of `DGCategory.yonedaPostcompEquiv` sends a homogeneous morphism `h_X ⟶ h_Y` to
its value at the identity of `X`. -/
@[simp] theorem yonedaPostcompEquiv_symm_apply (C : DGCategory.{v, u} R) {X Y : C.Obj} {m : ℤ}
    (φ : RightModule.HomogeneousMap (yonedaRightModule C X) (yonedaRightModule C Y) m) :
    (yonedaPostcompEquiv C X Y m).symm φ = RightModule.app φ (zero_add m) (C.id X) := rfl

end DGCategory
