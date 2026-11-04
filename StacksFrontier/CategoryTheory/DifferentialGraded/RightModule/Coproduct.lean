module

public import Mathlib.Algebra.DirectSum.Module
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DirectSum

/-!
# Arbitrary direct sums of right differential graded modules

Let `C` be a differential graded category over a commutative ring `R` and let `M : α → ` be a
family of right differential graded `C`-modules indexed by a type `α` of the same universe as
the modules. Their direct sum is computed degreewise: the degree-`i` part at an object `x` is
the direct sum `⨁ a, (M a).obj x i` of `R`-modules, with componentwise differential and
componentwise action. The index type sits in the universe of the modules because a degreewise
direct sum of `Type w`-valued modules indexed by a `Type w'` lands in `Type (max w w')`, and a
module in a larger universe cannot be compared with the ones it is built from: a homogeneous
morphism is only defined between two modules of one universe.

Two homogeneous morphisms out of the direct sum that agree on every summand are equal, and any
family of degree-`p` homogeneous morphisms out of the summands assembles into one out of the
direct sum. This is the universal property of the direct sum, degree by degree; it is proved
here for every degree, not only for the closed degree-zero morphisms, because the homotopy
category needs the degree `-1` case as well — that is where the homotopies live.

## Main definitions

* `DGCategory.RightModule.coprod`: the direct sum of a family of right differential graded
  modules.
* `DGCategory.RightModule.coprodι`: the inclusion of a summand, homogeneous of degree zero.
* `DGCategory.RightModule.coprodDesc`: the homogeneous morphism out of the direct sum assembled
  from a family of homogeneous morphisms out of the summands.

## Main results

* `DGCategory.RightModule.coprod_d_lof` and `DGCategory.RightModule.coprod_act_lof`: the
  differential and the action preserve each summand and are there the differential and the
  action of that summand.
* `DGCategory.RightModule.coprodι_closed`: the inclusion of a summand is a cocycle.
* `DGCategory.RightModule.coprod_hom_ext`: a homogeneous morphism out of the direct sum is
  determined by its restrictions to the summands.
* `DGCategory.RightModule.coprodDesc_coprodι`: the assembled morphism restricts to the given
  ones.
* `DGCategory.RightModule.homD_coprodDesc`: the differential of an assembled morphism is the
  assembly of the differentials, so assembling a family of cocycles gives a cocycle.

## Implementation notes

The inclusion of a summand has degree zero, so each of its components transports an element
along an equality `i + 0 = j` of degrees, exactly as the inclusions of a binary direct sum in
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DirectSum` do; the transport is
`DGCategory.RightModule.objCast`.

Every proof below is phrased with `DirectSum.lof` and never with a component index, so that no
case distinction on whether an index equals `a` is ever needed: the differential and the action
are `DirectSum.lmap` of the differentials and the actions of the summands, and `lmap` of a
`lof` is a `lof` by `DirectSum.lmap_lof`. Mathlib's `DirectSum.lof` and `DirectSum.toModule`
need a decidable equality on the index type, which is why the inclusion and the assembly carry
a `DecidableEq α` hypothesis; the direct sum itself does not.
-/

@[expose] public section

namespace DGCategory

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

namespace RightModule

open DirectSum

variable {α : Type w} (M : α → RightModule.{w} C)

/-! ### The direct sum of a family -/

/-- The direct sum of a family of right differential graded modules: the degreewise direct sum
of `R`-modules, with the componentwise differential and the componentwise action. -/
@[implicit_reducible]
def coprod : RightModule.{w} C where
  obj x i := ⨁ a, (M a).obj x i
  addCommGroup _ _ := inferInstance
  module _ _ := inferInstance
  d h z := DirectSum.lmap (fun a => (M a).dLinear h) z
  d_add h a b := by ext c; exact (M c).d_add h (a c) (b c)
  d_smul h r a := by ext c; exact (M c).d_smul h r (a c)
  d_d h₁ h₂ a := by ext c; exact (M c).d_d h₁ h₂ (a c)
  act h z f := DirectSum.lmap (fun a => (M a).actLinear h f) z
  act_add_left h a b f := by ext c; exact (M c).act_add_left h (a c) (b c) f
  act_add_right h a f g := by ext c; exact (M c).act_add_right h (a c) f g
  act_smul_left h r a f := by ext c; exact (M c).act_smul_left h r (a c) f
  act_smul_right h r a f := by ext c; exact (M c).act_smul_right h r (a c) f
  leibniz h hl a f := by ext c; exact (M c).leibniz h hl (a c) f
  assoc h₁ h₂ h₃ h₄ a g f := by ext c; exact (M c).assoc h₁ h₂ h₃ h₄ (a c) g f
  act_id a := by ext c; exact (M c).act_id (a c)

/-- The homogeneous parts of a direct sum are the direct sums of the homogeneous parts. -/
theorem coprod_obj (x : C.Obj) (i : ℤ) : (coprod M).obj x i = ⨁ a, (M a).obj x i := rfl

variable [DecidableEq α]

/-- The differential of a direct sum preserves each summand. -/
@[simp] theorem coprod_d_lof (a : α) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (y : (M a).obj x i) :
    (coprod M).d h (DirectSum.lof R α (fun c => (M c).obj x i) a y) =
      DirectSum.lof R α (fun c => (M c).obj x j) a ((M a).d h y) :=
  DirectSum.lmap_lof (fun c => (M c).dLinear h) a y

/-- The action on a direct sum preserves each summand. -/
@[simp] theorem coprod_act_lof (a : α) {x y : C.Obj} {m n k : ℤ} (h : m + n = k)
    (w : (M a).obj y m) (f : C.Hom x y n) :
    (coprod M).act h (DirectSum.lof R α (fun c => (M c).obj y m) a w) f =
      DirectSum.lof R α (fun c => (M c).obj x k) a ((M a).act h w f) :=
  DirectSum.lmap_lof (fun c => (M c).actLinear h f) a w

/-- The degree transport of a direct sum preserves each summand. -/
@[simp] theorem coprod_objCast_lof (a : α) (x : C.Obj) {i j : ℤ} (e : i = j)
    (y : (M a).obj x i) :
    (coprod M).objCast x e (DirectSum.lof R α (fun c => (M c).obj x i) a y) =
      DirectSum.lof R α (fun c => (M c).obj x j) a ((M a).objCast x e y) := by
  subst e; rfl

/-! ### The inclusion of a summand -/

/-- The underlying graded map of the inclusion of the `a`-th summand. -/
def coprodιFun (a : α) : GradedMap (M a) (coprod M) 0 := fun T =>
  (DirectSum.lof R α (fun c => (M c).obj T.x T.j) a).comp
    ((M a).objCast T.x (show T.i = T.j by have := T.hij; omega))

/-- The components of the inclusion of a summand: the transport of the degree, into that
summand. -/
theorem coprodιFun_apply (a : α) (x : C.Obj) (i j : ℤ) (e : i + 0 = j) (y : (M a).obj x i) :
    coprodιFun M a ⟨x, i, j, e⟩ y =
      DirectSum.lof R α (fun c => (M c).obj x j) a ((M a).objCast x (show i = j by omega) y) :=
  rfl

/-- The inclusion of the `a`-th summand of a direct sum, homogeneous of degree zero. Its
compatibility with the action is that the action on the direct sum is componentwise. -/
def coprodι (a : α) : HomogeneousMap (M a) (coprod M) 0 := by
  refine ⟨coprodιFun M a, ?_⟩
  intro x y i j n k l hij hik hjl hkl z f
  rw [coprodιFun_apply, coprodιFun_apply, coprod_act_lof]
  exact congrArg _ ((M a).act_objCast (show i = j by omega) (show k = l by omega)
    hik hjl z f).symm

/-- The value of the inclusion of a summand. -/
@[simp] theorem app_coprodι (a : α) {x : C.Obj} {i j : ℤ} (e : i + 0 = j)
    (y : (M a).obj x i) :
    app (coprodι M a) e y =
      DirectSum.lof R α (fun c => (M c).obj x j) a ((M a).objCast x (show i = j by omega) y) :=
  rfl

/-- The inclusion of a summand is closed, so it is a morphism of the category of complexes. -/
theorem coprodι_closed (a : α) : homD (coprodι M a) = 0 := by
  refine homD_eq_zero_of_comm_d _ fun x i j h₁ h₂ y => ?_
  rw [app_coprodι, app_coprodι, coprod_d_lof]
  refine congrArg _ ?_
  rw [(M a).d_objCast (show i = i + 0 by omega) h₁ (show i + 1 = j by omega),
    (M a).objCast_d (show i + 1 = j by omega)]

/-! ### The universal property -/

variable {M} {N : RightModule.{w} C} {p : ℤ}

/-- A homogeneous morphism out of a direct sum is determined by its values on the summands. -/
theorem coprod_hom_ext {ψ ψ' : HomogeneousMap (coprod M) N p}
    (h : ∀ (a : α) (x : C.Obj) (i j : ℤ) (e : i + p = j) (y : (M a).obj x i),
      app ψ e (DirectSum.lof R α (fun c => (M c).obj x i) a y) =
        app ψ' e (DirectSum.lof R α (fun c => (M c).obj x i) a y)) :
    ψ = ψ' := by
  refine hom_ext fun x i j e z => ?_
  have key : ψ.1 ⟨x, i, j, e⟩ = ψ'.1 ⟨x, i, j, e⟩ :=
    DirectSum.linearMap_ext (R := R) fun a => LinearMap.ext fun y => h a x i j e y
  exact LinearMap.congr_fun key z

variable (M)

/-- The underlying graded map of the morphism out of a direct sum assembled from a family of
morphisms out of the summands. -/
def coprodDescFun (φ : ∀ a, HomogeneousMap (M a) N p) : GradedMap (coprod M) N p := fun T =>
  DirectSum.toModule R α (N.obj T.x T.j) (fun a => (φ a).1 T)

/-- The components of the assembled morphism on a summand. -/
theorem coprodDescFun_apply_lof (φ : ∀ a, HomogeneousMap (M a) N p) (a : α) (x : C.Obj)
    (i j : ℤ) (e : i + p = j) (y : (M a).obj x i) :
    coprodDescFun M φ ⟨x, i, j, e⟩ (DirectSum.lof R α (fun c => (M c).obj x i) a y) =
      app (φ a) e y := by
  apply DirectSum.toModule_lof

/-- The homogeneous morphism out of a direct sum assembled from a family of homogeneous
morphisms of one degree out of the summands. Its compatibility with the action holds on each
summand, hence everywhere by the universal property of the direct sum. -/
def coprodDesc (φ : ∀ a, HomogeneousMap (M a) N p) : HomogeneousMap (coprod M) N p := by
  refine ⟨coprodDescFun M φ, ?_⟩
  intro x y i j n k l hij hik hjl hkl z f
  have key : (coprodDescFun M φ ⟨x, k, l, hkl⟩).comp
        (DirectSum.lmap fun c => (M c).actLinear hik f) =
      (N.actLinear hjl f).comp (coprodDescFun M φ ⟨y, i, j, hij⟩) := by
    refine DirectSum.linearMap_ext (R := R) fun a => LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply]
    rw [DirectSum.lmap_lof, coprodDescFun_apply_lof, coprodDescFun_apply_lof, actLinear_apply]
    exact app_act (φ a) hij hik hjl hkl w f
  exact LinearMap.congr_fun key z

/-- The value of the assembled morphism on a summand. -/
@[simp] theorem app_coprodDesc_lof (φ : ∀ a, HomogeneousMap (M a) N p) (a : α) {x : C.Obj}
    {i j : ℤ} (e : i + p = j) (y : (M a).obj x i) :
    app (coprodDesc M φ) e (DirectSum.lof R α (fun c => (M c).obj x i) a y) = app (φ a) e y :=
  coprodDescFun_apply_lof M φ a x i j e y

/-- The assembled morphism restricts on each summand to the morphism it was assembled from. -/
theorem coprodDesc_coprodι (φ : ∀ a, HomogeneousMap (M a) N p) (a : α) :
    homComp (add_zero p) (coprodDesc M φ) (coprodι M a) = φ a := by
  refine hom_ext fun x i j e y => ?_
  rw [app_homComp, app_coprodι, app_coprodDesc_lof,
    app_objCast (φ a) (show i = i + 0 by omega) (show i + 0 + p = j by omega) e]

/-- The differential of an assembled morphism is the assembly of the differentials. In
particular an assembly of cocycles is a cocycle. -/
theorem homD_coprodDesc (φ : ∀ a, HomogeneousMap (M a) N p) :
    homD (coprodDesc M φ) = coprodDesc M (fun a => homD (φ a)) := by
  refine coprod_hom_ext fun a x i j e y => ?_
  simp only [app_homD, coprod_d_lof, app_coprodDesc_lof]

end RightModule

end DGCategory

end
