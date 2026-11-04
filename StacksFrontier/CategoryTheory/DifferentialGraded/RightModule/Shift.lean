module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DGCategory

/-!
# The shift of a right differential graded module

Let `C` be a differential graded category over a commutative ring `R`, let `M` be a right
differential graded `C`-module and let `n` be an integer. The *shift* `M⟦n⟧` of `M` by `n` has
`(M⟦n⟧) x i = M x (i + n)`, the differential of `M` multiplied by the Koszul sign `(-1)^n`, and
the right action of `C` unchanged. The sign on the differential is forced: the graded Leibniz
rule for an element of degree `i` in `M⟦n⟧` is the Leibniz rule for an element of degree `i + n`
in `M`, whose sign is `(-1)^(i+n) = (-1)^n (-1)^i`, so the sign on the differential is exactly
what cancels the discrepancy. The action, by contrast, admits no sign: associativity composes
two actions on one side and one on the other, so a sign there would survive unmatched.

Shifting is a functor of differential graded categories of the differential graded category
`Mod^dg(C)` of right differential graded `C`-modules. On a homogeneous morphism of degree `p`
the shift carries the Koszul sign `(-1)^(n p)`, which is again forced; see the implementation
notes.

## Main definitions

* `DGCategory.RightModule.shift`: the shift `M⟦n⟧` of a right differential graded module.
* `DGCategory.RightModule.shiftMap`: the shift of a homogeneous morphism, of the same degree.
* `DGCategory.rightModuleShiftFunctor`: the shift as a functor of differential graded categories
  from `Mod^dg(C)` to itself.

## Main results

* `DGCategory.RightModule.shift_obj`, `DGCategory.RightModule.shift_d` and
  `DGCategory.RightModule.shift_act`: the degrees, the differential and the action of the shift.
* `DGCategory.RightModule.app_shiftMap`: the value of the shift of a homogeneous morphism.
* `DGCategory.RightModule.shift_objCast`: the transport along an equality of degrees in the
  shift is the transport in the module along the shifted equality.
* `DGCategory.rightModuleShiftFunctor_obj` and `DGCategory.rightModuleShiftFunctor_map`.

## Implementation notes

The shift of a homogeneous morphism `φ` of degree `p` is `(-1)^(n p) φ`, not `φ`. The sign is
forced by the differential of `Mod^dg(C)`, which is the graded commutator
`d φ = d_N ∘ φ - (-1)^p φ ∘ d_M`: *both* of its terms acquire the factor `(-1)^n` under the
shift, so the two factors do not cancel but combine into a single factor `(-1)^n` on `d φ`. An
unsigned shift of morphisms would therefore satisfy `d (φ⟦n⟧) = (-1)^n (d φ)⟦n⟧` and fail to
commute with the differential for odd `n`. Inserting the sign `(-1)^(n p)`, which depends on the
degree `p` of `φ`, repairs exactly this: it is multiplicative in `p`, equal to `1` at `p = 0`,
and satisfies the recursion `(-1)^(n (p+1)) = (-1)^(n p) (-1)^n` matching the degree shift of the
differential. In particular the shift is unsigned on the degree-zero morphisms, so the induced
ordinary functor on `Comp(Mod^dg(C))` is the naive one.

Neither `M⟦0⟧ = M` nor `(M⟦a⟧)⟦b⟧ = M⟦a + b⟧` holds, in any form: already the underlying
families of types differ, since `M⟦0⟧` has `M.obj x (i + 0)` in degree `i` and `(M⟦a⟧)⟦b⟧` has
`M.obj x (i + b + a)`, while `i + 0 = i` and `i + b + a = i + (a + b)` are not definitional
equalities of integers. The comparisons are therefore transports, i.e. instances of
`DGCategory.RightModule.objCast`, and the statements that are true are isomorphisms in
`Mod^dg(C)` rather than equalities of modules; they are deliberately not constructed here. No
construction in this file needs them.

The only degree transport that does occur here is `DGCategory.RightModule.shift_objCast`, needed
because the identity morphism of a right module is itself a transport; every other field and
proof is discharged by the normalisation lemmas of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Hom` and
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.HomComp`
(`DGCategory.RightModule.act_d`, `DGCategory.RightModule.d_app`,
`DGCategory.RightModule.app_d` and `DGCategory.RightModule.app_app`), which move a value at a
prescribed degree back to the canonical one.
-/

@[expose] public section

namespace DGCategory

universe w v u r

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-! ### Arithmetic of the Koszul sign of a shift -/

/-- The Koszul sign is an involution: `(-1)^n (-1)^n = 1`. -/
theorem neg_one_pow_natAbs_mul_self (n : ℤ) :
    (-1 : R) ^ n.natAbs * (-1 : R) ^ n.natAbs = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- The sign `(-1)^(n p)` of the shift of a degree-`p` morphism obeys the recursion that the
differential of `Mod^dg(C)`, which raises the degree by one, requires of it. -/
theorem neg_one_pow_natAbs_mul_succ (n p : ℤ) :
    (-1 : R) ^ (n * (p + 1)).natAbs = (-1 : R) ^ (n * p).natAbs * (-1 : R) ^ n.natAbs := by
  rw [show n * (p + 1) = n * p + n by ring]
  exact neg_one_pow_natAbs_add _ _

/-- The sign `(-1)^(n p)` of the shift of a degree-`p` morphism is multiplicative in `p`, as
composition of morphisms requires of it. -/
theorem neg_one_pow_natAbs_mul_add (n p q : ℤ) :
    (-1 : R) ^ (n * (p + q)).natAbs
      = (-1 : R) ^ (n * p).natAbs * (-1 : R) ^ (n * q).natAbs := by
  rw [mul_add]
  exact neg_one_pow_natAbs_add _ _

/-! ### The shift of a right differential graded module -/

/-- The differential of the shift `M⟦n⟧`: the differential of `M`, multiplied by the Koszul sign
`(-1)^n`. -/
def shiftD (M : RightModule.{w} C) (n : ℤ) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : M.obj x (i + n)) : M.obj x (j + n) :=
  (-1 : R) ^ n.natAbs • M.d (show i + n + 1 = j + n by omega) a

/-- The right action on the shift `M⟦n⟧`: the action of `M`, with no sign and no transport. -/
def shiftAct (M : RightModule.{w} C) (n : ℤ) {x y : C.Obj} {m q k : ℤ} (h : m + q = k)
    (a : M.obj y (m + n)) (f : C.Hom x y q) : M.obj x (k + n) :=
  M.act (show m + n + q = k + n by omega) a f

/-- The shift `M⟦n⟧` of a right differential graded `C`-module `M` by an integer `n`: its
degree-`i` part at an object `x` is the degree-`(i + n)` part of `M`, its differential is that of
`M` multiplied by the Koszul sign `(-1)^n`, and its action is that of `M`. -/
@[implicit_reducible]
def shift (M : RightModule.{w} C) (n : ℤ) : RightModule.{w} C where
  obj x i := M.obj x (i + n)
  addCommGroup x i := M.addCommGroup x (i + n)
  module x i := M.module x (i + n)
  d := shiftD M n
  d_add h a b := by simp only [shiftD, M.d_add, smul_add]
  d_smul h c a := by
    simp only [shiftD, M.d_smul]
    rw [smul_comm]
  d_d h₁ h₂ a := by simp only [shiftD, M.d_smul, M.d_d, smul_zero]
  act := shiftAct M n
  act_add_left h a b f := by simp only [shiftAct, M.act_add_left]
  act_add_right h a f g := by simp only [shiftAct, M.act_add_right]
  act_smul_left h c a f := by simp only [shiftAct, M.act_smul_left]
  act_smul_right h c a f := by simp only [shiftAct, M.act_smul_right]
  leibniz := by
    intro x y m q k l h hl a f
    have hc : (-1 : R) ^ n.natAbs * ((-1 : R) ^ m.natAbs * (-1 : R) ^ n.natAbs)
        = (-1 : R) ^ m.natAbs := by
      rw [mul_comm ((-1 : R) ^ m.natAbs), ← mul_assoc, neg_one_pow_natAbs_mul_self, one_mul]
    simp only [shiftD, shiftAct]
    rw [M.leibniz (show m + n + q = k + n by omega) (show k + n + 1 = l + n by omega),
      M.act_smul_left,
      act_d M (show m + n + 1 = m + 1 + n by omega) (show m + 1 + n + q = l + n by omega)
        (show m + n + 1 + q = l + n by omega),
      neg_one_pow_natAbs_add m n, smul_add, smul_smul, hc]
  assoc h₁ h₂ h₃ h₄ a g f := M.assoc h₁ _ _ _ a g f
  act_id a := M.act_id a

/-- The degree-`i` part of `M⟦n⟧` is the degree-`(i + n)` part of `M`. -/
@[simp] theorem shift_obj (M : RightModule.{w} C) (n : ℤ) (x : C.Obj) (i : ℤ) :
    (shift M n).obj x i = M.obj x (i + n) := rfl

/-- The differential of `M⟦n⟧` is that of `M`, multiplied by the Koszul sign `(-1)^n`. -/
@[simp] theorem shift_d (M : RightModule.{w} C) (n : ℤ) {x : C.Obj} {i j : ℤ} (h : i + 1 = j)
    (a : (shift M n).obj x i) :
    (shift M n).d h a = (-1 : R) ^ n.natAbs • M.d (show i + n + 1 = j + n by omega) a :=
  rfl

/-- The action of `M⟦n⟧` is the action of `M`. -/
@[simp] theorem shift_act (M : RightModule.{w} C) (n : ℤ) {x y : C.Obj} {m q k : ℤ}
    (h : m + q = k) (a : (shift M n).obj y m) (f : C.Hom x y q) :
    (shift M n).act h a f = M.act (show m + n + q = k + n by omega) a f :=
  rfl

/-- The transport along an equality of degrees in `M⟦n⟧` is the transport in `M` along the
shifted equality. -/
theorem shift_objCast (M : RightModule.{w} C) (n : ℤ) (x : C.Obj) {i j : ℤ} (h : i = j)
    (a : (shift M n).obj x i) :
    (shift M n).objCast x h a = M.objCast x (show i + n = j + n by omega) a := by
  subst h; rfl

/-! ### The shift of a homogeneous morphism -/

variable {M N : RightModule.{w} C} {p : ℤ}

/-- The underlying graded map of the shift of a homogeneous morphism of degree `p`: the morphism
itself, multiplied by the Koszul sign `(-1)^(n p)`. -/
def shiftMapFun (φ : HomogeneousMap M N p) (n : ℤ) :
    GradedMap (shift M n) (shift N n) p := fun T =>
  (-1 : R) ^ (n * p).natAbs • φ.1 ⟨T.x, T.i + n, T.j + n, by have := T.hij; omega⟩

/-- The value of the underlying graded map of the shift of a homogeneous morphism. -/
theorem shiftMapFun_apply (φ : HomogeneousMap M N p) (n : ℤ) (x : C.Obj) (i j : ℤ)
    (h : i + p = j) (a : (shift M n).obj x i) :
    shiftMapFun φ n ⟨x, i, j, h⟩ a =
      (-1 : R) ^ (n * p).natAbs • app φ (show i + n + p = j + n by omega) a :=
  rfl

/-- The shift of a homogeneous morphism `φ : M ⟶ N` of degree `p`, as a homogeneous morphism
`M⟦n⟧ ⟶ N⟦n⟧` of degree `p`: the morphism `φ` itself, multiplied by the Koszul sign `(-1)^(n p)`
which makes the shift commute with the differential of `Mod^dg(C)`. -/
def shiftMap (φ : HomogeneousMap M N p) (n : ℤ) :
    HomogeneousMap (shift M n) (shift N n) p := by
  refine ⟨shiftMapFun φ n, ?_⟩
  intro x y i j q k l hij hik hjl hkl a f
  rw [shiftMapFun_apply, shiftMapFun_apply, shift_act, shift_act, N.act_smul_left,
    app_act φ (show i + n + p = j + n by omega) (show i + n + q = k + n by omega)
      (show j + n + q = l + n by omega) (show k + n + p = l + n by omega) a f]

/-- The value of the shift of a homogeneous morphism. -/
@[simp] theorem app_shiftMap (φ : HomogeneousMap M N p) (n : ℤ) {x : C.Obj} {i j : ℤ}
    (h : i + p = j) (a : (shift M n).obj x i) :
    app (shiftMap φ n) h a =
      (-1 : R) ^ (n * p).natAbs • app φ (show i + n + p = j + n by omega) a :=
  rfl

end RightModule

/-! ### The shift as a functor of differential graded categories -/

/-- The shift by `n` as a functor of differential graded categories from `Mod^dg(C)` to itself:
it sends a right differential graded module `M` to `M⟦n⟧` and a homogeneous morphism `φ` of
degree `p` to `(-1)^(n p) φ`. The sign is what makes the functor commute with the differential;
see the implementation notes of this file. -/
def rightModuleShiftFunctor {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)
    (n : ℤ) :
    DGFunctor (rightModuleCategory.{w} C) (rightModuleCategory.{w} C) where
  obj M := RightModule.shift M n
  map φ := RightModule.shiftMap φ n
  map_add {M N q} φ ψ := by
    refine RightModule.hom_ext fun x i j e a => ?_
    rw [RightModule.app_shiftMap, RightModule.add_app, RightModule.add_app,
      RightModule.app_shiftMap, RightModule.app_shiftMap, smul_add]
  map_smul {M N q} c φ := by
    refine RightModule.hom_ext fun x i j e a => ?_
    rw [RightModule.app_shiftMap, RightModule.smul_app, RightModule.smul_app,
      RightModule.app_shiftMap, smul_comm]
  map_d {M N q} φ := by
    refine RightModule.hom_ext fun x i j e a => ?_
    simp only [rightModuleCategory_d, RightModule.app_shiftMap, RightModule.app_homD,
      RightModule.shift_d, RightModule.app_smul, RightModule.d_smul]
    rw [RightModule.d_app φ (show i + n + q = i + q + n by omega)
        (show i + q + n + 1 = j + n by omega) (show i + n + q + 1 = j + n by omega),
      RightModule.app_d φ (show i + n + 1 = i + 1 + n by omega)
        (show i + 1 + n + q = j + n by omega) (show i + n + 1 + q = j + n by omega),
      RightModule.neg_one_pow_natAbs_mul_succ (R := R) n q]
    module
  map_comp {M N P q₁ q₂ k} h ψ φ := by
    refine RightModule.hom_ext fun x i j e a => ?_
    have hk : (-1 : R) ^ (n * k).natAbs
        = (-1 : R) ^ (n * q₁).natAbs * (-1 : R) ^ (n * q₂).natAbs := by
      rw [← h]; exact RightModule.neg_one_pow_natAbs_mul_add n q₁ q₂
    simp only [rightModuleCategory_comp, RightModule.app_shiftMap, RightModule.app_homComp,
      RightModule.app_smul]
    rw [RightModule.app_app ψ φ (show i + n + q₂ = i + q₂ + n by omega)
        (show i + q₂ + n + q₁ = j + n by omega) (show i + n + q₂ + q₁ = j + n by omega), hk]
    module
  map_id M := by
    refine RightModule.hom_ext fun x i j e a => ?_
    simp only [rightModuleCategory_id, RightModule.app_shiftMap, RightModule.app_homId,
      RightModule.shift_objCast, mul_zero, Int.natAbs_zero, pow_zero, one_smul]

/-- The shift functor sends a right differential graded module to its shift. -/
@[simp] theorem rightModuleShiftFunctor_obj {R : Type r} [CommRing R]
    (C : DGCategory.{v, u} R) (n : ℤ) (M : RightModule.{w} C) :
    (rightModuleShiftFunctor C n).obj M = RightModule.shift M n := rfl

/-- The shift functor sends a homogeneous morphism to its shift. -/
@[simp] theorem rightModuleShiftFunctor_map {R : Type r} [CommRing R]
    (C : DGCategory.{v, u} R) (n : ℤ) {M N : RightModule.{w} C} {p : ℤ}
    (φ : (rightModuleCategory.{w} C).Hom M N p) :
    (rightModuleShiftFunctor C n).map φ = RightModule.shiftMap φ n := rfl

end DGCategory
