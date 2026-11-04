module

public import StacksFrontier.CategoryTheory.DifferentialGraded.ExactFunctorIso
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Triangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Yoneda

/-!
# The differential graded Yoneda functor commutes with the shift up to isomorphism

Let `C` be a differential graded category over a commutative ring `R` carrying axiom (B), and
let `h_X = C(-, X)` be the representable right differential graded `C`-module of an object `X`.
The hypothesis of Tag 0FQF in its original form, `DGCategory.DGFunctor.CommShiftB`, asks for
`h_{X[n]} = (h_X)[n]`, and that is false: the degree-`i` part of the left-hand side at an object
`y` is `C.Hom y (X[n]) i`, that of the right-hand side is `C.Hom y X (i + n)`, and axiom (B)
relates the two only by the linear equivalence `DGCategory.ShiftAxiomBIso.toShift`.

What axiom (B) does give, and gives with nothing assumed beyond its own laws, is an
*isomorphism* `h_{X[n]} ≅ (h_X)[n]` of right differential graded modules, hence the hypothesis
in the form `DGCategory.DGFunctor.CommShiftBIso`. The comparison is the inverse of the
identification of axiom (B), degreewise; it is a morphism of modules because that
identification is composition on the right
(`DGCategory.ShiftAxiomBIso.toShift_comp_right`), it is closed because axiom (B) multiplies the
differential by `(-1)^n`, which is the sign the shifted module carries
(`DGCategory.ShiftAxiomBIso.toShift_d`), and the two remaining fields of the hypothesis are the
laws `DGCategory.ShiftAxiomBIso.toShift_comp_left` and
`DGCategory.ShiftAxiomBIso.toShift_comp_right` read through it.

## Main definitions

* `DGCategory.yonedaShiftHom` and `DGCategory.yonedaUnshiftHom`: the comparison
  `h_{X[n]} ⟶ (h_X)[n]` and its inverse, as homogeneous morphisms of degree zero.
* `DGCategory.yonedaShiftCocycle` and `DGCategory.yonedaUnshiftCocycle`: the same, closed.
* `DGCategory.commShiftBIso_yonedaDGFunctor`: the hypothesis of Tag 0FQF for `X ↦ h_X`, in its
  isomorphism-valued form, with no hypothesis beyond axiom (B).

## Main results

* `DGCategory.ShiftAxiomBIso.symm_toShift_comp_right`,
  `DGCategory.ShiftAxiomBIso.symm_toShift_comp_left` and
  `DGCategory.ShiftAxiomBIso.symm_toShift_d`: the three laws of axiom (B) read for the inverse of
  the identification.
* `DGCategory.isDistinguishedTriangle_mapTriangleK_yoneda`: the functor
  `K(C) ⥤ K(Mod^dg(C))` induced by `X ↦ h_X` carries distinguished triangles to distinguished
  triangles, with nothing assumed of `C` beyond axioms (A), (B) and (C).
* `DGCategory.isTriangulated_yonedaOnK_of_commShiftKIso`: that functor is exact in the sense of
  Mathlib's `CategoryTheory.Functor.IsTriangulated` as soon as the two coherences of
  `CategoryTheory.Functor.CommShift` are supplied, which axiom (B) does not supply.

## Implementation notes

No heterogeneous equality occurs anywhere in this file, and no Koszul sign has to be moved
across one. That was the difficulty of the equality-valued form: there the comparison of
`h_{X[n]}` with `(h_X)[n]` was an equality of modules, the two fields of
`DGCategory.DGFunctor.CommShiftB` were heterogeneous equalities between morphisms of different
modules, and `HEq u v` does not give `HEq (c • u) (c • v)`, the two scalar multiplications
being operations of two different modules. Here every equation lives in one Hom module of
`Mod^dg(C)` and the sign `(-1)^{nk}` of `toShift_comp_left` is moved by the involutivity of the
sign, inside that module, where linearity absorbs it.

The degree bookkeeping is the usual one: each law is stated with the target degree prescribed
and an equation naming it, which is substituted away at the start of the proof, so that a
client can use the spelling of the degree that its own indices produce.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-! ### The three laws of axiom (B), read for the inverse of its identification -/

namespace ShiftAxiomBIso

variable (S : ShiftAxiomBIso C)

/-- **The inverse identification does not change composition on the right.** This is
`DGCategory.ShiftAxiomBIso.toShift_comp_right`, which says that the identification of axiom (B)
is composition on the right in disguise. -/
theorem symm_toShift_comp_right (n : ℤ) {z w X : C.Obj} {i q p : ℤ} (hp : i + q = p)
    (a : C.Hom w ((S.shiftFunctor n).obj X) i) (f : C.Hom z w q) :
    (S.toShift n z X p).symm (C.comp hp a f) =
      C.comp (show (i + n) + q = p + n by omega) ((S.toShift n w X i).symm a) f := by
  subst hp
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  rw [S.toShift_comp_right n ((S.toShift n w X i).symm a) f, LinearEquiv.apply_symm_apply]

/-- **The inverse identification cancels the identification.** A degree-`(k + n)` morphism read
as a degree-`k` morphism into the shifted target, composed with something and then read back, is
the original composite. This is again
`DGCategory.ShiftAxiomBIso.toShift_comp_right`, used in the other direction. -/
theorem symm_toShift_comp_toShift (n : ℤ) {z X Y : C.Obj} {i k p : ℤ} (hp : k + i = p)
    (f : C.Hom X Y (k + n)) (a : C.Hom z X i) :
    (S.toShift n z Y p).symm (C.comp hp (S.toShift n X Y k f) a) =
      C.comp (show (k + n) + i = p + n by omega) f a := by
  rw [S.symm_toShift_comp_right n hp, LinearEquiv.symm_apply_apply]

/-- **The inverse identification turns the shift of a morphism into the morphism itself**, up to
the Koszul sign `(-1)^{nk}` that the shift of a degree-`k` morphism carries. This is
`DGCategory.ShiftAxiomBIso.toShift_comp_left`. -/
theorem symm_toShift_comp_left (n : ℤ) {z X Y : C.Obj} {i k p : ℤ} (hp : k + i = p)
    (g : C.Hom X Y k) (a : C.Hom z ((S.shiftFunctor n).obj X) i) :
    (S.toShift n z Y p).symm (C.comp hp ((S.shiftFunctor n).map g) a) =
      (-1 : R) ^ (n * k).natAbs •
        C.comp (show k + (i + n) = p + n by omega) g ((S.toShift n z X i).symm a) := by
  subst hp
  have hcl := S.toShift_comp_left n g ((S.toShift n z X i).symm a)
  rw [LinearEquiv.apply_symm_apply] at hcl
  have hswap : C.comp (show k + i = k + i from rfl) ((S.shiftFunctor n).map g) a =
      (-1 : R) ^ (n * k).natAbs •
        (S.toShift n z Y (k + i))
          (C.comp (show k + (i + n) = (k + i) + n by omega) g
            ((S.toShift n z X i).symm a)) := by
    rw [hcl, smul_smul, RightModule.neg_one_pow_natAbs_mul_self, one_smul]
  rw [hswap, map_smul, LinearEquiv.symm_apply_apply]

/-- **The inverse identification multiplies the differential by `(-1)^n`**, which is the sign
the differential of a shifted module carries. This is `DGCategory.ShiftAxiomBIso.toShift_d`. -/
theorem symm_toShift_d (n : ℤ) {z X : C.Obj} {i p : ℤ} (hp : i + 1 = p)
    (a : C.Hom z ((S.shiftFunctor n).obj X) i) :
    (S.toShift n z X p).symm (C.d' hp a) =
      (-1 : R) ^ n.natAbs •
        C.d' (show (i + n) + 1 = p + n by omega) ((S.toShift n z X i).symm a) := by
  subst hp
  have hd := S.toShift_d n z X i ((S.toShift n z X i).symm a)
  rw [LinearEquiv.apply_symm_apply] at hd
  have hstep : C.d' (show (i + n) + 1 = (i + 1) + n by omega) ((S.toShift n z X i).symm a) =
      (-1 : R) ^ n.natAbs • (S.toShift n z X (i + 1)).symm (C.d a) := by
    rw [← map_smul]
    exact ((S.toShift n z X (i + 1)).symm_apply_eq.mpr hd.symm).symm
  rw [hstep, smul_smul, RightModule.neg_one_pow_natAbs_mul_self, one_smul]
  rfl

end ShiftAxiomBIso


/-! ### The comparison and its inverse -/

/-- The underlying graded map of the comparison `h_{X[n]} ⟶ (h_X)[n]`: the inverse of the
identification of axiom (B), on each graded piece. -/
def yonedaShiftFun (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.GradedMap (yonedaRightModule C ((S.shiftFunctor n).obj X))
      (RightModule.shift (yonedaRightModule C X) n) 0 := fun T =>
  ((yonedaRightModule C X).objCast T.x
      (show T.i + n = T.j + n by have := T.hij; omega)).comp
    (S.toShift n T.x X T.i).symm.toLinearMap

/-- The value of `yonedaShiftFun` at a morphism `a : z ⟶ X[n]` of degree `i`: the inverse of
the identification of axiom (B) applied to `a`, transported to degree `j + n`. -/
theorem yonedaShiftFun_apply (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) (z : C.Obj) (i j : ℤ)
    (e : i + 0 = j) (a : C.Hom z ((S.shiftFunctor n).obj X) i) :
    yonedaShiftFun S n X ⟨z, i, j, e⟩ a =
      (yonedaRightModule C X).objCast z (show i + n = j + n by omega)
        ((S.toShift n z X i).symm a) :=
  rfl

/-- **The comparison `h_{X[n]} ⟶ (h_X)[n]`.** Degreewise the inverse of the identification of
axiom (B); it commutes with the right action of `C` because that identification is composition
on the right. -/
def yonedaShiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.HomogeneousMap (yonedaRightModule C ((S.shiftFunctor n).obj X))
      (RightModule.shift (yonedaRightModule C X) n) 0 := by
  refine ⟨yonedaShiftFun S n X, ?_⟩
  intro z w i j q k l hij hik hjl hkl a f
  obtain rfl : k = i + q := by omega
  obtain rfl : l = i + q := by omega
  rw [yonedaShiftFun_apply, yonedaShiftFun_apply, RightModule.objCast_rfl,
    show (yonedaRightModule C ((S.shiftFunctor n).obj X)).act hik a f = C.comp hik a f from rfl,
    S.symm_toShift_comp_right n hik a f, RightModule.shift_act]
  exact ((yonedaRightModule C X).act_objCast_left (show i + n = j + n by omega)
    (show i + n + q = i + q + n by omega) (show j + n + q = i + q + n by omega)
    ((S.toShift n w X i).symm a) f).symm

/-- The component of `yonedaShiftHom` at a morphism `a : z ⟶ X[n]` of degree `i`: the inverse of
the identification of axiom (B) applied to `a`, transported to degree `j + n`. -/
@[simp] theorem app_yonedaShiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) {z : C.Obj}
    {i j : ℤ} (e : i + 0 = j) (a : C.Hom z ((S.shiftFunctor n).obj X) i) :
    RightModule.app (yonedaShiftHom S n X) e a =
      (yonedaRightModule C X).objCast z (show i + n = j + n by omega)
        ((S.toShift n z X i).symm a) :=
  rfl

/-- The underlying graded map of the inverse comparison `(h_X)[n] ⟶ h_{X[n]}`: the
identification of axiom (B) itself. -/
def yonedaUnshiftFun (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.GradedMap (RightModule.shift (yonedaRightModule C X) n)
      (yonedaRightModule C ((S.shiftFunctor n).obj X)) 0 := fun T =>
  ((yonedaRightModule C ((S.shiftFunctor n).obj X)).objCast T.x
      (show T.i = T.j by have := T.hij; omega)).comp
    (S.toShift n T.x X T.i).toLinearMap

/-- The value of `yonedaUnshiftFun` at a morphism `a : z ⟶ X` of degree `i + n`: the
identification of axiom (B) applied to `a`, transported to degree `j`. -/
theorem yonedaUnshiftFun_apply (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) (z : C.Obj) (i j : ℤ)
    (e : i + 0 = j) (a : C.Hom z X (i + n)) :
    yonedaUnshiftFun S n X ⟨z, i, j, e⟩ a =
      (yonedaRightModule C ((S.shiftFunctor n).obj X)).objCast z (show i = j by omega)
        (S.toShift n z X i a) :=
  rfl

/-- **The inverse comparison `(h_X)[n] ⟶ h_{X[n]}`**, the identification of axiom (B) itself. -/
def yonedaUnshiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.HomogeneousMap (RightModule.shift (yonedaRightModule C X) n)
      (yonedaRightModule C ((S.shiftFunctor n).obj X)) 0 := by
  refine ⟨yonedaUnshiftFun S n X, ?_⟩
  intro z w i j q k l hij hik hjl hkl a f
  obtain rfl : k = i + q := by omega
  obtain rfl : l = i + q := by omega
  rw [yonedaUnshiftFun_apply, yonedaUnshiftFun_apply, RightModule.objCast_rfl,
    RightModule.shift_act,
    show (yonedaRightModule C X).act (show i + n + q = i + q + n by omega) a f =
      C.comp (show i + n + q = i + q + n by omega) a f from rfl,
    (yonedaRightModule C ((S.shiftFunctor n).obj X)).act_objCast_left
      (show i = j by omega) (show i + q = i + q from rfl) hjl]
  exact S.toShift_comp_right n a f

/-- The component of `yonedaUnshiftHom` at a morphism `a : z ⟶ X` of degree `i + n`: the
identification of axiom (B) applied to `a`, transported to degree `j`. -/
@[simp] theorem app_yonedaUnshiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) {z : C.Obj}
    {i j : ℤ} (e : i + 0 = j) (a : C.Hom z X (i + n)) :
    RightModule.app (yonedaUnshiftHom S n X) e a =
      (yonedaRightModule C ((S.shiftFunctor n).obj X)).objCast z (show i = j by omega)
        (S.toShift n z X i a) :=
  rfl

/-- The identification of axiom (B) absorbs a transport of the degree. -/
theorem toShift_objCast (S : ShiftAxiomBIso C) (n : ℤ) {z X : C.Obj} {i i' : ℤ} (h : i = i')
    (a : C.Hom z X (i + n)) :
    (yonedaRightModule C ((S.shiftFunctor n).obj X)).objCast z h (S.toShift n z X i a) =
      S.toShift n z X i'
        ((yonedaRightModule C X).objCast z (show i + n = i' + n by omega) a) := by
  subst h
  rfl

/-! ### The comparison is closed, and the two are mutually inverse -/

/-- The comparison is a closed degree-zero morphism: the sign `(-1)^n` that axiom (B) puts on
the differential is the sign the differential of the shifted module carries. -/
theorem homD_yonedaShiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.homD (yonedaShiftHom S n X) = 0 := by
  refine RightModule.hom_ext fun z i j e a => ?_
  obtain rfl : j = i + 1 := by omega
  rw [RightModule.app_homD, RightModule.zero_app, app_yonedaShiftHom, app_yonedaShiftHom,
    RightModule.shift_d,
    (yonedaRightModule C X).d_objCast (show i + n = i + 0 + n by omega)
      (show i + 0 + n + 1 = i + 1 + n by omega) (show i + n + 1 = i + 1 + n by omega),
    RightModule.objCast_rfl]
  simp only [yonedaRightModule_d]
  rw [S.symm_toShift_d n (rfl : i + 1 = i + 1) a]
  simp

/-- The inverse comparison is a closed degree-zero morphism. -/
theorem homD_yonedaUnshiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.homD (yonedaUnshiftHom S n X) = 0 := by
  refine RightModule.hom_ext fun z i j e a => ?_
  obtain rfl : j = i + 1 := by omega
  rw [RightModule.app_homD, RightModule.zero_app, app_yonedaUnshiftHom, app_yonedaUnshiftHom,
    (yonedaRightModule C ((S.shiftFunctor n).obj X)).d_objCast (show i = i + 0 by omega)
      (show i + 0 + 1 = i + 1 by omega) (show i + 1 = i + 1 from rfl),
    RightModule.objCast_rfl, RightModule.shift_d]
  simp only [yonedaRightModule_d]
  rw [map_smul, S.toShift_d n z X i a]
  simp only [Int.natAbs_zero, pow_zero, one_smul, smul_smul,
    RightModule.neg_one_pow_natAbs_mul_self]
  exact sub_self _

/-- **The comparison and its inverse compose to the identity of `h_{X[n]}`.** -/
theorem homComp_yonedaUnshiftHom_yonedaShiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.homComp (show (0 : ℤ) + 0 = 0 by omega) (yonedaUnshiftHom S n X)
        (yonedaShiftHom S n X) =
      RightModule.homId (yonedaRightModule C ((S.shiftFunctor n).obj X)) := by
  refine RightModule.hom_ext fun z i j e a => ?_
  rw [RightModule.app_homComp, app_yonedaShiftHom, app_yonedaUnshiftHom,
    toShift_objCast S n (show i + 0 = j by omega), RightModule.objCast_objCast,
    ← toShift_objCast S n (show i = j by omega), LinearEquiv.apply_symm_apply,
    RightModule.app_homId]

/-- **The comparison and its inverse compose to the identity of `(h_X)[n]`.** -/
theorem homComp_yonedaShiftHom_yonedaUnshiftHom (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    RightModule.homComp (show (0 : ℤ) + 0 = 0 by omega) (yonedaShiftHom S n X)
        (yonedaUnshiftHom S n X) =
      RightModule.homId (RightModule.shift (yonedaRightModule C X) n) := by
  refine RightModule.hom_ext fun z i j e a => ?_
  rw [RightModule.app_homComp, app_yonedaUnshiftHom, app_yonedaShiftHom,
    toShift_objCast S n (show i = i + 0 by omega), LinearEquiv.symm_apply_apply,
    RightModule.objCast_objCast, RightModule.app_homId, RightModule.shift_objCast]

/-- The comparison `h_{X[n]} ⟶ (h_X)[n]`, as a closed degree-zero morphism of
`Mod^dg(C)`. -/
def yonedaShiftCocycle (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    (rightModuleCategory.{v} C).Cocycle (yonedaRightModule C ((S.shiftFunctor n).obj X))
      (RightModule.shift (yonedaRightModule C X) n) :=
  ⟨yonedaShiftHom S n X, homD_yonedaShiftHom S n X⟩

/-- The underlying homogeneous morphism of `yonedaShiftCocycle S n X` is `yonedaShiftHom S n X`. -/
@[simp] theorem yonedaShiftCocycle_val (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    (yonedaShiftCocycle S n X).1 = yonedaShiftHom S n X :=
  rfl

/-- The inverse comparison, as a closed degree-zero morphism of `Mod^dg(C)`. -/
def yonedaUnshiftCocycle (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    (rightModuleCategory.{v} C).Cocycle (RightModule.shift (yonedaRightModule C X) n)
      (yonedaRightModule C ((S.shiftFunctor n).obj X)) :=
  ⟨yonedaUnshiftHom S n X, homD_yonedaUnshiftHom S n X⟩

/-- The underlying homogeneous morphism of `yonedaUnshiftCocycle S n X` is
`yonedaUnshiftHom S n X`. -/
@[simp] theorem yonedaUnshiftCocycle_val (S : ShiftAxiomBIso C) (n : ℤ) (X : C.Obj) :
    (yonedaUnshiftCocycle S n X).1 = yonedaUnshiftHom S n X :=
  rfl

/-! ### The two remaining fields, as identities of homogeneous morphisms

Both are stated at the level of `DGCategory.RightModule`, not of `Mod^dg(C)`: the composition,
the shift of a morphism and the identification of axiom (B) for `Mod^dg(C)` are the
corresponding operations on homogeneous morphisms by definition, but a goal that spells them
through `Mod^dg(C)` is not type-correct at the transparency `rw` uses, and `rw` then refuses to
fire. Stated here and transported by `exact`, which works up to definitional equality, they go
through unchanged.
-/

/-- **The comparison is natural.** Postcomposing with the shift `f[n]` of a homogeneous
morphism and then comparing is comparing and then postcomposing with `f[n]` in the shifted
module, which carries the Koszul sign `(-1)^{nk}`; the two signs cancel. This is the field
`map` of `DGCategory.DGFunctor.CommShiftBIso` for the Yoneda functor. -/
theorem homComp_yonedaShiftHom_yonedaPostcomp (S : ShiftAxiomBIso C) (n : ℤ) {X Y : C.Obj}
    {k : ℤ} (f : C.Hom X Y k) :
    RightModule.homComp (zero_add k) (yonedaShiftHom S n Y)
        (yonedaPostcomp C ((S.shiftFunctor n).map f)) =
      RightModule.homComp (add_zero k) (RightModule.shiftMap (yonedaPostcomp C f) n)
        (yonedaShiftHom S n X) := by
  refine RightModule.hom_ext fun z i j e a => ?_
  obtain rfl : j = i + k := by omega
  rw [RightModule.app_homComp, RightModule.app_homComp, app_yonedaShiftHom,
    app_yonedaPostcomp, RightModule.objCast_rfl, RightModule.app_shiftMap,
    app_yonedaShiftHom,
    RightModule.app_objCast (yonedaPostcomp C f) (show i + n = i + 0 + n by omega)
      (show i + 0 + n + k = i + k + n by omega) (show i + n + k = i + k + n by omega),
    app_yonedaPostcomp, S.symm_toShift_comp_left n (show k + i = i + k by omega) f a]

/-- **The comparison carries the identification of axiom (B) of `C` to that of
`Mod^dg(C)`.** This is the field `toShift` of `DGCategory.DGFunctor.CommShiftBIso` for the
Yoneda functor, and it is `DGCategory.ShiftAxiomBIso.toShift_comp_right` once more. -/
theorem homComp_yonedaShiftHom_yonedaPostcomp_toShift (S : ShiftAxiomBIso C) (n : ℤ)
    {X Y : C.Obj} {k : ℤ} (f : C.Hom X Y (k + n)) :
    RightModule.homComp (zero_add k) (yonedaShiftHom S n Y)
        (yonedaPostcomp C (S.toShift n X Y k f)) =
      RightModule.toShiftHom n (yonedaPostcomp C f) := by
  refine RightModule.hom_ext fun z i j e a => ?_
  obtain rfl : j = i + k := by omega
  rw [RightModule.app_homComp, app_yonedaShiftHom, app_yonedaPostcomp,
    RightModule.objCast_rfl, RightModule.app_toShiftHom, app_yonedaPostcomp,
    S.symm_toShift_comp_toShift n (show k + i = i + k by omega) f a]

/-! ### The hypothesis of Tag 0FQF for the Yoneda functor -/

/-- **The differential graded Yoneda functor commutes with the shift up to isomorphism**, in
the form `DGCategory.DGFunctor.CommShiftBIso` asks for, with nothing assumed beyond axiom (B)
for `C`.

The comparison is `DGCategory.yonedaShiftCocycle`, the inverse of the identification of axiom
(B) read degreewise; the naturality field is
`DGCategory.ShiftAxiomBIso.symm_toShift_comp_left` and the field about the identifications is
`DGCategory.ShiftAxiomBIso.symm_toShift_comp_toShift`. -/
def commShiftBIso_yonedaDGFunctor (S : ShiftAxiomBIso C) :
    (yonedaDGFunctor C).CommShiftBIso S (rightModuleShiftAxiomB.{v} C).toShiftAxiomBIso where
  hom n X := yonedaShiftCocycle S n X
  inv n X := yonedaUnshiftCocycle S n X
  hom_inv_id n X := Subtype.ext (homComp_yonedaUnshiftHom_yonedaShiftHom S n X)
  inv_hom_id n X := Subtype.ext (homComp_yonedaShiftHom_yonedaUnshiftHom S n X)
  map := by
    intro n X Y k f
    exact homComp_yonedaShiftHom_yonedaPostcomp S n f
  toShift := by
    intro n X Y k f
    exact homComp_yonedaShiftHom_yonedaPostcomp_toShift S n f

/-- **The differential graded Yoneda functor carries distinguished triangles to distinguished
triangles.** Let `C` be a differential graded category satisfying axioms (A), (B) and (C). Then
the functor `K(C) ⥤ K(Mod^dg(C))` induced by `X ↦ h_X` carries the distinguished triangles of
Tag 09QW to the distinguished triangles of Tag 09QW, the third arrow of the image triangle
being formed with the comparison `h_{X[1]} ≅ (h_X)[1]`.

Nothing is assumed beyond the cone situation. In particular no compatibility of `X ↦ h_X` with
cones is needed: a distinguished triangle is carried to a distinguished triangle by transporting
the *admissible short exact sequence* it comes from, and a functor of differential graded
categories transports one of those for free. -/
theorem isDistinguishedTriangle_mapTriangleK_yoneda (CC : ConeSituationIso C) :
    letI : HasShift C.K ℤ := CC.shift.kShift
    letI : HasShift (rightModuleCategory.{v} C).K ℤ :=
      (rightModuleConeSituation.{v} C).shift.kShift
    ∀ T : Pretriangulated.Triangle C.K, IsDistinguishedTriangleIso C CC T →
      IsDistinguishedTriangleIso (rightModuleCategory.{v} C)
        (rightModuleConeSituation.{v} C).toConeSituationIso
        ((commShiftBIso_yonedaDGFunctor CC.shift).mapTriangleK.obj T) :=
  DGFunctor.CommShiftBIso.isDistinguishedTriangle_mapTriangleK CC
    (rightModuleConeSituation.{v} C).toConeSituationIso
    (commShiftBIso_yonedaDGFunctor CC.shift)

/-- **The differential graded Yoneda functor is exact as soon as the two coherences Mathlib's
`CategoryTheory.Functor.CommShift` demands are supplied.** The hypothesis `CommShiftBIso` of Tag
0FQF is free, by `DGCategory.commShiftBIso_yonedaDGFunctor`; what a `CommShiftKIso` adds to it
is exactly the agreement of the comparison isomorphisms with `shiftFunctorZero` and
`shiftFunctorAdd` of the two translations.

Those two are not a consequence of axiom (B), and this is the precise sense in which they are
the remaining obstruction. Axiom (B) relates the identifications `toShift n` for different `n`
by no law whatever: multiplying `toShift 0` by a unit of `R` leaves every field of
`DGCategory.ShiftAxiomBIso` intact — `toShift_d`, `toShift_comp_right` and `toShift_comp_left` are
each linear in `toShift` on both sides, and `toShift 0` occurs in no cone datum — while it
multiplies the comparison in degree `0` by the inverse unit and leaves
`CategoryTheory.Functor.CommShift.isoZero` alone, that being built from `zero_obj` and
`zero_map`. The same holds for the degrees `a`, `b` and `a + b` of the additivity coherence. So
the coherences have to come from the particular differential graded category at hand. -/
theorem isTriangulated_yonedaOnK_of_commShiftKIso (CC : ConeSituationIso C)
    (hCC : CC.shift.RoundTripCoherent)
    (hK : (yonedaDGFunctor C).CommShiftKIso CC.shift
      (rightModuleShiftAxiomB.{v} C).toShiftAxiomBIso) :
    letI : Preadditive C.K := homotopyPreadditive C
    letI : Limits.HasZeroObject C.K := homotopyHasZeroObjectIso C CC
    letI : HasShift C.K ℤ := CC.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor C.K n).Additive := fun n => homotopyShiftAdditiveIso C CC n
    letI : Pretriangulated C.K := homotopyPretriangulatedIso C CC hCC
    letI : (yonedaDGFunctor C).onK.CommShift ℤ := hK.commShift
    (yonedaDGFunctor C).onK.IsTriangulated :=
  hK.isTriangulated CC (rightModuleConeSituation.{v} C).toConeSituationIso hCC
    (rightModuleConeSituation.{v} C).shift.roundTripCoherent

end DGCategory
