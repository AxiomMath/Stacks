module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeBasis

/-!
# The integer powers of a trivializing section of an invertible module

Let `ℒ` be an invertible module on a scheme `S` and `x` a section of `ℒ` over an open `V` which
trivializes `ℒ` there. Its natural powers `x^d` (`powSecAt`) trivialize the positive tensor powers
`ℒ^{⊗ d}`. This file extends them to **all integer degrees**: `x` is invertible in the Laurent
algebra `⨁_{n ∈ ℤ} Γ(V, ℒ^{⊗ n})`, and its integer powers `x^n` multiply, `x^i x^j = x^{i + j}`,
for all `i j : ℤ`.

The device is Mathlib's `GradedMonoid`: the local sections of the integer tensor powers over `V`,
with the multiplication of the Laurent algebra, are a graded commutative monoid, so the pairs
`⟨n, s⟩` form a commutative monoid in which `⟨1, x⟩` has the inverse `⟨-1, y⟩`. The integer powers
are the components of the integer powers of that unit, and their multiplicativity is `zpow_add`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.intPow`: the `n`-th integer power of a
  trivializing section.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.lmul_intPow`: **`x^i x^j = x^{i + j}`.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.intPow_natCast`: in natural degrees the integer
  power is `powSecAt`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorGenerator

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-! ### The local sections of the Laurent algebra as a graded commutative monoid -/

section GradedMonoid

variable (V : S.Opens)

/-- The local sections over `V` of the integer tensor powers of `ℒ`. -/
abbrev LaurentSec (n : ℤ) : Type u := (tp L n).val.obj (op V)

/-- The multiplication of the local sections of the Laurent algebra, as a graded multiplication. -/
@[instance_reducible]
def laurentGMul : GradedMonoid.GMul (LaurentSec L V) where
  mul {i j} a b := (lmul L i j).app (op V) a b

/-- The unit of the local sections of the Laurent algebra. -/
@[instance_reducible]
def laurentGOne : GradedMonoid.GOne (LaurentSec L V) where
  one := (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval (op V)

attribute [local instance] laurentGMul laurentGOne

/-- The graded monoid structure of the local sections of the Laurent algebra. -/
@[instance_reducible]
def laurentGMonoid : GradedMonoid.GCommMonoid (LaurentSec L V) where
  one_mul a := Sigma.ext (zero_add _)
    (TensorPower.mulBilinear_one_mul S.sheaf.obj S.ringCatSheaf.property L a.1 (op V) a.2)
  mul_one a := Sigma.ext (add_zero _)
    (TensorPower.mulBilinear_mul_one S.sheaf.obj S.ringCatSheaf.property L a.1 (op V) a.2)
  mul_assoc a b c := Sigma.ext (add_assoc _ _ _)
    (TensorPower.mulBilinear_assoc S.sheaf.obj S.ringCatSheaf.property L a.1 b.1 c.1 (op V)
      a.2 b.2 c.2)
  mul_comm a b := Sigma.ext (add_comm _ _)
    (TensorPower.mulBilinear_comm S.sheaf.obj S.ringCatSheaf.property L a.1 b.1 (op V) a.2 b.2)

attribute [local instance] laurentGMul laurentGOne laurentGMonoid

/-- The product in the graded monoid of `⟨i, a⟩` and `⟨j, b⟩` is `⟨i + j, a b⟩`. -/
theorem mk_mul_mk' {i j : ℤ} (a : LaurentSec L V i) (b : LaurentSec L V j) :
    (GradedMonoid.mk i a * GradedMonoid.mk j b : GradedMonoid (LaurentSec L V)) =
      GradedMonoid.mk (i + j) ((lmul L i j).app (op V) a b) :=
  rfl

/-- The unit of the graded monoid is the unit section in degree `0`. -/
theorem one_eq_mk :
    (1 : GradedMonoid (LaurentSec L V)) =
      GradedMonoid.mk 0 ((TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval
        (op V)) :=
  rfl

/-- Two elements of the graded monoid in the same degree are equal exactly when their
components are. -/
theorem eq_of_mk_eq {n : ℤ} {a b : LaurentSec L V n}
    (h : (GradedMonoid.mk n a : GradedMonoid (LaurentSec L V)) = GradedMonoid.mk n b) : a = b :=
  eq_of_heq (Sigma.ext_iff.mp h).2

/-- The natural powers of a section are the powers in the graded monoid. -/
theorem mk_powSecAt (x : (tp L 1).val.obj (op V)) (d : ℕ) :
    (GradedMonoid.mk (d : ℤ) (powSecAt L (op V) x d) : GradedMonoid (LaurentSec L V)) =
      (GradedMonoid.mk 1 x) ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [pow_succ, ← ih, mk_mul_mk']
      exact Sigma.ext (succ_cast d).symm
        ((heq_of_eq (powSecAt_succ L (op V) x d)).trans (heq_reix L (succ_cast d) (op V) _))

end GradedMonoid

attribute [local instance] laurentGMul laurentGOne laurentGMonoid

/-! ### The inverse of a trivializing section -/

section Inverse

variable {V : S.Opens} {x : (tp L 1).val.obj (op V)} (hx : TrivializesPower L V x 1)

/-- The zeroth tensor power is trivial over every open. -/
def zeroTriv (V : S.Opens) :
    (tp L 0).over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V) :=
  Iso.refl _

/-- The generator of the trivialization `zeroTriv` is the unit section. -/
theorem generator_zeroTriv (V : S.Opens) :
    generator S.sheaf.obj S.ringCatSheaf.property V (tp L 0) (zeroTriv L V) =
      (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval (op V) :=
  rfl

/-- **The trivialization of `ℒ^{⊗ -1}` over an open trivializing `ℒ`**: tensoring with the
trivialized `ℒ` and multiplying into `ℒ^{⊗ 0}`. -/
def negOneTriv :
    (tp L (-1)).over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V) :=
  (tensorTrivialIso S.sheaf.obj S.ringCatSheaf.property V (tp L (-1)) (tp L ((1 : ℕ) : ℤ))
      hx.choose).symm ≪≫
    (SheafOfModules.overFunctor _ V).mapIso
      (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L (-1) 1) ≪≫
    (SheafOfModules.overFunctor _ V).mapIso (reix L (show (-1 : ℤ) + 1 = 0 by norm_num)) ≪≫
    zeroTriv L V

/-- The chosen inverse of a trivializing section: the generator of `negOneTriv`. -/
def invSec : (tp L (-1)).val.obj (op V) :=
  generator S.sheaf.obj S.ringCatSheaf.property V (tp L (-1)) (negOneTriv L hx)

/-- The multiplication of `ℒ^{⊗ a}` and `ℒ^{⊗ b}` sends `t ⊗ generator` to `t * generator`. -/
private theorem coherentMul_tensorTrivialIso_inv_app {V : S.Opens} (a b : ℤ)
    (eb : (tp L b).over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V))
    (t : (tp L a).val.obj (op V)) :
    (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L a b).hom.val.app (op V)
        (((tensorTrivialIso S.sheaf.obj S.ringCatSheaf.property V (tp L a) (tp L b) eb).inv.val.app
          (op (Over.mk (𝟙 V)))).hom t) =
      (lmul L a b).app (op V) t (generator S.sheaf.obj S.ringCatSheaf.property V (tp L b) eb) :=
  congrArg ((TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L a b).hom.val.app
    (op V)) (tensorTrivialIso_inv_app S.sheaf.obj S.ringCatSheaf.property V (tp L a) (tp L b) eb t)

/-- The product of `invSec` and `x` in the graded monoid is `1`. -/
theorem mk_invSec_mul :
    (GradedMonoid.mk (-1) (invSec L hx) * GradedMonoid.mk 1 x : GradedMonoid (LaurentSec L V)) =
      1 := by
  have hg : (negOneTriv L hx).hom.val.app (op (Over.mk (𝟙 V)))
      (invSec L hx) = (1 : (Stacks.SheafOfModules.SliceRestriction.sliceRingPresheaf
        S.sheaf.obj V).obj (op (Over.mk (𝟙 V)))) :=
    TwistRigidity.iso_hom_app_inv_app (negOneTriv L hx) (op (Over.mk (𝟙 V))) _
  have he : generator S.sheaf.obj S.ringCatSheaf.property V (tp L ((1 : ℕ) : ℤ)) hx.choose = x :=
    hx.choose_spec.trans (powSecAt_one_eq L (op V) x)
  have h1 : (negOneTriv L hx).hom.val.app (op (Over.mk (𝟙 V))) (invSec L hx) =
      (reix L (show (-1 : ℤ) + 1 = 0 by norm_num)).hom.val.app (op V)
        ((lmul L (-1) 1).app (op V) (invSec L hx) x) := by
    have h2 := coherentMul_tensorTrivialIso_inv_app L (-1) ((1 : ℕ) : ℤ) hx.choose (invSec L hx)
    rw [he] at h2
    exact congrArg ((reix L (show (-1 : ℤ) + 1 = 0 by norm_num)).hom.val.app (op V)) h2
  refine Sigma.ext (show (-1 : ℤ) + 1 = 0 by norm_num) ?_
  show HEq ((lmul L (-1) 1).app (op V) (invSec L hx) x) _
  refine (heq_reix L (show (-1 : ℤ) + 1 = 0 by norm_num) (op V) _).symm.trans ?_
  rw [← h1, hg]
  rfl

/-- The trivializing section, as a unit of the graded monoid. -/
def unitSec : (GradedMonoid (LaurentSec L V))ˣ where
  val := GradedMonoid.mk 1 x
  inv := GradedMonoid.mk (-1) (invSec L hx)
  val_inv := (mul_comm _ _).trans (mk_invSec_mul L hx)
  inv_val := mk_invSec_mul L hx

/-- The `n`-th power of `unitSec` lies in degree `n`. -/
theorem fst_zpow_unitSec (n : ℤ) : ((unitSec L hx ^ n : (GradedMonoid (LaurentSec L V))ˣ) :
    GradedMonoid (LaurentSec L V)).fst = n := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ k ih =>
      rw [zpow_add_one, Units.val_mul, GradedMonoid.fst_mul, ih]
      rfl
  | pred k ih =>
      rw [zpow_sub_one, Units.val_mul, GradedMonoid.fst_mul, ih]
      show -(k : ℤ) + -1 = -(k : ℤ) - 1
      ring

/-- **The `n`-th integer power of a trivializing section**, for `n : ℤ`. -/
def intPow (n : ℤ) : (tp L n).val.obj (op V) :=
  (fst_zpow_unitSec L hx n) ▸
    ((unitSec L hx ^ n : (GradedMonoid (LaurentSec L V))ˣ) : GradedMonoid (LaurentSec L V)).snd

/-- The integer power `x^n`, in degree `n`, is the `n`-th power of `unitSec`. -/
theorem mk_intPow (n : ℤ) :
    (GradedMonoid.mk n (intPow L hx n) : GradedMonoid (LaurentSec L V)) =
      ((unitSec L hx ^ n : (GradedMonoid (LaurentSec L V))ˣ) : GradedMonoid (LaurentSec L V)) := by
  refine Sigma.ext (fst_zpow_unitSec L hx n).symm ?_
  exact (eqRec_heq _ _)

/-- **The integer powers multiply**: `x^i x^j = x^{i + j}`. -/
theorem lmul_intPow (i j : ℤ) :
    (lmul L i j).app (op V) (intPow L hx i) (intPow L hx j) = intPow L hx (i + j) := by
  refine eq_of_mk_eq L V ?_
  rw [← mk_mul_mk', mk_intPow, mk_intPow, mk_intPow, ← Units.val_mul, ← zpow_add]

/-- In natural degrees the integer power is the natural power. -/
theorem intPow_natCast (d : ℕ) : intPow L hx (d : ℤ) = powSecAt L (op V) x d := by
  refine eq_of_mk_eq L V ?_
  rw [mk_intPow, mk_powSecAt, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl

/-- The zeroth integer power is the unit section. -/
theorem intPow_zero :
    intPow L hx 0 = (TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property L).eval (op V) :=
  intPow_natCast L hx 0

/-- The `-1`-st integer power is `invSec`. -/
theorem intPow_neg_one : intPow L hx (-1) = invSec L hx := by
  refine eq_of_mk_eq L V ?_
  rw [mk_intPow, zpow_neg_one]
  rfl

/-- The first integer power of `x` is `x`. -/
theorem intPow_one : intPow L hx 1 = x :=
  (intPow_natCast L hx 1).trans (powSecAt_one_eq L (op V) x)

/-- **`ℒ^{⊗ n}` is trivialized over `V` by `x^n`**, for an arbitrary integer `n`: an isomorphism of
its restriction to the slice over `V` with the structure sheaf there, sending `x^n` to `1`. -/
def IntTriv (n : ℤ) : Prop :=
  ∃ e : (tp L n).over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V),
    generator S.sheaf.obj S.ringCatSheaf.property V (tp L n) e = intPow L hx n

/-- If `ℒ^{⊗ a}` and `ℒ^{⊗ b}` are trivialized by `x^a` and `x^b`, then `ℒ^{⊗ (a + b)}` is
trivialized by `x^{a + b}`. -/
theorem intTriv_add {a b : ℤ} (ha : IntTriv L hx a) (hb : IntTriv L hx b) :
    IntTriv L hx (a + b) := by
  obtain ⟨ea, hea⟩ := ha
  obtain ⟨eb, heb⟩ := hb
  refine ⟨(SheafOfModules.overFunctor _ V).mapIso
      (TensorPower.coherentMulIso S.sheaf.obj S.ringCatSheaf.property L a b).symm ≪≫
    tensorTrivialIso S.sheaf.obj S.ringCatSheaf.property V (tp L a) (tp L b) eb ≪≫ ea, ?_⟩
  refine (coherentMul_tensorTrivialIso_inv_app L a b eb
    (generator S.sheaf.obj S.ringCatSheaf.property V (tp L a) ea)).trans ?_
  rw [hea, heb]
  exact lmul_intPow L hx a b

/-- `ℒ^{⊗ 0}` is trivialized by `x^0`. -/
theorem intTriv_zero : IntTriv L hx 0 :=
  ⟨zeroTriv L V, (generator_zeroTriv L V).trans (intPow_zero L hx).symm⟩

/-- `ℒ^{⊗ 1}` is trivialized by `x^1`. -/
theorem intTriv_one : IntTriv L hx 1 :=
  ⟨hx.choose, (hx.choose_spec.trans (powSecAt_one_eq L (op V) x)).trans (intPow_one L hx).symm⟩

/-- `ℒ^{⊗ -1}` is trivialized by `x^{-1}`. -/
theorem intTriv_neg_one : IntTriv L hx (-1) :=
  ⟨negOneTriv L hx, (intPow_neg_one L hx).symm⟩

/-- **Every integer tensor power of `ℒ` is trivialized over `V` by the integer power of `x`.** -/
theorem intTriv (n : ℤ) : IntTriv L hx n := by
  induction n using Int.induction_on with
  | zero => exact intTriv_zero L hx
  | succ k ih => exact intTriv_add L hx ih (intTriv_one L hx)
  | pred k ih =>
      have h := intTriv_add L hx ih (intTriv_neg_one L hx)
      rwa [← sub_eq_add_neg] at h

/-- The chosen trivialization of `ℒ^{⊗ n}` over `V` by `x^n`. -/
def intTrivIso (n : ℤ) : (tp L n).over V ≅ SheafOfModules.unit
    (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
      S.sheaf.obj S.ringCatSheaf.property V) :=
  (intTriv L hx n).choose

/-- The generator of `intTrivIso` is `x^n`. -/
theorem generator_intTrivIso (n : ℤ) :
    generator S.sheaf.obj S.ringCatSheaf.property V (tp L n) (intTrivIso L hx n) =
      intPow L hx n :=
  (intTriv L hx n).choose_spec

end Inverse

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
