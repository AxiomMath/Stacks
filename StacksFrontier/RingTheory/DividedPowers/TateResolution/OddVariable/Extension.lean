module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Combinatorics.Enumerative.Bell
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic

/-!
# Adjoining an odd variable: the extension and its grading

Let `A` be a strictly graded-commutative, nonnegatively graded algebra and let `d` be a positive
odd degree.  The odd-variable extension is `A⟨T⟩ = A ⊕ AT` with `T ^ 2 = 0`, graded so that `T`
has degree `d`; its degree-`m` piece is `A_m ⊕ A_{m-d} T`.  Strict graded commutativity forces the
adjoined variable to commute with a homogeneous coefficient only up to the Koszul sign, so the
right action on the square-zero summand is twisted: a homogeneous `a` of degree `m` satisfies
`T * a = (-1) ^ (d * m) • (a * T)`.  The twist is implemented by the grading-sign automorphism
`signRingEquiv`, which multiplies the degree-`m` piece by `(-1) ^ (d * m)`, and the extension
itself is Mathlib's trivial square-zero extension `TrivSqZeroExt A (TwistedModule Aᵢ d)` for the
resulting bimodule structure.

The construction and its grading are available for every natural degree `d`, and strict graded
commutativity is inherited whenever `A` has it.  The compatible divided powers on `A⟨T⟩`, which
need `d` odd, are in `StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable.Uniqueness`
and `StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable.Existence`.

## Main definitions

* `DividedPowers.TateResolution.signRingEquiv` — the grading-sign automorphism of `A`.
* `DividedPowers.TateResolution.TwistedModule` — the coefficient module `A` with its right action
  twisted by the grading sign.
* `DividedPowers.TateResolution.OddVariableExtension` — the algebra `A⟨T⟩`.
* `DividedPowers.TateResolution.OddVariableExtension.grade` — its degree decomposition.

## Main results

* `DividedPowers.TateResolution.OddVariableExtension.variable_sq` — the adjoined variable squares
  to zero.
* `DividedPowers.TateResolution.OddVariableExtension.generator_mul_inclusion` — the Koszul
  commutation rule.
* `DividedPowers.TateResolution.OddVariableExtension.instGradedAlgebra` and
  `DividedPowers.TateResolution.OddVariableExtension.instIsStrictlyGradedComm` — the extension is
  again a strictly graded-commutative graded algebra.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v

section Extension

open scoped RightActions DirectSum


variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- Multiplication by the grading sign on one homogeneous component. -/
public def signComponent (Aᵢ : ℕ → Submodule R A) (d m : ℕ) : Aᵢ m →+ A where
  toFun x := (-1 : R) ^ (d * m) • (x : A)
  map_zero' := by simp
  map_add' := by simp [smul_add]

/-- The grading-sign components send the unit of the graded monoid to `1`. -/
public theorem signComponent_one (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) :
    signComponent Aᵢ d 0
      (@GradedMonoid.GOne.one ℕ (fun m ↦ Aᵢ m) _ _) = 1 := by
  change (-1 : R) ^ (d * 0) • (1 : A) = 1
  simp

/-- The grading-sign components are multiplicative on homogeneous elements. -/
public theorem signComponent_mul (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) {i j : ℕ} (x : Aᵢ i) (y : Aᵢ j) :
    signComponent Aᵢ d (i + j)
        (@GradedMonoid.GMul.mul ℕ (fun m ↦ Aᵢ m) _ _ i j x y) =
      signComponent Aᵢ d i x * signComponent Aᵢ d j y := by
  change (-1 : R) ^ (d * (i + j)) • ((x : A) * (y : A)) =
    ((-1 : R) ^ (d * i) • (x : A)) * ((-1 : R) ^ (d * j) • (y : A))
  simp only [Nat.mul_add, pow_add]; rw [smul_mul_smul]

/-- The grading-sign endomorphism of a graded algebra.  On degree `m` it is multiplication by
`(-1)^(d*m)`. -/
public noncomputable def signRingHom (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) : A →+* A :=
  (DirectSum.toSemiring
    (signComponent Aᵢ d)
    (signComponent_one Aᵢ d)
    (signComponent_mul Aᵢ d)) |>.comp (DirectSum.decomposeRingEquiv Aᵢ).toRingHom

/-- On a homogeneous element of degree `m`, the grading sign is multiplication by
`(-1) ^ (d * m)`. -/
public theorem signRingHom_of_mem (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d m : ℕ)
    {a : A} (ha : a ∈ Aᵢ m) :
    signRingHom Aᵢ d a = (-1 : R) ^ (d * m) • a := by
  change (DirectSum.toSemiring (signComponent Aᵢ d) (signComponent_one Aᵢ d)
      (signComponent_mul Aᵢ d))
      ((DirectSum.decomposeRingEquiv Aᵢ) a) = _
  rw [show DirectSum.decomposeRingEquiv Aᵢ a = DirectSum.decompose Aᵢ a from rfl,
    DirectSum.decompose_of_mem Aᵢ ha, DirectSum.toSemiring_of]
  rfl

/-- Applying the grading sign twice is the identity. -/
public theorem signRingHom_involutive (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    Function.Involutive (signRingHom Aᵢ d) := by
  classical
  intro a
  rw [← DirectSum.sum_support_decompose Aᵢ a]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  let x := DirectSum.decompose Aᵢ a m
  have hx : (x : A) ∈ Aᵢ m := x.property
  rw [signRingHom_of_mem Aᵢ d m hx,
    signRingHom_of_mem Aᵢ d m ((Aᵢ m).smul_mem _ hx)]
  rw [smul_smul]
  have hs : (-1 : R) ^ (d * m) * (-1 : R) ^ (d * m) = 1 := by
    rw [← pow_two, ← pow_mul]; simp
  rw [hs, one_smul]

/-- The grading sign as an involutive ring automorphism. -/
public noncomputable def signRingEquiv (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    A ≃+* A :=
  { signRingHom Aᵢ d with
    invFun := signRingHom Aᵢ d
    left_inv := signRingHom_involutive Aᵢ d
    right_inv := signRingHom_involutive Aᵢ d }

/-- On a homogeneous element of degree `m`, the grading-sign automorphism is multiplication by
`(-1) ^ (d * m)`. -/
public theorem signRingEquiv_of_mem (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d m : ℕ) {a : A} (ha : a ∈ Aᵢ m) :
    signRingEquiv Aᵢ d a = (-1 : R) ^ (d * m) • a :=
  signRingHom_of_mem Aᵢ d m ha

/-- The grading-sign automorphism fixes the image of `R`. -/
@[simp]
public theorem signRingEquiv_algebraMap (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) (r : R) :
    signRingEquiv Aᵢ d (algebraMap R A r) = algebraMap R A r := by
  rw [signRingEquiv_of_mem Aᵢ d 0 (SetLike.algebraMap_mem_graded Aᵢ r)]; simp

/-- The second copy of `A`, with its right action twisted by the grading sign. -/
public def TwistedModule (_Aᵢ : ℕ → Submodule R A) (_d : ℕ) := A

namespace TwistedModule

/-- The additive group structure of `TwistedModule Aᵢ d` is that of `A`. -/
public instance (Aᵢ : ℕ → Submodule R A) (d : ℕ) : AddCommGroup (TwistedModule Aᵢ d) :=
  inferInstanceAs (AddCommGroup A)

/-- The `R`-module structure of `TwistedModule Aᵢ d` is that of `A`. -/
public instance (Aᵢ : ℕ → Submodule R A) (d : ℕ) : Module R (TwistedModule Aᵢ d) :=
  inferInstanceAs (Module R A)

/-- The left `A`-module structure of `TwistedModule Aᵢ d` is left multiplication in `A`. -/
public instance (Aᵢ : ℕ → Submodule R A) (d : ℕ) : Module A (TwistedModule Aᵢ d) :=
  inferInstanceAs (Module A A)

/-- The right action of `A` on `TwistedModule Aᵢ d`: `a` acts by right multiplication by
`signRingEquiv Aᵢ d a`. -/
public noncomputable instance (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    Module Aᵐᵒᵖ (TwistedModule Aᵢ d) :=
  Module.compHom A (RingEquiv.op (signRingEquiv Aᵢ d)).toRingHom

/-- The left action of `A` and the twisted right action of `A` on `TwistedModule Aᵢ d` commute. -/
public noncomputable instance (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    SMulCommClass A Aᵐᵒᵖ (TwistedModule Aᵢ d) where
  smul_comm a b x := by
    change a * ((show A from x) * signRingEquiv Aᵢ d b.unop) =
      (a * (show A from x)) * signRingEquiv Aᵢ d b.unop
    rw [mul_assoc]

/-- The twisted right action is `x <• a = x * signRingEquiv Aᵢ d a`. -/
@[simp]
public theorem op_smul (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)
    (x : TwistedModule Aᵢ d) (a : A) :
    x <• a = (show A from x) * signRingEquiv Aᵢ d a := by
  rfl

/-- The left action of `A` on `TwistedModule Aᵢ d` is multiplication in `A`. -/
@[simp]
public theorem smul_eq_mul (Aᵢ : ℕ → Submodule R A) (d : ℕ) (a : A)
    (x : TwistedModule Aᵢ d) : a • x = a * (show A from x) := by
  rfl

end TwistedModule

/-- The odd-variable extension `A⟨T⟩`.  Its elements are pairs `(a, b)`, written
mathematically as `a + bT`. -/
@[stacks 09PH "odd_variable_extension"]
public abbrev OddVariableExtension (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :=
  TrivSqZeroExt A (TwistedModule Aᵢ d)

namespace OddVariableExtension

attribute [local implicit_reducible] TwistedModule

/-- The canonical inclusion of the original algebra into its odd-variable extension. -/
public noncomputable def inclusion (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    A →+* OddVariableExtension Aᵢ d :=
  TrivSqZeroExt.inlHom A (TwistedModule Aᵢ d)

/-- The `R`-algebra structure on `OddVariableExtension Aᵢ d`, whose structure map is the composite
of `algebraMap R A` with `inclusion Aᵢ d`. -/
public noncomputable instance (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    Algebra R (OddVariableExtension Aᵢ d) where
  algebraMap := (inclusion Aᵢ d).comp (algebraMap R A)
  smul := (· • ·)
  commutes' r x := by
    apply TrivSqZeroExt.ext
    · change algebraMap R A r * x.fst = x.fst * algebraMap R A r
      exact Algebra.commutes _ _
    · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_mul]
      simp only [inclusion, RingHom.comp_apply, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero,
        add_zero, zero_add]
      change algebraMap R A r * (show A from x.snd) =
        (show A from x.snd) * signRingEquiv Aᵢ d (algebraMap R A r)
      rw [signRingEquiv_algebraMap, Algebra.commutes]
  smul_def' r x := by
    change (r • x.fst, r • x.snd) =
      ((inclusion Aᵢ d).comp (algebraMap R A)) r * x
    apply TrivSqZeroExt.ext
    · change r • x.fst = algebraMap R A r * x.fst
      exact Algebra.smul_def _ _
    · rw [TrivSqZeroExt.snd_mul]
      simp only [inclusion, RingHom.comp_apply, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero]
      change r • (show A from x.snd) = algebraMap R A r * (show A from x.snd)
      exact Algebra.smul_def _ _

/-- The adjoined variable. -/
public noncomputable def generator (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    OddVariableExtension Aᵢ d :=
  TrivSqZeroExt.inr (show TwistedModule Aᵢ d from (1 : A))

/-- The adjoined variable squares to zero. -/
@[simp]
public theorem variable_sq (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ) :
    generator Aᵢ d ^ 2 = 0 := by
  rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr A _ _

/-- The coefficient of `T` in degree `m`; it is zero below degree `d`. -/
public def shiftedGrade (Aᵢ : ℕ → Submodule R A) (d m : ℕ) :
    Submodule R (TwistedModule Aᵢ d) :=
  if d ≤ m then Aᵢ (m - d) else ⊥

/-- The degree-`m` piece `A_m ⊕ A_{m-d}T` of the odd-variable extension. -/
@[stacks 09PH "odd_variable_extension"]
public def grade (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d m : ℕ) :
    Submodule R (OddVariableExtension Aᵢ d) where
  carrier := {x | x.fst ∈ Aᵢ m ∧ x.snd ∈ shiftedGrade Aᵢ d m}
  zero_mem' := ⟨(Aᵢ m).zero_mem, (shiftedGrade Aᵢ d m).zero_mem⟩
  add_mem' := fun hx hy ↦
    ⟨(Aᵢ m).add_mem hx.1 hy.1, (shiftedGrade Aᵢ d m).add_mem hx.2 hy.2⟩
  smul_mem' := fun r _ hx ↦
    ⟨(Aᵢ m).smul_mem r hx.1, (shiftedGrade Aᵢ d m).smul_mem r hx.2⟩

/-- An element `a + bT` has degree `m` exactly when `a ∈ Aᵢ m` and `b ∈ Aᵢ (m - d)`, with `b = 0`
when `m < d`. -/
@[simp]
public theorem mem_grade_iff (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d m : ℕ) (x : OddVariableExtension Aᵢ d) :
    x ∈ grade Aᵢ d m ↔
      x.fst ∈ Aᵢ m ∧ (show A from x.snd) ∈ (if d ≤ m then Aᵢ (m - d) else ⊥) := Iff.rfl

/-- A homogeneous element of `A` remains homogeneous of the same degree in the extension. -/
public theorem inclusion_mem_grade (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d m : ℕ) {a : A} (ha : a ∈ Aᵢ m) :
    inclusion Aᵢ d a ∈ grade Aᵢ d m := by
  simp [inclusion, grade, shiftedGrade, ha]

/-- The adjoined variable is homogeneous of degree `d`. -/
public theorem generator_mem_grade (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d : ℕ) : generator Aᵢ d ∈ grade Aᵢ d d := by
  rw [mem_grade_iff]; simp only [generator, ite_eq_left le_rfl, Nat.sub_self]
  change (0 : A) ∈ Aᵢ d ∧ (1 : A) ∈ Aᵢ 0
  exact ⟨(Aᵢ d).zero_mem, SetLike.one_mem_graded Aᵢ⟩

/-- The Koszul commutation rule for the adjoined variable and a homogeneous coefficient. -/
public theorem generator_mul_inclusion (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ]
    (d m : ℕ) {a : A} (ha : a ∈ Aᵢ m) :
    generator Aᵢ d * inclusion Aᵢ d a =
      (-1 : R) ^ (d * m) • (inclusion Aᵢ d a * generator Aᵢ d) := by
  rw [show generator Aᵢ d = TrivSqZeroExt.inr
      (show TwistedModule Aᵢ d from (1 : A)) from rfl,
    show inclusion Aᵢ d a = TrivSqZeroExt.inl a from rfl,
    TrivSqZeroExt.inr_mul_inl, TrivSqZeroExt.inl_mul_inr]
  apply TrivSqZeroExt.ext
  · simp
  · rw [TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inr,
      TwistedModule.op_smul, TwistedModule.smul_eq_mul, one_mul, mul_one]
    change signRingEquiv Aᵢ d a = (-1 : R) ^ (d * m) • a
    exact signRingEquiv_of_mem Aᵢ d m ha

variable (Aᵢ : ℕ → Submodule R A) [GradedAlgebra Aᵢ] (d : ℕ)

/-- The canonical inclusion as an algebra homomorphism. -/
@[implicit_reducible]
public noncomputable def inclusionAlgHom : A →ₐ[R] OddVariableExtension Aᵢ d :=
  { inclusion Aᵢ d with commutes' := fun _ ↦ rfl }

/-- `inclusionAlgHom Aᵢ d` agrees with `inclusion Aᵢ d`. -/
@[simp]
public theorem inclusionAlgHom_apply (a : A) :
    inclusionAlgHom Aᵢ d a = inclusion Aᵢ d a := rfl

/-- Multiplication in coefficient coordinates. -/
public theorem mul_snd (x y : OddVariableExtension Aᵢ d) :
    (show A from (x * y).snd) =
      x.fst * (show A from y.snd) + (show A from x.snd) * signRingEquiv Aᵢ d y.fst := rfl

/-- Every element has its canonical expression `a + bT`. -/
public theorem inclusion_fst_add_inclusion_snd_mul_generator (x : OddVariableExtension Aᵢ d) :
    inclusion Aᵢ d x.fst + inclusion Aᵢ d x.snd * generator Aᵢ d = x := by
  apply TrivSqZeroExt.ext
  · change x.fst + (show A from x.snd) * 0 = x.fst; simp
  · change 0 + ((show A from x.snd) * 1 + 0 * signRingEquiv Aᵢ d 0) = x.snd; simp

/-- The coefficient of the variable is homogeneous in the shifted degree. -/
public theorem inr_mem_grade {m : ℕ} {a : A} (ha : a ∈ Aᵢ m) :
    TrivSqZeroExt.inr (show TwistedModule Aᵢ d from a) ∈ grade Aᵢ d (m + d) := by
  rw [mem_grade_iff]
  change (0 : A) ∈ Aᵢ (m + d) ∧ a ∈ (if d ≤ m + d then Aᵢ (m + d - d) else ⊥)
  simp [ha]

/-- The coefficient of `T` in a degree-`m` element lies in `Aᵢ (m - d)` once `d ≤ m`. -/
private theorem snd_mem_of_mem_grade {m : ℕ} {x : OddVariableExtension Aᵢ d}
    (hx : x ∈ grade Aᵢ d m) (h : d ≤ m) : (show A from x.snd) ∈ Aᵢ (m - d) := by
  simpa [h] using ((mem_grade_iff Aᵢ d m x).mp hx).2

/-- The coefficient of `T` in a degree-`m` element vanishes when `m < d`. -/
private theorem snd_eq_zero_of_mem_grade {m : ℕ} {x : OddVariableExtension Aᵢ d}
    (hx : x ∈ grade Aᵢ d m) (h : ¬ d ≤ m) : (show A from x.snd) = 0 := by
  simpa [h] using ((mem_grade_iff Aᵢ d m x).mp hx).2

/-- The inclusion on a homogeneous component. -/
public abbrev leftComponent (m : ℕ) : Aᵢ m →+ grade Aᵢ d m where
  toFun a := ⟨TrivSqZeroExt.inl a, inclusion_mem_grade Aᵢ d m a.property⟩
  map_zero' := Subtype.ext (TrivSqZeroExt.inl_zero _)
  map_add' _ _ := Subtype.ext (TrivSqZeroExt.inl_add _ _ _)

/-- Multiplication by the variable on a homogeneous component. -/
public abbrev rightComponent (m : ℕ) : Aᵢ m →+ grade Aᵢ d (m + d) where
  toFun a := ⟨TrivSqZeroExt.inr (show TwistedModule Aᵢ d from (a : A)),
    inr_mem_grade Aᵢ d a.property⟩
  map_zero' := Subtype.ext (TrivSqZeroExt.inr_zero _)
  map_add' _ _ := Subtype.ext (TrivSqZeroExt.inr_add _ _ _)

/-- Decompose the constant coefficient in the extension grading. -/
public noncomputable def decomposeLeft :
    A →+ ⨁ m, grade Aᵢ d m :=
  (DirectSum.toAddMonoid fun m ↦
    (DirectSum.of _ m).comp (leftComponent Aᵢ d m)).comp
      (DirectSum.decomposeAddEquiv Aᵢ).toAddMonoidHom

/-- Decompose the variable coefficient in the extension grading. -/
public noncomputable def decomposeRight :
    A →+ ⨁ m, grade Aᵢ d m :=
  (DirectSum.toAddMonoid fun m ↦
    (DirectSum.of _ (m + d)).comp (rightComponent Aᵢ d m)).comp
      (DirectSum.decomposeAddEquiv Aᵢ).toAddMonoidHom

/-- `decomposeLeft` sends a homogeneous element of degree `m` to its degree-`m` component. -/
public theorem decomposeLeft_of_mem {m : ℕ} {a : A} (ha : a ∈ Aᵢ m) :
    decomposeLeft Aᵢ d a = DirectSum.of _ m (leftComponent Aᵢ d m ⟨a, ha⟩) := by
  change DirectSum.toAddMonoid _ (DirectSum.decompose Aᵢ a) = _
  rw [DirectSum.decompose_of_mem Aᵢ ha, DirectSum.toAddMonoid_of]; rfl

/-- `decomposeRight` sends a homogeneous element `a` of degree `m` to the degree-`(m + d)`
component `a T`. -/
public theorem decomposeRight_of_mem {m : ℕ} {a : A} (ha : a ∈ Aᵢ m) :
    decomposeRight Aᵢ d a =
      DirectSum.of _ (m + d) (rightComponent Aᵢ d m ⟨a, ha⟩) := by
  change DirectSum.toAddMonoid _ (DirectSum.decompose Aᵢ a) = _
  rw [DirectSum.decompose_of_mem Aᵢ ha, DirectSum.toAddMonoid_of]; rfl

private theorem recompose_left (a : A) :
    DirectSum.coeAddMonoidHom (grade Aᵢ d) (decomposeLeft Aᵢ d a) =
      TrivSqZeroExt.inl a := by
  induction a using DirectSum.Decomposition.inductionOn Aᵢ with
  | zero => simp
  | homogeneous a =>
    rw [decomposeLeft_of_mem Aᵢ d a.property, DirectSum.coeAddMonoidHom_of]; rfl
  | add a b ha hb => simp [ha, hb]

private theorem recompose_right (a : A) :
    DirectSum.coeAddMonoidHom (grade Aᵢ d) (decomposeRight Aᵢ d a) =
      TrivSqZeroExt.inr (show TwistedModule Aᵢ d from a) := by
  induction a using DirectSum.Decomposition.inductionOn Aᵢ with
  | zero => rw [map_zero, map_zero]; rfl
  | homogeneous a =>
    rw [decomposeRight_of_mem Aᵢ d a.property, DirectSum.coeAddMonoidHom_of]; rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    exact (TrivSqZeroExt.inr_add A (show TwistedModule Aᵢ d from a)
      (show TwistedModule Aᵢ d from b)).symm

/-- The homogeneous decomposition, obtained by decomposing both coefficients. -/
public noncomputable def decompositionMap :
    OddVariableExtension Aᵢ d →+ ⨁ m, grade Aᵢ d m where
  toFun x := decomposeLeft Aᵢ d x.fst + decomposeRight Aᵢ d x.snd
  map_zero' := by
    change decomposeLeft Aᵢ d (0 : A) + decomposeRight Aᵢ d (0 : A) = 0; simp
  map_add' x y := by
    change decomposeLeft Aᵢ d (x.fst + y.fst) +
      decomposeRight Aᵢ d ((show A from x.snd) + (show A from y.snd)) = _
    simp [add_add_add_comm]

/-- The decomposition map sends a homogeneous element of degree `m` to its degree-`m` component. -/
@[simp]
public theorem decompositionMap_coe {m : ℕ} (x : grade Aᵢ d m) :
    decompositionMap Aᵢ d x = DirectSum.of _ m x := by
  change decomposeLeft Aᵢ d x.val.fst + decomposeRight Aᵢ d x.val.snd = _
  rw [decomposeLeft_of_mem Aᵢ d x.property.1]
  by_cases h : d ≤ m
  · have hy := snd_mem_of_mem_grade Aᵢ d x.property h
    rw [decomposeRight_of_mem Aᵢ d hy]
    generalize he : m - d = n at *
    have hm : m = n + d := by omega
    subst m
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x.val
  · have hy := snd_eq_zero_of_mem_grade Aᵢ d x.property h
    have hy' : decomposeRight Aᵢ d x.val.snd = 0 :=
      (congrArg (decomposeRight Aᵢ d) hy).trans (map_zero _)
    rw [hy', add_zero]
    congr 1
    apply Subtype.ext
    exact TrivSqZeroExt.ext rfl hy.symm

/-- The internal direct-sum decomposition of the underlying module. -/
public noncomputable instance gradeDecomposition : DirectSum.Decomposition (grade Aᵢ d) :=
  DirectSum.Decomposition.ofAddHom (grade Aᵢ d) (decompositionMap Aᵢ d)
    (by
      apply AddMonoidHom.ext
      intro x
      change DirectSum.coeAddMonoidHom (grade Aᵢ d)
        (decomposeLeft Aᵢ d x.fst + decomposeRight Aᵢ d x.snd) = x
      rw [map_add, recompose_left, recompose_right]
      exact TrivSqZeroExt.inl_fst_add_inr_snd_eq x)
    (by
      apply DirectSum.addHom_ext
      intro m x
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      exact decompositionMap_coe Aᵢ d x)

/-- Multiplication respects the degree on the extension. -/
public theorem mul_mem_grade {i j : ℕ} {x y : OddVariableExtension Aᵢ d}
    (hx : x ∈ grade Aᵢ d i) (hy : y ∈ grade Aᵢ d j) :
    x * y ∈ grade Aᵢ d (i + j) := by
  rw [mem_grade_iff]
  refine ⟨SetLike.mul_mem_graded hx.1 hy.1, ?_⟩
  change x.fst * (show A from y.snd) +
    (show A from x.snd) * signRingEquiv Aᵢ d y.fst ∈ _
  apply Submodule.add_mem
  · by_cases h : d ≤ j
    · have hy' := snd_mem_of_mem_grade Aᵢ d hy h
      have hij : d ≤ i + j := by omega
      simpa [hij, show i + j - d = i + (j - d) by omega] using
        SetLike.mul_mem_graded hx.1 hy'
    · simp [snd_eq_zero_of_mem_grade Aᵢ d hy h]
  · by_cases h : d ≤ i
    · have hx' := snd_mem_of_mem_grade Aᵢ d hx h
      have hij : d ≤ i + j := by omega
      rw [signRingEquiv_of_mem Aᵢ d j hy.1]
      simpa [hij, show i + j - d = i - d + j by omega] using
        SetLike.mul_mem_graded hx' ((Aᵢ j).smul_mem ((-1 : R) ^ (d * j)) hy.1)
    · simp [snd_eq_zero_of_mem_grade Aᵢ d hx h]

/-- The unit has degree zero and multiplication adds degrees. -/
public instance instGradedMonoid : SetLike.GradedMonoid (grade Aᵢ d) where
  one_mem := by
    change (1 : A) ∈ Aᵢ 0 ∧ (0 : TwistedModule Aᵢ d) ∈ shiftedGrade Aᵢ d 0
    exact ⟨SetLike.one_mem_graded Aᵢ, Submodule.zero_mem _⟩
  mul_mem := fun _ _ _ _ hx hy ↦ mul_mem_grade Aᵢ d hx hy

/-- The homogeneous pieces give an internal grading of the extension. -/
public noncomputable instance instGradedAlgebra : GradedAlgebra (grade Aᵢ d) :=
  { gradeDecomposition Aᵢ d, instGradedMonoid Aᵢ d with }

/-- The two coefficients identify the underlying module with `A ⊕ A`. -/
@[implicit_reducible]
public def coefficients : OddVariableExtension Aᵢ d ≃ₗ[R] A × A where
  toFun x := (x.fst, x.snd)
  invFun x := (x.1, x.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficients of `inclusion Aᵢ d a` are `(a, 0)`. -/
@[simp]
public theorem coefficients_inclusion (a : A) :
    coefficients Aᵢ d (inclusion Aᵢ d a) = (a, 0) := rfl

/-- The coefficients of the adjoined variable are `(0, 1)`. -/
@[simp]
public theorem coefficients_generator :
    coefficients Aᵢ d (generator Aᵢ d) = (0, 1) := rfl

/-- The multiplication formula in the ordinary coefficient module. -/
@[simp]
public theorem coefficients_mul (x y : OddVariableExtension Aᵢ d) :
    coefficients Aᵢ d (x * y) =
      ((coefficients Aᵢ d x).1 * (coefficients Aᵢ d y).1,
        (coefficients Aᵢ d x).1 * (coefficients Aᵢ d y).2 +
          (coefficients Aᵢ d x).2 * signRingEquiv Aᵢ d (coefficients Aᵢ d y).1) := rfl

/-- The grading can be read directly from the two coefficients. -/
public theorem mem_grade_coefficients_iff (m : ℕ) (x : OddVariableExtension Aᵢ d) :
    x ∈ grade Aᵢ d m ↔ (coefficients Aᵢ d x).1 ∈ Aᵢ m ∧
      (coefficients Aᵢ d x).2 ∈ (if d ≤ m then Aᵢ (m - d) else ⊥) :=
  mem_grade_iff Aᵢ d m x

private theorem sign_shift (i j : ℕ) (h : d ≤ j) :
    (-1 : R) ^ (i * (j - d)) = (-1 : R) ^ (i * j) * (-1 : R) ^ (d * i) := by
  rw [← pow_add]
  have he : i * j + d * i = i * (j - d) + 2 * (d * i) := by
    calc
      i * j + d * i = i * ((j - d) + d) + d * i := by rw [Nat.sub_add_cancel h]
      _ = _ := by ring
  rw [he, pow_add, pow_mul]; simp

variable [IsStrictlyGradedComm Aᵢ]

private theorem fst_mul_snd_eq {i j : ℕ} {a b : A}
    (ha : a ∈ Aᵢ i) (hb : b ∈ Aᵢ (j - d)) (h : d ≤ j) :
    a * b = (-1 : R) ^ (i * j) • (b * signRingEquiv Aᵢ d a) := by
  rw [signRingEquiv_of_mem Aᵢ d i ha, mul_smul_comm, smul_smul,
    ← sign_shift d i j h]
  exact IsStrictlyGradedComm.graded_comm ha hb

private theorem snd_mul_sign_eq {i j : ℕ} {a b : A}
    (ha : a ∈ Aᵢ (i - d)) (hb : b ∈ Aᵢ j) (h : d ≤ i) :
    a * signRingEquiv Aᵢ d b = (-1 : R) ^ (i * j) • (b * a) := by
  rw [signRingEquiv_of_mem Aᵢ d j hb, mul_smul_comm,
    IsStrictlyGradedComm.graded_comm ha hb, smul_smul, ← pow_add]
  congr 2
  calc
    d * j + (i - d) * j = ((i - d) + d) * j := by ring
    _ = i * j := by rw [Nat.sub_add_cancel h]

/-- Strict graded commutativity is preserved by the square-zero extension. -/
public instance instIsStrictlyGradedComm : IsStrictlyGradedComm (grade Aᵢ d) where
  graded_comm := by
    intro i j x y hx hy
    have hx := (mem_grade_iff Aᵢ d i x).mp hx
    have hy := (mem_grade_iff Aᵢ d j y).mp hy
    apply TrivSqZeroExt.ext
    · change x.fst * y.fst = (-1 : R) ^ (i * j) • (y.fst * x.fst)
      exact IsStrictlyGradedComm.graded_comm hx.1 hy.1
    · change x.fst * (show A from y.snd) +
        (show A from x.snd) * signRingEquiv Aᵢ d y.fst =
          (-1 : R) ^ (i * j) • (y.fst * (show A from x.snd) +
            (show A from y.snd) * signRingEquiv Aᵢ d x.fst)
      have h₁ : x.fst * (show A from y.snd) =
          (-1 : R) ^ (i * j) • ((show A from y.snd) * signRingEquiv Aᵢ d x.fst) := by
        by_cases h : d ≤ j
        · exact fst_mul_snd_eq Aᵢ d hx.1 (by simpa [h] using hy.2) h
        · have hy' : (show A from y.snd) = 0 := by simpa [h] using hy.2
          simp [hy']
      have h₂ : (show A from x.snd) * signRingEquiv Aᵢ d y.fst =
          (-1 : R) ^ (i * j) • (y.fst * (show A from x.snd)) := by
        by_cases h : d ≤ i
        · exact snd_mul_sign_eq Aᵢ d (by simpa [h] using hx.2) hy.1 h
        · have hx' : (show A from x.snd) = 0 := by simpa [h] using hx.2
          simp [hx']
      rw [h₁, h₂, smul_add, add_comm]
  odd_sq_zero := by
    intro k x hx
    have hx := (mem_grade_iff Aᵢ d (2 * k + 1) x).mp hx
    rw [pow_two]; apply TrivSqZeroExt.ext
    · change x.fst * x.fst = 0
      exact (pow_two x.fst) ▸ IsStrictlyGradedComm.odd_sq_zero hx.1
    · change x.fst * (show A from x.snd) +
        (show A from x.snd) * signRingEquiv Aᵢ d x.fst = 0
      by_cases h : d ≤ 2 * k + 1
      · have hb : (show A from x.snd) ∈ Aᵢ (2 * k + 1 - d) := by
          simpa [h] using hx.2
        rw [fst_mul_snd_eq Aᵢ d hx.1 hb h]
        have hs : (-1 : R) ^ ((2 * k + 1) * (2 * k + 1)) = -1 := by
          rw [show (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * k + 2 * k) + 1 by ring]
          simp [pow_add, pow_mul]
        rw [hs, neg_one_smul, neg_add_cancel]
      · have hx' : (show A from x.snd) = 0 := by simpa [h] using hx.2
        simp [hx']

end OddVariableExtension

end Extension

end DividedPowers.TateResolution
